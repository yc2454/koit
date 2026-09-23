import Koit.BPF.State

/-!
The step function of the target machine: eBPF with the verifier's
safety conditions as refusals. `step` is a total function of the
state for each kernel `K`, so the machine is deterministic per
kernel; it answers with the next state or the cause it refuses for,
one constructor of `Cause` per item of `bir.md` 5.3. A state is
halted when its instruction is `exit`, the result register holds a
scalar, and nothing is held; a state that is neither halted nor
steppable is stuck, and the correctness theorem of the lowering says
the code it emits never reaches one.

One function serves BIR and bytecode: the register type and the
jump-target type are parameters, and the convention of `State.lean`
says how a call takes its operands and whether `lea` is admitted.
The shared state is reached through the operations of
`Koit.Machine.Ops`, the same ones Core's and LIR's semantics call, so
a map lookup or a kernel call is one definition at every level.
-/

namespace Koit.BPF

open Koit.Machine (toNatMod wrap leBytes ofLe bswap Kernel HeldObj)
open Koit.Interface (CallDecl ResourceDecl KindDecl)

variable {ρ τ : Type} [DecidableEq ρ]

/-- What a step computes: a value, or the cause of a refusal. -/
abbrev StepM := Except Cause

/-! ### Registers -/

/-- A register's value, which must be initialized. -/
def reg (X : Env ρ τ) (m : State ρ) (r : ρ) : StepM Val :=
  match m.regs r with
  | some v => pure v
  | none => throw (.uninitRegister (X.conv.name r))

/-- A source operand: a register's value or an immediate as a 64-bit
pattern. -/
def src (X : Env ρ τ) (m : State ρ) : Src ρ → StepM Val
  | .reg r => reg X m r
  | .imm k => pure (.scalar (toNatMod k 64))

/-! ### The ALU -/

/-- The operation on two patterns at `cls` bits, the result at `cls`
bits and, for 32, zero-extended into the register: the kernel's
total arithmetic, division and modulo by zero yielding zero and the
dividend, shifts masked to the class. -/
def aluScalar (op : AluOp) (cls : Cls) (a b : Nat) : Nat :=
  let w := cls.bits
  let a := toNatMod a w
  let b := toNatMod b w
  let sa : Int := wrap true w a
  let sb : Int := wrap true w b
  let r : Int := match op with
    | .add => Machine.arith .add false w a b
    | .sub => Machine.arith .sub false w a b
    | .mul => Machine.arith .mul false w a b
    | .div => Machine.arith .div false w a b
    | .mod => Machine.arith .mod false w a b
    | .and => Machine.arith .band false w a b
    | .or => Machine.arith .bor false w a b
    | .xor => Machine.arith .bxor false w a b
    | .lsh => Machine.arith .shl false w a b
    | .rsh => Machine.arith .shr false w a b
    | .sdiv => Machine.arith .div true w sa sb
    | .smod => Machine.arith .mod true w sa sb
    | .arsh => Machine.arith .shr true w sa b
  toNatMod r w

/-- `alu(op, cls) d s`: on two scalars the operation; on a location,
`add` and `sub` of a scalar at 64 bits move its offset, and `sub` of
two locations of one region is their offset difference; anything
else is refused. -/
def alu (X : Env ρ τ) (m : State ρ) (op : AluOp) (cls : Cls) (d : ρ) (s : Src ρ) :
    StepM (State ρ) := do
  let a ← reg X m d
  let b ← src X m s
  match a, b with
  | .scalar x, .scalar y => return m.set d (.scalar (aluScalar op cls x y))
  | .loc r o t, .scalar y =>
    match op, cls with
    | .add, .w64 => return m.set d (.loc r (o + wrap true 64 y) t)
    | .sub, .w64 => return m.set d (.loc r (o - wrap true 64 y) t)
    | _, _ => throw (.aluOnLocation s!"`{op.print}({cls.print})` on {r.print} + {o}")
  | .loc r o _, .loc r' o' _ =>
    match op, cls with
    | .sub, .w64 =>
      unless r == r' do
        throw (.aluOnLocation s!"the difference of {r.print} + {o} and {r'.print} + {o'}")
      return m.set d (.scalar (toNatMod (o - o') 64))
    | _, _ => throw (.aluOnLocation s!"`{op.print}({cls.print})` on two locations")
  | a, b => throw (.aluOnLocation s!"`{op.print}({cls.print})` on {a.print} and {b.print}")

/-- `mov(cls) d s`: a copy at 64 bits; at 32 bits the low pattern of
a scalar, and a location is refused. -/
def mov (X : Env ρ τ) (m : State ρ) (cls : Cls) (d : ρ) (s : Src ρ) : StepM (State ρ) := do
  let b ← src X m s
  match cls, b with
  | .w64, v => return m.set d v
  | .w32, .scalar y => return m.set d (.scalar (toNatMod y 32))
  | .w32, v => throw (.aluOnLocation s!"a 32-bit move of {v.print}")

/-- `movsx(cls, w) d s`: the low `w` bits of a scalar sign-extended
to the class. -/
def movsx (X : Env ρ τ) (m : State ρ) (cls : Cls) (w : Nat) (d s : ρ) : StepM (State ρ) := do
  match ← reg X m s with
  | .scalar y => return m.set d (.scalar (toNatMod (wrap true w (toNatMod y w)) cls.bits))
  | v => throw (.aluOnLocation s!"a sign extension of {v.print}")

/-- `end(to, w) d`: to big-endian is the swap of the low `w` bits on
this little-endian machine, to little-endian their truncation; both
zero-extend. -/
def endian (X : Env ρ τ) (m : State ρ) (to : Endian) (w : Nat) (d : ρ) : StepM (State ρ) := do
  match ← reg X m d with
  | .scalar y =>
    let low := toNatMod y w
    return m.set d (.scalar (match to with
      | .be => bswap w low
      | .le => low))
  | v => throw (.aluOnLocation s!"a byte swap of {v.print}")

/-! ### Memory -/

/-- The width of a context field's type. -/
def ctxWidth : Core.Ty → Nat
  | .int _ _ w => w
  | _ => 0

/-- A load of `w` bits from the context at `eff`: a field's declaration
yields its value, a packet-bound declaration yields the packet's location
with the current token; anything else is refused. -/
def ctxLoad (X : Env ρ τ) (m : State ρ) (eff : Int) (w : Nat) : StepM Val := do
  if eff < 0 then throw (.ctxAccess eff (w / 8) false)
  let o := eff.toNat
  if let some f := X.kind.ctx.find? (fun f => f.offset == o && ctxWidth f.ty == w) then
    return .scalar (toNatMod ((m.ctx.lookup f.name).getD 0) w)
  if let some b := X.kind.ctxBounds.find? (fun b => b.offset == o && w == 32) then
    return .loc .pkt (if b.isEnd then m.machine.packet.size else 0) m.machine.layout
  throw (.ctxAccess eff (w / 8) false)

/-- A load of `w` bits through `base + off`, by the region's rules. -/
def loadAt (X : Env ρ τ) (m : State ρ) (base : Val) (off : Int) (w : Nat) : StepM Val := do
  let n := w / 8
  match base with
  | .loc r o t =>
    let eff := o + off
    match r with
    | .shared sr =>
      if eff < 0 then throw (.outOfRegion r eff n)
      if sr == .pkt && t != m.machine.layout then throw (.staleToken eff)
      unless m.machine.admits sr eff.toNat n t do throw (.outOfRegion r eff n)
      return .scalar (ofLe (m.machine.bytesAt sr eff.toNat n))
    | .frame => m.frame.load eff n
    | .ctx => ctxLoad X m eff w
  | v => throw (.noRegion v)

/-- A store of `v` as `w` bits through `base + off`: a location or a
handle only into an aligned frame slot, a scalar into any writable
declaration or region. -/
def storeAt (X : Env ρ τ) (m : State ρ) (base : Val) (off : Int) (w : Nat) (v : Val) :
    StepM (State ρ) := do
  let n := w / 8
  match base with
  | .loc r o t =>
    let eff := o + off
    match r with
    | .frame => return { m with frame := ← m.frame.store eff n v }
    | .shared sr =>
      let .scalar x := v | throw (.pointerLeak r eff)
      if eff < 0 then throw (.outOfRegion r eff n)
      if sr == .pkt && t != m.machine.layout then throw (.staleToken eff)
      unless m.machine.admits sr eff.toNat n t do throw (.outOfRegion r eff n)
      return { m with machine := m.machine.writeAt sr eff.toNat (leBytes (toNatMod x w) n) }
    | .ctx =>
      let .scalar x := v | throw (.pointerLeak r eff)
      if eff < 0 then throw (.ctxAccess eff n true)
      match X.kind.ctx.find? (fun f => f.offset == eff.toNat && ctxWidth f.ty == w) with
      | some f =>
        unless f.writable do throw (.ctxAccess eff n true)
        return { m with ctx := m.ctx.map fun (g, y) =>
          if g == f.name then (g, toNatMod x w) else (g, y) }
      | none => throw (.ctxAccess eff n true)
  | v => throw (.noRegion v)

/-- The initialized bytes a location points at, for a key or a memory
argument: a shared region admits them, the frame requires them
initialized and unspilled, the context has none. -/
def readBytes (X : Env ρ τ) (m : State ρ) (v : Val) (n : Nat) : StepM (List UInt8) := do
  match v with
  | .loc (.shared sr) o t =>
    if o < 0 then throw (.outOfRegion (.shared sr) o n)
    if sr == .pkt && t != m.machine.layout then throw (.staleToken o)
    unless m.machine.admits sr o.toNat n t do throw (.outOfRegion (.shared sr) o n)
    return m.machine.bytesAt sr o.toNat n
  | .loc .frame o _ => m.frame.readBytes o n
  | .loc .ctx o _ => throw (.outOfRegion .ctx o n)
  | v =>
    let _ := X
    throw (.noRegion v)

/-! ### Jumps -/

/-- The next instruction a target selects, which must be in the
code. -/
def jumpTo (X : Env ρ τ) (m : State ρ) (t : τ) : StepM (State ρ) := do
  match X.conv.resolve X.prog.labels m.pc t with
  | some pc' =>
    unless pc' < X.prog.code.size do throw (.pcOutOfCode pc')
    return { m with pc := pc' }
  | none => throw (.malformed "a jump to a label the program does not define")

/-- Two patterns compared at `cls` bits, signed for the `s` forms. -/
def cmpScalar (cmp : Cmp) (cls : Cls) (a b : Nat) : Bool :=
  let w := cls.bits
  let a := toNatMod a w
  let b := toNatMod b w
  let sa : Int := wrap true w a
  let sb : Int := wrap true w b
  match cmp with
  | .eq => a == b
  | .ne => a != b
  | .gt => a > b
  | .ge => a ≥ b
  | .lt => a < b
  | .le => a ≤ b
  | .sgt => sa > sb
  | .sge => sa ≥ sb
  | .slt => sa < sb
  | .sle => sa ≤ sb
  | .set => (a &&& b) != 0

/-- Two offsets of one region compared. -/
def cmpOffset (cmp : Cmp) (a b : Int) : Bool :=
  match cmp with
  | .eq => a == b
  | .ne => a != b
  | .gt | .sgt => a > b
  | .ge | .sge => a ≥ b
  | .lt | .slt => a < b
  | .le | .sle => a ≤ b
  | .set => (toNatMod a 64 &&& toNatMod b 64) != 0

/-- The condition of `jcond`: two scalars at the class, two locations
of one region by offset, or a location against the immediate zero
under `eq` and `ne`, which a location never satisfies; anything else
is refused. -/
def cond (X : Env ρ τ) (m : State ρ) (cmp : Cmp) (cls : Cls) (a : ρ) (b : Src ρ) :
    StepM Bool := do
  let x ← reg X m a
  match x, b with
  | .loc _ _ _, .imm 0 =>
    match cmp with
    | .eq => return false
    | .ne => return true
    | _ => throw (.badComparison s!"`{cmp.print}` of {x.print} and zero")
  | _, _ =>
    let y ← src X m b
    match x, y with
    | .scalar x, .scalar y => return cmpScalar cmp cls x y
    | .loc r o _, .loc r' o' _ =>
      unless r == r' do
        throw (.badComparison s!"{r.print} + {o} against {r'.print} + {o'}")
      return cmpOffset cmp o o'
    | x, y => throw (.badComparison s!"`{cmp.print}` of {x.print} and {y.print}")

/-! ### Calls -/

/-- The key size a map takes: its key type's for a hash kind, the
4-byte index for the array kinds. -/
def keySize (ms : Machine.MapState) : Nat :=
  match ms.decl.kind with
  | .hash .. => ms.keySize
  | _ => 4

/-- Whether a declaration's result is a location, so that its failure signal
is null rather than a negative return. -/
def yieldsLocation (decl : CallDecl) : Bool :=
  match decl.sig with
  | .fn _ (some (.own ..)) | .fn _ (some (.ref ..)) => true
  | _ => false

/-- The signedness and width a scalar parameter's type fits to. -/
def scalarType : Core.Ty → Bool × Nat
  | .int _ s w => (s, w)
  | .bool _ => (false, 8)
  | .refined _ _ base _ => scalarType base
  | _ => (false, 64)

/-- The innermost held entry must be the resource's on the object. -/
def innermost (m : State ρ) (res : Core.Resource) (obj : Option HeldObj) : StepM Unit := do
  match m.machine.held with
  | h :: _ =>
    unless h.decl.res == res && h.obj == obj do
      throw (.badRelease s!"{h.decl.describe} is the innermost held")
  | [] => throw (.badRelease "nothing is held")

/-- A machine operation run on the shared state; its error is one the
checks before it should have caught, a malformed program. -/
def machineOp (st : Machine.State) (f : Machine.Op α) : StepM (α × Machine.State) :=
  match f.exec st with
  | .ok r => pure r
  | .error e => throw (.malformed e)

def resourceDecl (X : Env ρ τ) (r : Core.Resource) : StepM ResourceDecl :=
  match X.pre.resource? r with
  | some decl => pure decl
  | none => throw (.malformed s!"no declaration for `{r}`")

/-- A builtin: the map and ring operations with the kernel's answers,
the protocol operations on the held stack, `printk` on the trace. A
builtin that is a helper call is refused under a held declaration that
forbids calls, unless it is that declaration's own release. -/
def callBuiltin (X : Env ρ τ) (m : State ρ) (b : Builtin) (args : List Val) :
    StepM (Option Val × Machine.State) := do
  let st := m.machine
  let tok := st.layout
  let name := b.print
  let releases : List ResourceDecl := match b with
    | .submit | .discard => X.pre.resources.filter (·.res == ⟨"ringbuf"⟩)
    | .unlock => X.pre.resources.filter (·.res == ⟨"spinlock"⟩)
    | .leave r => X.pre.resources.filter (·.res == r)
    | _ => []
  if let some h := Machine.forbidsCall st releases then
    throw (.forbiddenCall name h.describe)
  let objOf (v : Val) : StepM HeldObj :=
    match v.heldObj with
    | some obj => pure obj
    | none => throw (.badArgument name s!"{v.print} is not a lock's field or a kernel object")
  match b, args with
  | .tail m', [.handle mn, idx] =>
    -- taken, the machine records the entry and the run stops here;
    -- not taken, nothing happens
    unless mn == m' do throw (.badArgument name s!"`tail` through `{mn}`, declared for `{m'}`")
    let i ← match idx with
      | .scalar i => pure (toNatMod i 32)
      | v => throw (.badArgument name s!"`tail` takes an index, not {v.print}")
    let (_, st') ← machineOp st (Machine.tailCall mn i)
    return (none, st')
  | .lookup, [.handle mn, key] =>
    let some ms := st.map? mn | throw (.malformed s!"unknown map `{mn}`")
    let kb ← readBytes X m key (keySize ms)
    let (r, st') ← machineOp st (Machine.lookup mn kb)
    return (some (match r with
      | some r => .loc (.shared r) 0 tok
      | none => .scalar 0), st')
  | .update, [.handle mn, key, val] =>
    let some ms := st.map? mn | throw (.malformed s!"unknown map `{mn}`")
    let kb ← readBytes X m key ms.keySize
    let vb ← readBytes X m val ms.valueSize
    let (rc, st') ← machineOp st (Machine.update mn kb vb)
    return (some (.scalar (toNatMod rc 64)), st')
  | .delete, [.handle mn, key] =>
    let some ms := st.map? mn | throw (.malformed s!"unknown map `{mn}`")
    let kb ← readBytes X m key ms.keySize
    let (rc, st') ← machineOp st (Machine.delete mn kb)
    return (some (.scalar (toNatMod rc 64)), st')
  | .reserve n, [.handle mn] =>
    let decl ← resourceDecl X ⟨"ringbuf"⟩
    let (r, st') ← machineOp st (Machine.reserve decl mn n)
    return (some (match r with
      | some id => .loc (.kernel id) 0 tok
      | none => .scalar 0), st')
  | .submit, [v] =>
    let obj ← objOf v
    innermost m ⟨"ringbuf"⟩ (some obj)
    let ((), st') ← machineOp st (Machine.submit obj)
    return (none, st')
  | .discard, [v] =>
    let obj ← objOf v
    innermost m ⟨"ringbuf"⟩ (some obj)
    let ((), st') ← machineOp st (Machine.discard obj)
    return (none, st')
  | .lock, [v] =>
    let obj ← objOf v
    let decl ← resourceDecl X ⟨"spinlock"⟩
    if st.held.any (·.decl.res == decl.res) then throw (.lockHeld decl.describe)
    let ((), st') ← machineOp st (Machine.lock decl obj)
    return (none, st')
  | .unlock, [v] =>
    let obj ← objOf v
    innermost m ⟨"spinlock"⟩ (some obj)
    let ((), st') ← machineOp st (Machine.unlock obj)
    return (none, st')
  | .enter r, [] =>
    let decl ← resourceDecl X r
    if decl.nesting == .no && st.held.any (·.decl.res == r) then throw (.lockHeld decl.describe)
    let ((), st') ← machineOp st (Machine.enter decl)
    return (none, st')
  | .leave r, [] =>
    innermost m r none
    let ((), st') ← machineOp st (Machine.leave r)
    return (none, st')
  | .printk fmt n _, vs =>
    -- the first operand locates the format's bytes; the trace records
    -- the format itself
    unless vs.length == n + 1 do throw (.badArgument name s!"{n + 1} arguments expected")
    let mut ws : List Machine.Val := []
    for v in vs.drop 1 do
      match v with
      | .scalar x => ws := ws ++ [.scalar x]
      | v => throw (.badArgument name s!"`printk` takes scalars, not {v.print}")
    let ((), st') ← machineOp st (Machine.print fmt ws)
    return (none, st')
  | _, _ => throw (.badArgument name "the wrong operands")

/-- A kernel function: the arguments fitted to the declaration's parameter
kinds, a scalar reduced to its width, a `ref` or `view` parameter's
bytes read, an owned parameter's object; the call through the
machine, which appends the trace event and pushes or pops the held
stack per the declaration; and the answer as `r0`, a location for an object
handed out, the 64-bit pattern otherwise, the failure signal by the
declaration's result type. -/
def callKernel (X : Env ρ τ) (K : Kernel) (m : State ρ) (name : String) (args : List Val) :
    StepM (Option Val × Machine.State) := do
  let some decl := X.pre.call? name | throw (.malformed s!"unknown kernel function `{name}`")
  let .fn params ret := decl.sig | throw (.malformed s!"`{name}` is a builtin")
  unless args.length == params.length do
    throw (.malformed s!"`{name}` takes {params.length} arguments")
  let st := m.machine
  let mut vs : List Machine.Val := []
  for (p, v) in params.zip args do
    match p.ty with
    | .own .. =>
      match v with
      | .loc (.shared (.kernel id)) _ _ => vs := vs ++ [.object id]
      | _ => throw (.badArgument name s!"`{p.name}` takes an owned reference, not {v.print}")
    | .ref _ t | .view _ t =>
      let some n := X.sizeOf t | throw (.malformed s!"no layout for `{t.print}`")
      vs := vs ++ [.bytes (← readBytes X m v n)]
    | t =>
      match v with
      | .scalar x =>
        let (s, w) := scalarType t
        vs := vs ++ [.scalar (wrap s w x)]
      | _ => throw (.badArgument name s!"`{p.name}` takes a scalar, not {v.print}")
  let releases := Machine.releasesOf X.pre decl
  if let some h := Machine.forbidsCall st releases then
    throw (.forbiddenCall name h.describe)
  if let some rrow := releases.head? then
    innermost m rrow.res (vs.findSome? fun
      | .object id => some (HeldObj.object id)
      | _ => none)
  let (out, st') ← machineOp st (Machine.call X.pre K X.kind decl vs)
  let _ := ret
  match out with
  | .ok v =>
    let r0 ← match v with
      | none => pure (Val.scalar 0)
      | some (.scalar x) => pure (Val.scalar (toNatMod x 64))
      | some (.object id) => pure (Val.loc (.kernel id) 0 st'.layout)
      | some (.bytes _) => throw (.malformed s!"`{name}` answers with bytes")
    return (some r0, st')
  | .failed n =>
    return (some (if yieldsLocation decl then .scalar 0 else .scalar (toNatMod n 64)), st')

/-- How many operands a callee takes on the instruction, under the
explicit convention. -/
def arity (X : Env ρ τ) : Callee → StepM Nat
  | .builtin b => pure b.arity
  | .kernel name =>
    match X.pre.call? name with
    | some { sig := .fn params _, .. } => pure params.length
    | _ => throw (.malformed s!"unknown kernel function `{name}`")

/-- The kernel's argument layout of a callee, which the fixed
convention reads: a builtin's own, a kernel declaration's in the kind, and
for an inline declaration koit's arguments in order. -/
def layout (X : Env ρ τ) : Callee → StepM (List Interface.AbiArg)
  | .builtin b => pure b.abi
  | .kernel name =>
    match X.pre.call? name with
    | some decl =>
      match decl.implIn X.kind.name, decl.sig with
      | .inline, .fn params _ => pure ((List.range params.length).map .arg)
      | impl, _ => pure impl.abi
    | none => throw (.malformed s!"unknown kernel function `{name}`")

/-- The koit arguments read back from the kernel's registers by the
layout: the `i`-th argument from its position, the context checked
where the layout says, the constants and sizes read but not used. -/
def argsByLayout (X : Env ρ τ) (m : State ρ) (h : Callee) (abi : List Interface.AbiArg)
    (regs : List ρ) : StepM (List Val) := do
  let mut found : List (Nat × Val) := []
  for (a, r) in abi.zip regs do
    -- every position is read, as the verifier requires it initialized
    let v ← reg X m r
    match a with
    | .arg i => found := found ++ [(i, v)]
    -- the format's location is the call's first operand
    | .fmt => found := found ++ [(0, v)]
    | .ctx =>
      match v with
      | .loc .ctx _ _ => pure ()
      | v => throw (.badArgument h.print s!"the context expected, not {v.print}")
    | .const _ | .argSize _ => pure ()
  let n := found.length
  (List.range n).mapM fun i =>
    match found.lookup i with
    | some v => pure v
    | none => throw (.malformed s!"`{h.print}`: the layout has no argument {i}")

/-- `call h`: the operands from the instruction or from the
convention's registers by the kernel's layout, the callee, the
result into the instruction's register or the convention's, and the
convention's registers dead after. -/
def call (X : Env ρ τ) (K : Kernel) (m : State ρ) (h : Callee) (args : List ρ) (dst : Option ρ) :
    StepM (State ρ) := do
  let (vs, dstReg, dead) ← match X.conv.fixedCall with
    | some (regs, dead) => do
      let abi ← layout X h
      unless abi.length ≤ regs.length do
        throw (.malformed s!"`{h.print}` takes more than {regs.length} kernel arguments")
      pure (← argsByLayout X m h abi regs, some X.conv.ret, dead)
    | none => pure (← args.mapM (reg X m), dst, [])
  let (res, st') ← match h with
    | .builtin b => callBuiltin X m b vs
    | .kernel name => callKernel X K m name vs
  let m := { m with machine := st' }
  let m := m.clear dead
  match dstReg, res with
  | some d, some v => return m.set d v
  | some d, none =>
    -- the kernel sets `r0` even for a declaration without a result
    if X.conv.fixedCall.isSome then return m.set d (.scalar 0)
    else throw (.malformed s!"`{h.print}` yields nothing to bind")
  | none, _ => return m

/-! ### Atomics -/

/-- `atomic(op, cls, fetch) [d + off] s`: the read-modify-write at
the class's width on a location into a map value or the frame; with
`fetch` the previous value replaces `s`, and `cmpxchg` compares with
and answers in the result register, as the kernel does. -/
def atomic (X : Env ρ τ) (m : State ρ) (op : Core.AtomicOp) (cls : Cls) (fetch : Bool)
    (d : ρ) (off : Int) (s : ρ) : StepM (State ρ) := do
  let base ← reg X m d
  let .scalar x ← reg X m s | throw (.aluOnLocation "an atomic update of a location")
  let w := cls.bits
  match base with
  | .loc (.shared (.map ..)) _ _ | .loc .frame _ _ => pure ()
  | .loc r o _ => throw (.outOfRegion r (o + off) (w / 8))
  | v => throw (.noRegion v)
  let .scalar old ← loadAt X m base off w
    | throw (.aluOnLocation "an atomic update of a spilled location")
  let expected ← match op with
    | .cmpxchg =>
      match ← reg X m X.conv.ret with
      | .scalar e => pure [(e : Int)]
      | v => throw (.aluOnLocation s!"`cmpxchg` against {v.print}")
    | _ => pure []
  let args : List Int := expected ++ [(x : Int)]
  let m ← match Machine.atomic op false w (old : Int) args with
    | some nv => storeAt X m base off w (.scalar (toNatMod nv w))
    | none => pure m
  match op with
  | .cmpxchg => return m.set X.conv.ret (.scalar old)
  | _ => return if fetch then m.set s (.scalar old) else m

/-! ### Halting and the step -/

/-- The width of the kind's verdict. -/
def verdictWidth (kind : KindDecl) : Nat :=
  match kind.verdictTy with
  | .int _ _ w => w
  | _ => 32

/-- A state is halted when its instruction is `exit`, the result
register holds a scalar, and nothing is held; its value is the
scalar at the kind's verdict width. -/
def halted? (X : Env ρ τ) (m : State ρ) : Option Nat :=
  match X.prog.code[m.pc]? with
  | some .exit =>
    -- an `exit` inside a subprogram returns; only the program's halts
    if !m.frames.isEmpty then none else
    match m.regs X.conv.ret with
    | some (.scalar n) =>
      if m.machine.held.isEmpty then some (toNatMod n (verdictWidth X.kind)) else none
    | _ => none
  | _ => none

/-- One step: the next state, or the cause of the refusal. -/
def step (X : Env ρ τ) (K : Kernel) (m : State ρ) : StepM (State ρ) := do
  let some ins := X.prog.code[m.pc]? | throw (.pcOutOfCode m.pc)
  let next (m' : State ρ) : State ρ := { m' with pc := m.pc + 1 }
  match ins with
  | .alu op cls d s => return next (← alu X m op cls d s)
  | .mov cls d s => return next (← mov X m cls d s)
  | .movsx cls w d s => return next (← movsx X m cls w d s)
  | .«end» to w d => return next (← endian X m to w d)
  | .ldx w d s off =>
    let base ← reg X m s
    return next (m.set d (← loadAt X m base off w))
  | .stx w d off s =>
    let base ← reg X m d
    let v ← src X m s
    return next (← storeAt X m base off w v)
  | .ja t => jumpTo X m t
  | .jcond cmp cls a b t =>
    if ← cond X m cmp cls a b then jumpTo X m t else return next m
  | .lddw d k => return next (m.set d (.scalar (toNatMod k 64)))
  | .lea d obj =>
    unless X.conv.lea do throw (.malformed "`lea` in bytecode")
    let some o := X.prog.objects.find? (·.name == obj)
      | throw (.malformed s!"no frame object `{obj}`")
    return next (m.set d (.loc .frame o.base m.machine.layout))
  | .mapref d mn =>
    unless (m.machine.map? mn).isSome do throw (.malformed s!"unknown map `{mn}`")
    return next (m.set d (.handle mn))
  | .mapval d mn k =>
    match m.machine.map? mn with
    | some ms =>
      match ms.decl.kind with
      | .array .. => return next (m.set d (.loc (.map mn 0) k m.machine.layout))
      | _ => throw (.malformed s!"direct value access to `{mn}`, which is not an array")
    | none => throw (.malformed s!"unknown map `{mn}`")
  | .call h args dst => return next (← call X K m h args dst)
  | .arg d i =>
    match m.args[i]? with
    | some v => return next (m.set d v)
    | none => throw (.malformed s!"no argument {i} for the subprogram")
  | .callSub t args dst =>
    -- the caller's registers and frame saved, the callee on a fresh
    -- frame with its arguments: in BIR those on the instruction, in
    -- bytecode the convention's registers as they are
    let vs ← args.mapM fun r => reg X m r
    let saved : Saved ρ := { retPc := m.pc + 1, regs := m.regs, frame := m.frame, dst }
    let m' := { m with frames := saved :: m.frames, frame := Frame.init, args := vs }
    jumpTo X m' t
  | .atomic op cls fetch d off s => return next (← atomic X m op cls fetch d off s)
  | .exit =>
    match m.frames with
    | saved :: rest =>
      -- a return: the caller's registers and frame back, the result
      -- in the convention's register and the instruction's, and the
      -- convention's argument registers dead
      let result := m.regs X.conv.ret
      let mut m' : State ρ := { m with regs := saved.regs, frame := saved.frame,
                                       frames := rest, pc := saved.retPc }
      if let some v := result then m' := m'.set X.conv.ret v
      if let some d := saved.dst then
        if let some v := result then m' := m'.set d v
      if let some (regs, dead) := X.conv.fixedCall then
        for r in regs ++ dead do
          if r != X.conv.ret then m' := { m' with regs := fun r' => if r' = r then none else m'.regs r' }
      return m'
    | [] =>
      if (halted? X m).isSome then throw .halted
      match m.regs X.conv.ret with
      | some (.scalar _) => throw .exitHeld
      | _ => throw .exitNotScalar

/-- The reflexive transitive closure of the successful steps. -/
inductive Star (X : Env ρ τ) (K : Kernel) : State ρ → State ρ → Prop
  | refl (m : State ρ) : Star X K m m
  | step {m m' m'' : State ρ} : step X K m = .ok m' → Star X K m' m'' → Star X K m m''

/-- A halted state with its verdict. -/
def Halted (X : Env ρ τ) (m : State ρ) (v : Nat) : Prop := halted? X m = some v

/-- A state that is neither halted nor steppable: the verifier's
refusals, which the lowering's theorem makes unreachable. -/
def Stuck (X : Env ρ τ) (K : Kernel) (m : State ρ) : Prop :=
  halted? X m = none ∧ ∃ c, step X K m = .error c

end Koit.BPF
