import Koit.Lower.LIR

/-!
Pass I, inlining, LIR to LIR: the call graph is acyclic, so each
`x = call f(args) unwind U absent A` is replaced, callees first, by a
block that binds the callee's parameters and holds its body with the
locals renamed apart and three substitutions: `return e` becomes
`x := e; br d` and a bare `return` becomes `A; br d`, with `d` the
number of constructs between the return and the block that wraps the
inlined body; `raise k e` becomes `U; raise k e`; and a nested
`call g(...) unwind U'` becomes `call g(...) unwind (U'; U)`, which
the recursion then inlines in turn. Scalars bind by value into fresh
locals and locations by copying the location, as the call rule's
frame does. The result is closed LIR: one body per program and no
`call` statements.
-/

namespace Koit.Lower

open Koit (Span)

namespace Inl

/-- A renaming of locals, and a counter for fresh ones. -/
structure IS where
  counter : Nat := 0

abbrev IM := StateM IS

def fresh (base : String) : IM String := do
  let s ← get
  set { s with counter := s.counter + 1 }
  return s!"{base}_i{s.counter}"

abbrev Ren := List (String × String)

def ren (r : Ren) (x : String) : String := (r.lookup x).getD x

mutual

partial def renExpr (r : Ren) : LIR.Expr → LIR.Expr
  | .var x => .var (ren r x)
  | .arith op s w l e => .arith op s w (renExpr r l) (renExpr r e)
  | .cast s w s' w' e => .cast s w s' w' (renExpr r e)
  | .bswap w e => .bswap w (renExpr r e)
  | .load s w a => .load s w (renAddr r a)
  | .addr a => .addr (renAddr r a)
  | e => e

partial def renAddr (r : Ren) : LIR.Addr → LIR.Addr
  | .var x => .var (ren r x)
  | .plus a k => .plus (renAddr r a) k
  | .index a e k => .index (renAddr r a) (renExpr r e) k
  | a => a

end

def renCond (r : Ren) (c : LIR.Cond) : LIR.Cond :=
  { c with l := renExpr r c.l, r := renExpr r c.r }

/-- The block's own declarations given fresh names, so that the
inlined copy declares nothing the caller declares. -/
partial def renameDecls (r : Ren) : List LIR.Stmt → IM Ren
  | [] => return r
  | s :: rest => do
    let r ← match s with
      | .«let» _ x .. | .frame _ x .. => do return (x, ← fresh x) :: r
      | .call _ (some x) .. | .builtin _ (some x) .. | .kernel _ (some x) .. => do
        return (x, ← fresh x) :: r
      | .ite _ _ t e => do renameDecls (← renameDecls r t) e
      | .block _ b | .loop _ b => renameDecls r b
      | .call _ none _ _ u a => do
        renameDecls (← renameDecls r (u.getD [])) (a.getD [])
      | _ => pure r
    renameDecls r rest

/-- `br n` with every escaping index raised by `k`: the branches that
leave more than `depth` constructs are the ones that leave the code
being moved. -/
partial def shiftBr (k : Nat) (depth : Nat) : List LIR.Stmt → List LIR.Stmt
  | [] => []
  | s :: rest =>
    (match s with
     | .br sp n => .br sp (if n ≥ depth then n + k else n)
     | .ite sp c t e => .ite sp c (shiftBr k depth t) (shiftBr k depth e)
     | .block sp b => .block sp (shiftBr k (depth + 1) b)
     | .loop sp b => .loop sp (shiftBr k (depth + 1) b)
     | .call sp x f args u a =>
       .call sp x f args (u.map (shiftBr k depth)) (a.map (shiftBr k depth))
     | s => s) :: shiftBr k depth rest

/-- The callee's body inside the caller: renamed, its returns turned
into stores and branches to the wrapping block, its raises preceded
by the caller's releases, its calls carrying them in their
`unwind`. -/
partial def substBody (r : Ren) (x : Option String) (U A : List LIR.Stmt) (depth : Nat) :
    List LIR.Stmt → List LIR.Stmt
  | [] => []
  | s :: rest =>
    (match s with
     | .«let» sp y t e => [LIR.Stmt.«let» sp (ren r y) t (renExpr r e)]
     | .assign sp y e => [.assign sp (ren r y) (renExpr r e)]
     | .store sp w a e => [.store sp w (renAddr r a) (renExpr r e)]
     | .ctxStore sp f e => [.ctxStore sp f (renExpr r e)]
     | .frame sp y n src => [.frame sp (ren r y) n src]
     | .ite sp c t e =>
       [.ite sp (renCond r c) (substBody r x U A depth t) (substBody r x U A depth e)]
     | .block sp b => [.block sp (substBody r x U A (depth + 1) b)]
     | .loop sp b => [.loop sp (substBody r x U A (depth + 1) b)]
     | .br sp n => [.br sp n]
     | .ret sp (some e) =>
       (match x with
        | some x => [LIR.Stmt.assign sp x (renExpr r e)]
        | none => []) ++ [.br sp depth]
     | .ret sp none => shiftBr (depth + 1) 0 A ++ [.br sp depth]
     | .raise sp k e => U ++ [.raise sp k (renExpr r e)]
     | .call sp y f args u a =>
       [.call sp (y.map (ren r)) f (args.map (renExpr r))
          (u.map fun u' => substBody r x U A depth u' ++ U)
          (a.map (substBody r x U A depth))]
     | .builtin sp y b args => [.builtin sp (y.map (ren r)) b (args.map (renExpr r))]
     | .kernel sp y h args => [.kernel sp (y.map (ren r)) h (args.map (renExpr r))])
    ++ substBody r x U A depth rest

/-- Every call in a block replaced by the callee's inlined body; the
callees' own bodies have been inlined already. -/
partial def inlineStmts (fns : List LIR.Fn) : List LIR.Stmt → IM (List LIR.Stmt)
  | [] => return []
  | s :: rest => do
    let s' ← match s with
      | .call sp x f args u a =>
        match fns.find? (·.name == f) with
        | some d =>
          let U ← inlineStmts fns (u.getD [])
          let A ← inlineStmts fns (a.getD [])
          -- the parameters, bound to the arguments in fresh locals
          let mut r : Ren := []
          let mut binds : List LIR.Stmt := []
          for (p, e) in d.params.zip args do
            let p' ← fresh p.name
            r := (p.name, p') :: r
            binds := binds ++ [.«let» sp p' p.ty e]
          r ← renameDecls r d.body
          -- the absent body's branches leave the wrapping block too
          let body := substBody r x U A 0 d.body
          -- the result, declared before the block that assigns it
          let decl : List LIR.Stmt := match x, d.ret with
            | some x, some t =>
              [.«let» sp x t (match t with
                | .int _ w => .lit w 0
                | .ptr => .lit 64 0)]
            | _, _ => []
          pure (decl ++ [LIR.Stmt.block sp (binds ++ body)])
        | none => pure [s]
      | .ite sp c t e => do pure [.ite sp c (← inlineStmts fns t) (← inlineStmts fns e)]
      | .block sp b => do pure [.block sp (← inlineStmts fns b)]
      | .loop sp b => do pure [.loop sp (← inlineStmts fns b)]
      | s => pure [s]
    return s' ++ (← inlineStmts fns rest)

end Inl

/-- The functions with every callee before its callers, in the
acyclic call graph. -/
partial def calleesFirst (fns : List LIR.Fn) : List LIR.Fn :=
  let callees (f : LIR.Fn) : List String :=
    let rec go : List LIR.Stmt → List String
      | [] => []
      | s :: rest =>
        (match s with
         | .call _ _ g _ u a => g :: go (u.getD []) ++ go (a.getD [])
         | .ite _ _ t e => go t ++ go e
         | .block _ b | .loop _ b => go b
         | _ => []) ++ go rest
    go f.body
  let rec order (done pending : List LIR.Fn) (fuel : Nat) : List LIR.Fn :=
    match fuel with
    | 0 => done ++ pending
    | fuel + 1 =>
      let ready := pending.filter fun f =>
        (callees f).all fun g => g == f.name || done.any (·.name == g)
      if ready.isEmpty then done ++ pending
      else order (done ++ ready) (pending.filter fun f => !ready.any (·.name == f.name)) fuel
  order [] fns fns.length

/-- Pass I: every function inlined into its callers, callees first,
then into the programs; the result has no functions. -/
def inline (u : LIR.CompUnit) : LIR.CompUnit :=
  let go : Inl.IM (List LIR.Program) := do
    let mut done : List LIR.Fn := []
    for f in calleesFirst u.fns do
      let body ← Inl.inlineStmts done f.body
      done := done ++ [{ f with body }]
    u.programs.mapM fun p => do
      let body ← Inl.inlineStmts done p.body
      let handlers ← p.handlers.mapM fun h => do
        pure { h with body := ← Inl.inlineStmts done h.body }
      pure { p with body, handlers }
  let (programs, _) := go.run {}
  { u with fns := [], programs }

end Koit.Lower
