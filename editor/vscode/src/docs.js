// What each construct of the language means, shown when the mouse
// rests on it. The text here is about the construct itself; what a
// call or a context field means comes from the kernel interface the
// compiler carries, and is read out of `koitc interface` instead.

// One entry per keyword: a title line and the explanation under it.
const KEYWORDS = {
  check: [
    "`check e` — discharge a demand at runtime",
    "A place the checker cannot prove in range is a demand. `check`",
    "tests the condition, adds it to the facts that hold from there",
    "on, and sends the failing path to the `invariant` handler. It is",
    "the one way to turn a fact the checker cannot see into one it can."
  ],
  hold: [
    "`hold r { ... }` — take a resource for a block",
    "The resource is acquired on entry and released on every exit from",
    "the block, including a failing one. Inside, what the resource",
    "forbids is rejected: under `lock(p)` there are no calls, no",
    "resize, and no sleep, and locks do not nest."
  ],
  where: [
    "`where` — a refinement carried in the type",
    "`var n: u64 where n <= MAX_KEY` means every value of `n` satisfies",
    "the bound, at every assignment. An index built from `n` is then in",
    "range by the type alone, with no second test at the use."
  ],
  fails: [
    "`fails k` — the failure kinds a function may raise",
    "A function that can fail says so in its signature, so the caller",
    "sees the obligation at the call and must mark it."
  ],
  fail: [
    "`fail r` — raise a failure with reason `r`",
    "Control goes to the handler for this kind, which runs the cleanup",
    "the resources in scope require and then exits with its verdict.",
    "`else fail r` puts a reason on a fallible operation."
  ],
  bounded: [
    "`bounded` — the loop's trip count is known",
    "Every loop in a program is bounded, because the verifier must see",
    "termination. The bound is part of the loop, not a hope about it."
  ],
  preserve: [
    "`preserve R` — the program writes nothing in `R`",
    "A header clause or a contract clause: no statement of the program,",
    "nor of the functions it calls, may carry a write effect meeting",
    "`R`. A program that preserves any packet range may not resize the",
    "packet, since a resize moves every byte."
  ],
  move: [
    "`move` — hand over an owned reference",
    "The source is no longer usable; ownership is what makes the",
    "release exactly once."
  ],
  own: [
    "`own T` — an owned reference",
    "Acquired from a call that says so, released on every path out,",
    "and released exactly once. A leak and a double release are both",
    "type errors."
  ],
  ref: [
    "`ref T` — a borrowed reference",
    "Valid for the region it came from; it does not carry the",
    "obligation to release."
  ],
  view: [
    "`view T` — a typed window into the packet",
    "`pkt.view<T>(off)` tests once that the window lies inside the",
    "packet. A field of the view is then a place, needing no further",
    "test, until something resizes the packet."
  ],
  program: [
    "`program name : kind` — an attachable program",
    "The kind fixes what the context offers, which verdicts exist,",
    "and which calls are in scope. `fail v` after the kind names the",
    "verdict an unhandled failure exits with."
  ],
  contract: [
    "`contract` — what a program of a kind must satisfy",
    "A program declares `implements`, and the checker holds it to the",
    "contract's exits, effects, and preserved state."
  ],
  implements: [
    "`implements c` — this program satisfies contract `c`"
  ],
  map: [
    "`map m : storage[n] of T` — kernel-side storage",
    "The element type is a koit type, refinements included, so what a",
    "slot holds is known without reading it: a fresh map is zero, and",
    "every write has been checked against the refinement."
  ],
  config: [
    "`config` — a value fixed before load",
    "Known to the checker as a constant, so a bound stated in terms of",
    "it is decided at compile time."
  ],
  const: ["`const` — a compile-time constant"],
  type: ["`type T = { ... }` — a named layout, fields and refinements"],
  license: ["`license` — the module's license, as the kernel reads it"],
  let: ["`let x = e` — an immutable binding"],
  var: ["`var x = e` — a mutable binding"],
  as: [
    "`e as T` — a cast between machine types",
    "Widening and narrowing are explicit, because the verifier tracks",
    "the range of each register and a silent truncation loses it."
  ],
  repeat: [
    "`repeat n { ... }` — a loop with a literal bound",
    "The trip count is in the source, so termination is syntactic."
  ],
  for: [
    "`for i in 0..n { ... }` — a loop over a bounded range",
    "`i` carries the range as a refinement inside the body."
  ],
  pass: [
    "`pass` — exit, letting the packet through",
    "A statement, not a value: it is `return` of this kind's verdict of",
    "that name, `PASS` in an `xdp` program and `OK` in a `tc` one. The",
    "resources held here are released on the way out."
  ],
  drop: [
    "`drop` — exit, discarding the packet",
    "A statement: `return` of this kind's verdict of that name, `DROP`",
    "in an `xdp` program and `SHOT` in a `tc` one."
  ],
  tx: [
    "`tx` — exit, sending the packet back out the way it came",
    "A statement: `return TX`. Only kinds whose table has the verdict",
    "offer the word."
  ],
  abort: [
    "`abort` — exit, reporting an error",
    "A statement: `return ABORTED`. The kernel fires its exception",
    "tracepoint on this verdict, so a failure stays observable."
  ],
  verdict: [
    "`verdict in { ... }` — the verdicts this program may return",
    "A header clause, not a value. The names inside the braces are the",
    "kind's own verdicts, written bare; every exit of the program, every",
    "handler's exit, and the default failure verdict are checked against",
    "the set, so a contract cannot be satisfied by failing."
  ],
  except: [
    "`except` — the maps a `preserve maps` clause lets through",
    "The list runs to the end of the clause, so a further region needs",
    "its own `preserve`."
  ],
  pkt: [
    "`pkt` — the packet the program was handed",
    "A dynamic region: nothing in it is readable until a test says so,",
    "and a resize drops every window carved from it."
  ],
  ctx: ["`ctx` — the context the kind offers, field by field"],
  reason: [
    "`reason` — inside a handler, what the failing site passed",
    "For a helper failure it is the helper's negative return."
  ],
  short_packet: [
    "failure kind `short_packet`",
    "A read or a view that reaches past the end of the packet."
  ],
  missing: ["failure kind `missing` — a lookup found nothing"],
  invariant: [
    "failure kind `invariant`",
    "A `check` whose condition did not hold at runtime."
  ],
  bound: ["failure kind `bound` — an index outside its range"],
  helper: [
    "failure kind `helper`",
    "A kernel call returned an error; `reason` is its negative return."
  ]
};

// The machine types. Width and byte order are both in the type, so a
// comparison that mixes them does not type.
const TYPES = {
  u8: "an 8-bit unsigned integer",
  u16: "a 16-bit unsigned integer",
  u32: "a 32-bit unsigned integer",
  u64: "a 64-bit unsigned integer",
  i8: "an 8-bit signed integer",
  i16: "a 16-bit signed integer",
  i32: "a 32-bit signed integer",
  i64: "a 64-bit signed integer",
  be16: "a 16-bit big-endian integer",
  be32: "a 32-bit big-endian integer",
  be64: "a 64-bit big-endian integer",
  bool: "a boolean"
};

const BYTE_ORDER =
  "Byte order is in the type: comparing it to a host value needs " +
  "`hton` or `ntoh`, and the checker rejects the mix that a C program " +
  "gets wrong silently.";

// The markdown shown for a word, or null when the word is not one of
// the language's own.
function keywordDoc(word) {
  if (KEYWORDS[word]) {
    const lines = KEYWORDS[word];
    return lines[0] + "\n\n" + lines.slice(1).join(" ");
  }
  if (TYPES[word]) {
    let text = "`" + word + "` — " + TYPES[word];
    if (word.startsWith("be")) text += "\n\n" + BYTE_ORDER;
    return text;
  }
  return null;
}

// The `?` that marks a fallible operation, hovered on its own.
const FALLIBLE_DOC =
  "`?` — this operation can fail\n\n" +
  "A fallible operation is marked where it is written, so the cost is " +
  "visible in the source. On failure, control goes to the handler for " +
  "its kind; `else fail r` gives that handler a reason.";

// The kinds a failure can have, which are what a handler table is
// written over.
const FAILURE_KINDS =
  ["short_packet", "missing", "invariant", "bound", "helper", "program"];

// The four ways a map is declared, each with what follows its name.
const MAP_KINDS = [
  { name: "array", snippet: "array[${1:n}] of ${2:T}",
    doc: "a fixed number of slots, indexed; a fresh one is zero" },
  { name: "percpu_array", snippet: "percpu_array[${1:n}] of ${2:T}",
    doc: "one array per cpu, so no update contends with another" },
  { name: "hash", snippet: "hash[${1:n}] of ${2:K} -> ${3:V}",
    doc: "a lookup keyed by a value; a miss is a `missing` failure" },
  { name: "ringbuf", snippet: "ringbuf[${1:bytes}]",
    doc: "a queue to userspace; `reserve` takes an owned reference" }
];

// The statements and expressions worth offering whole, where writing
// the construct means writing more than its first word.
const SNIPPETS = [
  { label: "check", body: "check ${1:condition}",
    detail: "discharge a demand at runtime" },
  { label: "hold", body: "hold lock(${1:place}) {\n\t$0\n}",
    detail: "take a lock for a block" },
  { label: "for", body: "for ${1:i} in 0..${2:n} {\n\t$0\n}",
    detail: "a loop over a bounded range" },
  { label: "repeat", body: "repeat ${1:n} {\n\t$0\n}",
    detail: "a loop with a literal bound" },
  { label: "if", body: "if ${1:condition} {\n\t$0\n}",
    detail: "a branch; its test is a fact inside" },
  { label: "if let", body: "if let ${1:x} = ${2:e} {\n\t$0\n}",
    detail: "bind when the operation succeeds" }
];

// The declarations, offered where a declaration may stand.
const DECL_SNIPPETS = [
  { label: "program",
    body: "program ${1:name} : ${2:xdp} fail ${3:pass} {\n\t$0\n}",
    detail: "an attachable program" },
  { label: "fn", body: "fn ${1:name}(${2:x}: ${3:u32}) -> ${4:u32} {\n\t$0\n}",
    detail: "a function" },
  { label: "type", body: "type ${1:Name} = { ${2:field}: ${3:u32} }",
    detail: "a named layout" },
  { label: "map", body: "map ${1:name} : array[${2:n}] of ${3:T}",
    detail: "kernel-side storage" },
  { label: "const", body: "const ${1:NAME} = ${2:0}",
    detail: "a compile-time constant" },
  { label: "contract", body: "contract ${1:Name} : ${2:xdp} {\n\t$0\n}",
    detail: "what a program of a kind must satisfy" }
];

module.exports = {
  keywordDoc, FALLIBLE_DOC, FAILURE_KINDS, MAP_KINDS, SNIPPETS, DECL_SNIPPETS
};
