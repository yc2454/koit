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
  except: [
    "`except` — the exits a contract permits",
    "Narrows what the implementing program may do on a path."
  ],
  bounded: [
    "`bounded` — the loop's trip count is known",
    "Every loop in a program is bounded, because the verifier must see",
    "termination. The bound is part of the loop, not a hope about it."
  ],
  preserve: [
    "`preserve` — what the program must leave intact",
    "Named in a contract, checked of the program that implements it."
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
  pass: ["`pass` — exit with the verdict that lets the packet through"],
  drop: ["`drop` — exit with the verdict that discards the packet"],
  tx: ["`tx` — exit with the verdict that sends the packet back out"],
  abort: ["`abort` — exit with the verdict that reports an error"],
  verdict: ["`verdict` — the value a program exits with"],
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

module.exports = { keywordDoc, FALLIBLE_DOC };
