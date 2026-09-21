// The kernel interface, read out of `koitc interface --kernel TAG`
// and indexed by name, so that hovering a call or a context field
// shows what the compiler itself knows about it: the signature, the
// effects, how it can fail, and which kinds may use it.
//
// The interface is fixed for a kernel tag, so it is read once per tag
// and kept.

// An entry is a line at column zero and the indented lines under it.
function entries(text) {
  const out = [];
  let cur = null;
  for (const line of text.split("\n")) {
    if (/^\S/.test(line)) {
      if (cur) out.push(cur);
      cur = { head: line.replace(/\s+$/, ""), body: [] };
    } else if (cur && line.trim()) {
      cur.body.push(line.replace(/\s+$/, ""));
    }
  }
  if (cur) out.push(cur);
  return out;
}

// The whole entry as the interface prints it, for the hover body.
function render(entry) {
  return [entry.head, ...entry.body].join("\n");
}

// Indexes one kernel's interface: name -> { label, text }.
function index(text, kernel) {
  const byName = new Map();
  const put = (name, label, text) => {
    if (name && !byName.has(name)) byName.set(name, { label, text });
  };

  for (const e of entries(text)) {
    const head = e.head;
    let m;

    // A call: `fn name(args) -> ret effects { ... } fails k in kinds`,
    // or `builtin name`, which the compiler lowers itself.
    if ((m = head.match(/^(fn|builtin)\s+([A-Za-z_][A-Za-z0-9_.]*)/))) {
      const kind = m[1] === "builtin" ? "builtin" : "call";
      put(m[2], `${kind}, kernel ${kernel}`, render(e));
      // `pkt.len` is also hovered as `len`.
      if (m[2].includes(".")) {
        put(m[2].split(".").pop(), `${kind}, kernel ${kernel}`, render(e));
      }
      continue;
    }

    // A program kind, with its context fields and its verdicts.
    if ((m = head.match(/^kind\s+([A-Za-z_][A-Za-z0-9_]*)/))) {
      const name = m[1];
      put(name, `program kind, kernel ${kernel}`, render(e));
      // Each context field is hovered on its own.
      for (const line of e.body) {
        const f = line.match(/^\s*ctx\s+([A-Za-z_][A-Za-z0-9_]*)\s*:\s*(.*)$/);
        if (f) {
          put(f[1], `context field of \`${name}\``,
              `ctx ${f[1]} : ${f[2]}`);
        }
      }
      // Each verdict of the kind, so `PASS` and `pass` both say
      // which kind they belong to.
      const v = head.match(/verdicts\s*\{([^}]*)\}/);
      if (v) {
        for (const w of v[1].trim().split(/\s+/)) {
          put(w, `verdict of \`${name}\``,
              `${w}, one of the verdicts of \`${name}\`:\n${head.trim()}`);
        }
      }
      continue;
    }

    if ((m = head.match(/^resource\s+([A-Za-z_][A-Za-z0-9_]*)/))) {
      put(m[1], `resource, kernel ${kernel}`, render(e));
      continue;
    }
    if ((m = head.match(/^region\s+([A-Za-z_][A-Za-z0-9_ ]*?)\s*:/))) {
      put(m[1].trim().split(/\s+/).pop(), `region, kernel ${kernel}`,
          render(e));
      continue;
    }
    if ((m = head.match(/^slot\s+([A-Za-z_][A-Za-z0-9_]*)/))) {
      put(m[1], `slot, kernel ${kernel}`, render(e));
      continue;
    }
    if ((m = head.match(/^const\s+([A-Za-z_][A-Za-z0-9_]*)/))) {
      put(m[1], `constant of the interface, kernel ${kernel}`, head.trim());
      continue;
    }
    if ((m = head.match(/^type\s+([A-Za-z_][A-Za-z0-9_]*)/))) {
      put(m[1], `type of the interface, kernel ${kernel}`, render(e));
      continue;
    }
  }
  return byName;
}

module.exports = { index };
