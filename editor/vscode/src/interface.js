// The kernel interface, read out of `koitc interface --kernel TAG`.
//
// Two things come out of it: an index by name, so that hovering a
// call or a context field shows what the compiler knows about it, and
// a model of the kinds and the calls, so that what is offered at a
// position is only what a program of that kind may write. The
// interface is fixed for a kernel tag, so it is read once per tag.

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

// The note the interface puts after a call, without its `//`.
function noteOf(text) {
  const m = text.match(/\/\/\s*(.*)$/m);
  return m ? m[1].trim() : "";
}

// What a call's entry says without the note: the signature, the
// effects, and how it fails, which is what a completion shows on the
// right of the name.
function detailOf(text) {
  return text.replace(/\/\/.*$/gm, "").replace(/\s+/g, " ").trim();
}

// Reads the whole interface into { byName, kinds, calls, types,
// consts }. `kinds` is keyed by name; a call's `kinds` is the list it
// is restricted to, or null when every kind may call it.
function parse(text, kernel) {
  const byName = new Map();
  const put = (name, label, body) => {
    if (name && !byName.has(name)) byName.set(name, { label, text: body });
  };
  const kinds = new Map();
  const calls = [];
  const types = [];
  const consts = [];

  const all = entries(text);

  // The kinds first, so that a call's `in xdp, tc` can be read
  // against the names that exist.
  for (const e of all) {
    const m = e.head.match(/^kind\s+([A-Za-z_][A-Za-z0-9_]*)/);
    if (!m) continue;
    const name = m[1];
    const whole = render(e);
    const kind = {
      name,
      packet: !/\bpkt\s+none\b/.test(e.head),
      verdicts: [],
      sugar: [],
      ctx: [],
      text: whole
    };
    const v = whole.match(/verdicts\s*\{([^}]*)\}/);
    if (v) kind.verdicts = v[1].trim().split(/\s+/).filter(Boolean);
    const s = whole.match(/sugar\s*\{([^}]*)\}/);
    if (s) {
      for (const pair of s[1].split(",")) {
        const p = pair.split("=");
        if (p.length === 2) {
          kind.sugar.push({ word: p[0].trim(), verdict: p[1].trim() });
        }
      }
    }
    const field = /^\s*ctx\s+([A-Za-z_]\w*)\s*:\s*([A-Za-z_]\w*)(.*)$/;
    for (const line of e.body) {
      const f = line.match(field);
      if (f) {
        kind.ctx.push({
          name: f[1], type: f[2], writable: /\bwritable\b/.test(f[3])
        });
      }
    }
    kinds.set(name, kind);

    put(name, `program kind, kernel ${kernel}`, whole);
    for (const f of kind.ctx) {
      put(f.name, `context field of \`${name}\``,
          `ctx ${f.name} : ${f.type}${f.writable ? "  writable" : ""}`);
    }
    for (const w of kind.verdicts) {
      put(w, `verdict of \`${name}\``,
          `${w}, one of the verdicts of \`${name}\`:\n${e.head.trim()}`);
    }
  }

  for (const e of all) {
    const head = e.head;
    const whole = render(e);
    let m;

    // A call: `fn name(args) -> ret effects { ... } fails k in kinds`,
    // or `builtin name`, which the compiler lowers itself.
    if ((m = head.match(/^(fn|builtin)\s+([A-Za-z_][A-Za-z0-9_.]*)/))) {
      const label = m[1] === "builtin" ? "builtin" : "call";
      const name = m[2];
      // `in xdp, tc` restricts a call to those kinds; a call without
      // it is in scope everywhere. The note is dropped first, since
      // the restriction is the last thing the entry says.
      let only = null;
      const where = detailOf(whole).match(/\bin\s+([a-z_][A-Za-z0-9_,\s]*)$/);
      if (where) {
        const named = where[1].split(",").map((w) => w.trim())
          .filter((w) => kinds.has(w));
        if (named.length) only = named;
      }
      calls.push({
        name, label, kinds: only, text: whole,
        detail: detailOf(whole), note: noteOf(whole),
        builtin: m[1] === "builtin"
      });
      put(name, `${label}, kernel ${kernel}`, whole);
      if (name.includes(".")) {
        put(name.split(".").pop(), `${label}, kernel ${kernel}`, whole);
      }
      continue;
    }

    if ((m = head.match(/^resource\s+([A-Za-z_][A-Za-z0-9_]*)/))) {
      put(m[1], `resource, kernel ${kernel}`, whole);
      continue;
    }
    if ((m = head.match(/^region\s+([A-Za-z_][A-Za-z0-9_ ]*?)\s*:/))) {
      put(m[1].trim().split(/\s+/).pop(), `region, kernel ${kernel}`, whole);
      continue;
    }
    if ((m = head.match(/^slot\s+([A-Za-z_][A-Za-z0-9_]*)/))) {
      put(m[1], `slot, kernel ${kernel}`, whole);
      continue;
    }
    if ((m = head.match(/^const\s+([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(.*)$/))) {
      consts.push({ name: m[1], value: m[2].trim() });
      put(m[1], `constant of the interface, kernel ${kernel}`, head.trim());
      continue;
    }
    if ((m = head.match(/^type\s+([A-Za-z_][A-Za-z0-9_]*)/))) {
      types.push({ name: m[1], text: whole });
      put(m[1], `type of the interface, kernel ${kernel}`, whole);
      continue;
    }
  }

  return { kernel, byName, kinds, calls, types, consts };
}

module.exports = { parse };
