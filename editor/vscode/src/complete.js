// What may be written at a position, offered as the list pops up.
//
// The buffer is broken while it is being typed — `ctx.` is not a
// program — so nothing here asks the compiler about the text at the
// cursor. What is offered comes from two things that hold anyway:
// the kernel interface, which is fixed for a kernel tag, and the kind
// of the program the cursor is in, which the header above it names.
// So a call restricted to `xdp` and `tc` is not offered inside a
// `syscall` program, and `tx` is not offered in a `tc` one, because
// `tc` has no such verdict.

const vscode = require("vscode");
const {
  keywordDoc, FAILURE_KINDS, MAP_KINDS, SNIPPETS, DECL_SNIPPETS
} = require("./docs");

const K = vscode.CompletionItemKind;

// The machine types, which are always in scope.
const PRIMITIVES =
  ["u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64",
   "be16", "be32", "be64", "bool"];

// The words that make sense inside a body, as words.
const STATEMENT_WORDS =
  ["let", "var", "if", "else", "for", "in", "repeat", "break", "continue",
   "return", "check", "hold", "fail", "where", "as", "move", "true",
   "false"];

// The words a declaration starts with, offered beside the snippets so
// that typing one matches whether or not the snippet is wanted.
const DECL_WORDS =
  ["program", "fn", "type", "map", "const", "config", "contract",
   "license"];

// What may stand between a program's header and its body.
const HEADER_WORDS = [
  { label: "verdict", body: "verdict in { ${1:PASS} }",
    detail: "the verdicts this program may return" },
  { label: "preserve", body: "preserve ${1:pkt}",
    detail: "a region the program writes nothing in" },
  { label: "on", body: "on ${1:short_packet} { $0 }",
    detail: "a handler for a kind of failure" },
  { label: "default", body: "default { ${1:drop} }",
    detail: "what a failure with no handler of its own does" },
  { label: "implements", body: "implements ${1:Contract}",
    detail: "the contract this program satisfies" }
];

// A contract states the same clauses, and nothing else.
const CONTRACT_WORDS = HEADER_WORDS.filter(
  (w) => w.label === "verdict" || w.label === "preserve");

function item(label, kind, detail, doc) {
  const it = new vscode.CompletionItem(label, kind);
  if (detail) it.detail = detail;
  if (doc) it.documentation = new vscode.MarkdownString(doc);
  return it;
}

function snippet(label, body, detail, doc) {
  const it = item(label, K.Snippet, detail, doc);
  it.insertText = new vscode.SnippetString(body);
  return it;
}

// A line without what a comment or a string literal covers, so that
// neither the brace counter nor the context tests read them.
function bare(line) {
  return line.replace(/"(\\.|[^"\\])*"/g, '""')
             .replace(/'(\\.|[^'\\])*'/g, "''")
             .replace(/\/\/.*$/, "");
}

// Whether the cursor is inside a comment or a string, where there is
// nothing to offer.
function inText(prefix) {
  if (/\/\//.test(prefix)) return true;
  const quotes = (prefix.match(/"/g) || []).length;
  const ticks = (prefix.match(/'/g) || []).length;
  return quotes % 2 === 1 || ticks % 2 === 1;
}

// The program whose body the cursor is in, by the nearest header
// above it, and null above the first one. A `fn` is not tied to a
// kind, so a cursor inside one is treated the same way.
function enclosingKind(doc, line) {
  for (let i = line; i >= 0; i--) {
    const head = /^\s*(?:program|contract)\s+[A-Za-z_]\w*\s*:\s*([a-z_]+)/;
    const m = bare(doc.lineAt(i).text).match(head);
    if (m) return m[1];
  }
  return null;
}

// How deep in brackets the cursor is, so that a declaration is
// offered where a declaration may stand and a statement where a
// statement may.
function depthAt(doc, pos) {
  let depth = 0;
  for (let i = 0; i <= pos.line; i++) {
    let text = bare(doc.lineAt(i).text);
    if (i === pos.line) text = bare(doc.lineAt(i).text.slice(0, pos.character));
    for (const c of text) {
      if (c === "{") depth++;
      else if (c === "}") depth--;
    }
  }
  return depth;
}

// Whether the cursor stands between a program's header and its body,
// where a handler goes. Walking back over blank lines, comments, and
// the handlers already written must reach the header itself; the
// brace that opens the body, or the one that closed it, ends the walk.
function inHeader(doc, line) {
  for (let i = line - 1; i >= 0; i--) {
    const text = bare(doc.lineAt(i).text).trim();
    if (!text) continue;
    if (/^on\b/.test(text)) continue;
    return /^(program|contract)\s+[A-Za-z_]\w*\s*:/.test(text);
  }
  return false;
}

// Whether the cursor is inside a contract, whose body holds the same
// clauses a program's header does and no statements at all.
function inContract(doc, line) {
  for (let i = line; i >= 0; i--) {
    const text = bare(doc.lineAt(i).text).trim();
    if (/^contract\s+[A-Za-z_]\w*\s*:/.test(text)) return true;
    if (/^(program|fn)\s+[A-Za-z_]\w*/.test(text)) return false;
  }
  return false;
}

// What this unit declares, read off the declaration lines. The
// checker knows this properly; here it only has to be enough to
// offer a name that exists.
function localNames(doc) {
  const out = { maps: [], types: [], consts: [], fns: [], contracts: [] };
  const where = {
    map: "maps", type: "types", const: "consts", config: "consts",
    fn: "fns", contract: "contracts"
  };
  for (let i = 0; i < doc.lineCount; i++) {
    const decl = /^\s*(map|type|const|config|fn|contract)\s+([A-Za-z_]\w*)/;
    const m = bare(doc.lineAt(i).text).match(decl);
    if (m) {
      out[where[m[1]]].push({
        name: m[2], line: (doc.lineAt(i).text.trim()), word: m[1]
      });
    }
  }
  return out;
}

// The text of a declaration, from its line until its brackets close.
function declText(doc, word, name) {
  const head = new RegExp(`^\\s*${word}\\s+${name}\\b`);
  for (let i = 0; i < doc.lineCount; i++) {
    if (!head.test(bare(doc.lineAt(i).text))) continue;
    let text = "";
    let depth = 0;
    for (let j = i; j < doc.lineCount && j < i + 48; j++) {
      const line = bare(doc.lineAt(j).text);
      text += (j === i ? line.trim() : " " + line.trim());
      for (const c of line) {
        if ("{[(".includes(c)) depth++;
        else if ("}])".includes(c)) depth--;
      }
      if (depth <= 0) break;
    }
    return text;
  }
  return null;
}

// The fields a record type declares, in order. A refinement on a
// field carries no colon, so splitting the braces at the commas that
// are not nested is enough to find the names.
function fieldsOf(doc, name) {
  const text = declText(doc, "type", name);
  if (!text) return null;
  const open = text.indexOf("{");
  if (open < 0) return null;
  const body = text.slice(open + 1, text.lastIndexOf("}"));
  const parts = [];
  let depth = 0;
  let cur = "";
  for (const c of body) {
    if ("{[(".includes(c)) depth++;
    else if ("}])".includes(c)) depth--;
    if (c === "," && depth === 0) { parts.push(cur); cur = ""; }
    else cur += c;
  }
  parts.push(cur);
  const fields = [];
  for (const part of parts) {
    const m = part.trim().match(/^([A-Za-z_]\w*)\s*:\s*(.+)$/);
    if (m) fields.push({ name: m[1], type: m[2].trim() });
  }
  return fields.length ? fields : null;
}

// The element type of a map, which is what indexing it gives.
function elementOf(doc, name) {
  const text = declText(doc, "map", name);
  if (!text) return null;
  const arrow = text.match(/->\s*([A-Za-z_]\w*)/);
  if (arrow) return arrow[1];
  const of = text.match(/\bof\s+([A-Za-z_]\w*)/);
  return of ? of[1] : null;
}

// The type a name holds, where the binding says so plainly: a window
// carved from the packet, or a slot of a map. Nothing else is
// guessed, so a name whose type only the checker knows offers
// nothing rather than something wrong.
function typeOfName(doc, line, name) {
  const bind = new RegExp(`\\b(?:let|var)\\s+${name}\\s*(?::[^=]*)?=\\s*(.*)$`);
  for (let i = line; i >= 0; i--) {
    const m = bare(doc.lineAt(i).text).match(bind);
    if (!m) continue;
    const rhs = m[1];
    const view = rhs.match(/pkt\s*\.\s*view\s*<\s*([A-Za-z_]\w*)/);
    if (view) return view[1];
    const slot = rhs.match(/^\s*([A-Za-z_]\w*)\s*\[/);
    if (slot) return elementOf(doc, slot[1]);
    return null;
  }
  return null;
}

// The types that may be named: the machine types, what the unit
// declares, and what the interface brings.
function typeItems(doc, model) {
  const items = PRIMITIVES.map((t) =>
    item(t, K.TypeParameter, "a machine type", keywordDoc(t)));
  // `verdict` names the enclosing program's kind's verdict type.
  items.push(item("verdict", K.TypeParameter,
                  "the enclosing kind's verdict type", keywordDoc("verdict")));
  for (const q of ["own", "ref", "view"]) {
    items.push(item(q, K.Keyword, "a qualifier on what follows",
                    keywordDoc(q)));
  }
  for (const t of localNames(doc).types) {
    items.push(item(t.name, K.Struct, "declared in this unit", t.line));
  }
  for (const t of model.types) {
    items.push(item(t.name, K.Struct, `from the interface, ${model.kernel}`,
                    "```koit\n" + t.text + "\n```"));
  }
  return items;
}

// The calls a program of this kind may make. A call the interface
// restricts to other kinds is not offered at all, which is the whole
// point of asking the interface rather than a word list.
function callItems(model, kind) {
  const items = [];
  for (const c of model.calls) {
    if (c.name.includes(".")) continue;
    if (kind && c.kinds && !c.kinds.includes(kind)) continue;
    const it = item(c.name, K.Function, c.detail,
                    "```koit\n" + c.text + "\n```" +
                    (c.note ? "\n\n" + c.note : ""));
    it.insertText = new vscode.SnippetString(`${c.name}($0)`);
    items.push(it);
  }
  return items;
}

// The verdicts of this kind, by the words a program writes: `tc` has
// `pass` and `drop` and no `tx`, and `syscall` has none of them.
function verdictItems(model, kind) {
  const k = kind ? model.kinds.get(kind) : null;
  if (!k) return [];
  return k.sugar.map((s) =>
    item(s.word, K.Keyword, `exit with ${s.verdict}`,
         keywordDoc(s.word) ||
         `Exits the program with the verdict \`${s.verdict}\`.`));
}

// The whole list for a position.
function completions(doc, pos, model) {
  const line = doc.lineAt(pos.line).text;
  const prefix = line.slice(0, pos.character);
  if (inText(prefix)) return [];

  const kind = enclosingKind(doc, pos.line);
  const k = kind ? model.kinds.get(kind) : null;
  const local = localNames(doc);

  // `ctx.` — the fields this kind offers, and no others.
  if (/\bctx\s*\.\s*[A-Za-z0-9_]*$/.test(prefix)) {
    if (!k) return [];
    return k.ctx.map((f) => item(
      f.name, K.Field, f.type + (f.writable ? ", writable" : ", read-only"),
      `A context field of \`${kind}\`` +
      (f.writable ? "." : ", which a program may read but not write.")));
  }

  // `pkt.` — the window, the length, and the resizes, where the kind
  // has a packet at all.
  if (/\bpkt\s*\.\s*[A-Za-z0-9_]*$/.test(prefix)) {
    if (k && !k.packet) return [];
    const items = [snippet(
      "view", "view<${1:T}>(${2:0})?", "carve a typed window",
      keywordDoc("view"))];
    for (const c of model.calls) {
      if (!c.name.startsWith("pkt.")) continue;
      if (kind && c.kinds && !c.kinds.includes(kind)) continue;
      const short = c.name.slice(4);
      const it = item(short, K.Method, c.detail,
                      "```koit\n" + c.text + "\n```");
      it.insertText = new vscode.SnippetString(`${short}($0)`);
      items.push(it);
    }
    return items;
  }

  // `pkt.view<` — the type of the window.
  if (/\bview\s*<\s*[A-Za-z0-9_]*$/.test(prefix)) return typeItems(doc, model);

  // `name.` and `name[i].` — the fields of the type the name holds,
  // where the binding or the map declaration says what that is. A
  // name whose type only the checker knows offers nothing, rather
  // than a list that does not belong to it.
  const dot = prefix.match(/\b([A-Za-z_]\w*)\s*(\[[^\]]*\])?\s*\.\s*\w*$/);
  if (dot) {
    const [, name, indexed] = dot;
    if (local.types.some((t) => t.name === name)) {
      return [item("size", K.Constant, "the byte width of " + name,
                   "The size of `" + name + "`, a constant the compiler " +
                   "computes from its layout.")];
    }
    const ty = indexed ? elementOf(doc, name)
                       : typeOfName(doc, pos.line, name);
    const fields = ty ? fieldsOf(doc, ty) : null;
    if (!fields) return [];
    return fields.map((f) => item(
      f.name, K.Field, f.type, `A field of \`${ty}\`.`));
  }

  // `verdict in { ` — the names inside the braces are the kind's own
  // verdicts, written bare. They are not expressions, so nothing else
  // belongs here.
  if (/\bverdict\s+in\s*\{[^}]*$/.test(prefix)) {
    if (!k) return [];
    return k.verdicts.map((v) => item(
      v, K.EnumMember, `a verdict of \`${kind}\``,
      `One of the verdicts \`${kind}\` may return. Inside this clause ` +
      "it is a bare name, not an expression."));
  }

  // `on ` — the kinds a failure can have.
  if (/^\s*on\s+[A-Za-z0-9_]*$/.test(prefix)) {
    return FAILURE_KINDS.map((f) => {
      const it = item(f, K.EnumMember, "a failure kind", keywordDoc(f));
      it.insertText = new vscode.SnippetString(`${f} { $0 }`);
      return it;
    });
  }

  // `program p : ` and `contract c : ` — the kinds there are.
  if (/^\s*(program|contract)\s+[A-Za-z_][A-Za-z0-9_]*\s*:\s*[A-Za-z0-9_]*$/
        .test(prefix)) {
    return [...model.kinds.values()].map((x) => item(
      x.name, K.Class,
      x.verdicts.length ? `verdicts ${x.verdicts.join(", ")}` : "no verdicts",
      "```koit\n" + x.text + "\n```"));
  }

  // `map m : ` — the four storages, each with what follows it.
  if (/^\s*map\s+[A-Za-z_][A-Za-z0-9_]*\s*:\s*[A-Za-z0-9_]*$/.test(prefix)) {
    return MAP_KINDS.map((m) =>
      snippet(m.name, m.snippet, m.doc, m.doc));
  }

  // `implements ` — the contracts this unit declares.
  if (/\bimplements\s+[A-Za-z0-9_]*$/.test(prefix)) {
    return local.contracts.map((c) =>
      item(c.name, K.Interface, "declared in this unit", c.line));
  }

  // `hold ` — the only thing that names a lock.
  if (/\bhold\s+[A-Za-z0-9_]*$/.test(prefix)) {
    return [snippet("lock", "lock(${1:place}) {\n\t$0\n}",
                    "take the lock in a map value", keywordDoc("hold"))];
  }

  // A type is wanted after a colon that is not a header's.
  if (/:\s*[A-Za-z0-9_]*$/.test(prefix)) return typeItems(doc, model);

  // Otherwise: what may stand here. Between a header and a body that
  // is a handler; at the top level a declaration; inside a body a
  // statement.
  const items = [];
  if (depthAt(doc, pos) <= 0) {
    if (inHeader(doc, pos.line)) {
      for (const h of HEADER_WORDS) {
        items.push(snippet(h.label, h.body, h.detail, keywordDoc(h.label)));
      }
      return items;
    }
    for (const d of DECL_SNIPPETS) {
      items.push(snippet(d.label, d.body, d.detail, keywordDoc(d.label)));
    }
    for (const w of DECL_WORDS) {
      items.push(item(w, K.Keyword, "a declaration", keywordDoc(w)));
    }
    return items;
  }

  if (inContract(doc, pos.line)) {
    for (const w of CONTRACT_WORDS) {
      items.push(snippet(w.label, w.body, w.detail, keywordDoc(w.label)));
    }
    return items;
  }

  for (const s of SNIPPETS) {
    items.push(snippet(s.label, s.body, s.detail, keywordDoc(s.label)));
  }
  for (const w of STATEMENT_WORDS) {
    items.push(item(w, K.Keyword, null, keywordDoc(w)));
  }
  items.push(...verdictItems(model, kind));
  items.push(...callItems(model, kind));
  if (!k || k.packet) {
    items.push(item("pkt", K.Variable, "the packet", keywordDoc("pkt")));
  }
  if (k && k.ctx.length) {
    items.push(item("ctx", K.Variable, `the context of \`${kind}\``,
                    keywordDoc("ctx")));
  }
  for (const m of local.maps) {
    items.push(item(m.name, K.Variable, "a map of this unit", m.line));
  }
  for (const c of local.consts) {
    items.push(item(c.name, K.Constant, "declared in this unit", c.line));
  }
  for (const f of local.fns) {
    const it = item(f.name, K.Function, "declared in this unit", f.line);
    it.insertText = new vscode.SnippetString(`${f.name}($0)`);
    items.push(it);
  }
  for (const c of model.consts) {
    items.push(item(c.name, K.Constant,
                    `= ${c.value}, from the interface`, null));
  }
  items.push(...typeItems(doc, model).filter((t) => t.kind === K.Struct));
  return items;
}

module.exports = { completions };
