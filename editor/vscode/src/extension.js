// The koit extension. Everything it shows comes from `koitc` itself:
// the diagnostics are the checker's, the hovers are the compiler's
// kernel interface, and the bytecode and the C are what the back end
// emits. Nothing about the language is reimplemented here.

const vscode = require("vscode");
const cp = require("child_process");
const fs = require("fs");
const os = require("os");
const path = require("path");
const crypto = require("crypto");

const { keywordDoc, FALLIBLE_DOC } = require("./docs");
const { index } = require("./interface");

let diagnostics;   // the squiggles, one collection for the extension
let output;        // the channel the commands print to
let status;        // the status bar item, checked or not
let interfaces;    // kernel tag -> name -> hover entry
let virtualDocs;   // uri string -> text, for the read-only panes
let virtualEmitter;
let timers;        // uri string -> the pending re-check

// ---------------------------------------------------------------- //
// Finding and running the compiler
// ---------------------------------------------------------------- //

// The `koitc` to use: the setting, then the build output of each
// workspace folder, then whatever is on PATH.
function koitcPath() {
  const koit = vscode.workspace.getConfiguration("koit");
  const configured = koit.get("koitcPath");
  if (configured) return configured;
  for (const folder of vscode.workspace.workspaceFolders || []) {
    const built = path.join(
      folder.uri.fsPath, ".lake", "build", "bin", "koitc");
    if (fs.existsSync(built)) return built;
  }
  return "koitc";
}

function kernelTag() {
  return vscode.workspace.getConfiguration("koit").get("kernel") || "v6.8";
}

function cpuFlag() {
  return vscode.workspace.getConfiguration("koit").get("cpu") || "v3";
}

// Runs the compiler and hands back both streams and the exit code. A
// failure to spawn is reported as code 127 rather than thrown, so the
// caller can say what was missing.
function runKoitc(args, cwd) {
  return new Promise((resolve) => {
    cp.execFile(koitcPath(), args, { cwd, maxBuffer: 32 * 1024 * 1024 },
      (err, stdout, stderr) => {
        if (err && err.code === undefined && err.errno !== undefined) {
          resolve({ code: 127, stdout: "", stderr: String(err.message) });
        } else {
          resolve({ code: err ? err.code || 1 : 0, stdout, stderr });
        }
      });
  });
}

// The document's text on disk, so that an unsaved edit is checked
// too. The name keeps the `.ko` suffix the compiler expects.
function snapshot(doc) {
  const dir = path.join(os.tmpdir(), "koit-vscode");
  fs.mkdirSync(dir, { recursive: true });
  const tag = crypto.createHash("sha1").update(doc.uri.toString())
    .digest("hex").slice(0, 8);
  const file = path.join(dir, `${tag}-${path.basename(doc.fileName)}`);
  fs.writeFileSync(file, doc.getText());
  return file;
}

function workspaceOf(doc) {
  const folder = vscode.workspace.getWorkspaceFolder(doc.uri);
  return folder ? folder.uri.fsPath : path.dirname(doc.fileName);
}

// ---------------------------------------------------------------- //
// Diagnostics
// ---------------------------------------------------------------- //

// A position the compiler named, as a position in the document: it
// counts lines and columns from one, the editor from zero.
function positionOf(doc, line, col) {
  const l = Math.min(Math.max(0, line - 1), Math.max(0, doc.lineCount - 1));
  const width = doc.lineCount ? doc.lineAt(l).text.length : 0;
  return new vscode.Position(l, Math.min(Math.max(0, col - 1), width));
}

// The span of a diagnostic as a range to underline. The compiler
// gives both ends, so the squiggle covers the whole construct; a
// span of no width, which is what a lexical error carries, is widened
// to the word it points at so that there is something to see.
function rangeOf(doc, d) {
  const from = positionOf(doc, d.start.line, d.start.col);
  const to = positionOf(doc, d.stop.line, d.stop.col);
  if (from.line !== to.line || from.character !== to.character) {
    return new vscode.Range(from, to);
  }
  const word = doc.getWordRangeAtPosition(from);
  if (word) return word;
  return new vscode.Range(from, doc.lineAt(from.line).range.end);
}

// The text form, `file:line:col: message`, read for a `koitc` too old
// to know `--json`. It names one end only, so the squiggle covers the
// word there.
function fromText(doc, stderr) {
  const found = [];
  for (const line of stderr.split("\n")) {
    const m = line.match(/^(.*?):(\d+):(\d+):\s*(.*)$/);
    if (!m) continue;
    const pos = positionOf(doc, Number(m[2]), Number(m[3]));
    const word = doc.getWordRangeAtPosition(pos);
    found.push(new vscode.Diagnostic(
      word || new vscode.Range(pos, doc.lineAt(pos.line).range.end),
      m[4], vscode.DiagnosticSeverity.Error));
  }
  return found;
}

async function check(doc) {
  if (doc.languageId !== "koit") return;
  const file = snapshot(doc);
  const r = await runKoitc(
    ["check", "--json", "--kernel", kernelTag(), file], workspaceOf(doc));

  if (r.code === 127) {
    diagnostics.set(doc.uri, []);
    status.text = "$(error) koit: koitc not found";
    status.tooltip = "Build it with `lake build koitc`, or set koit.koitcPath.";
    status.show();
    return;
  }

  let found = null;
  try {
    const report = JSON.parse(r.stdout);
    found = report.diagnostics.map((d) => new vscode.Diagnostic(
      rangeOf(doc, d), d.msg, vscode.DiagnosticSeverity.Error));
  } catch (e) {
    // Not a report, so either an older compiler or a failure it did
    // not put in the document.
    found = fromText(doc, r.stderr);
  }

  // A failure the compiler did not place, so that it is still seen.
  if (!found.length && r.code !== 0) {
    const msg = r.stderr.trim() || `koitc exited with ${r.code}`;
    found.push(new vscode.Diagnostic(
      new vscode.Range(0, 0, 0, 1), msg, vscode.DiagnosticSeverity.Error));
  }
  for (const d of found) d.source = `koit ${kernelTag()}`;
  diagnostics.set(doc.uri, found);

  if (found.length) {
    status.text = `$(error) koit: ${found[0].message.slice(0, 48)}`;
    status.tooltip = found[0].message;
  } else {
    status.text = `$(pass) koit: checked against ${kernelTag()}`;
    status.tooltip =
      "The checker accepted this unit: every demand is entailed, every " +
      "fallible operation is marked, and every resource is released.";
  }
  status.show();
}

// A re-check while typing, once the keystrokes stop.
function scheduleCheck(doc) {
  const key = doc.uri.toString();
  clearTimeout(timers.get(key));
  timers.set(key, setTimeout(() => check(doc), 250));
}

// ---------------------------------------------------------------- //
// Hover
// ---------------------------------------------------------------- //

// The interface of a kernel tag, read once and kept.
async function interfaceFor(tag, cwd) {
  if (interfaces.has(tag)) return interfaces.get(tag);
  const r = await runKoitc(["interface", "--kernel", tag], cwd);
  const table = r.code === 0 ? index(r.stdout, tag) : new Map();
  interfaces.set(tag, table);
  return table;
}

// What this file itself declares, so that hovering a map, a type, or
// a program of the unit shows its declaration.
function localDecl(doc, word) {
  const re = new RegExp(
    `^\\s*(const|config|type|map|fn|program|contract)\\s+${word}\\b`);
  for (let i = 0; i < doc.lineCount; i++) {
    if (!re.test(doc.lineAt(i).text)) continue;
    // A declaration runs until its brackets close, so that a record
    // type is shown whole rather than cut off at its first line.
    // The body of a function or a program is not part of its
    // declaration, so a head that opens one stops there.
    const hasBody = /^\s*(fn|program|contract)\b/.test(doc.lineAt(i).text);
    const lines = [];
    let depth = 0;
    for (let j = i; j < doc.lineCount && j < i + 24; j++) {
      const text = doc.lineAt(j).text;
      lines.push(j === i ? text.trim() : text);
      for (const c of text) {
        if ("{[(".includes(c)) depth++;
        else if ("}])".includes(c)) depth--;
      }
      if (depth <= 0) break;
      if (hasBody && /\{\s*$/.test(text)) break;
    }
    return {
      label: `declared in this unit, line ${i + 1}`,
      text: lines.join("\n").replace(/\s+$/, "")
    };
  }
  return null;
}

function markdown(label, code, prose) {
  const md = new vscode.MarkdownString();
  md.appendMarkdown(`*${label}*\n\n`);
  if (code) md.appendCodeblock(code, "koit");
  if (prose) md.appendMarkdown("\n" + prose);
  md.isTrusted = true;
  return md;
}

const hoverProvider = {
  async provideHover(doc, pos) {
    // The `?` that marks a fallible operation is not a word.
    const here = doc.lineAt(pos.line).text[pos.character];
    if (here === "?") {
      return new vscode.Hover(new vscode.MarkdownString(FALLIBLE_DOC));
    }

    const range = doc.getWordRangeAtPosition(pos);
    if (!range) return null;
    const word = doc.getText(range);

    // The language's own constructs come first: they are what the
    // hover is for.
    const own = keywordDoc(word);
    if (own) {
      const md = new vscode.MarkdownString(own);
      return new vscode.Hover(md, range);
    }

    // Then what this unit declares.
    const local = localDecl(doc, word);
    if (local) {
      return new vscode.Hover(markdown(local.label, local.text), range);
    }

    // Then the kernel interface the compiler carries.
    const table = await interfaceFor(kernelTag(), workspaceOf(doc));
    const entry = table.get(word);
    if (entry) {
      return new vscode.Hover(markdown(entry.label, entry.text), range);
    }
    return null;
  }
};

// ---------------------------------------------------------------- //
// Code lenses: what can be done with a program, above the program
// ---------------------------------------------------------------- //

const lensProvider = {
  provideCodeLenses(doc) {
    const lenses = [];
    for (let i = 0; i < doc.lineCount; i++) {
      const m = doc.lineAt(i).text
        .match(/^\s*program\s+([A-Za-z_][A-Za-z0-9_]*)/);
      if (!m) continue;
      const range = new vscode.Range(i, 0, i, 1);
      const args = [doc.uri, m[1]];
      lenses.push(new vscode.CodeLens(range, {
        title: "$(play) run on a packet", command: "koit.run", arguments: args
      }));
      lenses.push(new vscode.CodeLens(range, {
        title: "$(file-binary) bytecode", command: "koit.showBytecode",
        arguments: args
      }));
      lenses.push(new vscode.CodeLens(range, {
        title: "$(code) C", command: "koit.showC", arguments: args
      }));
    }
    return lenses;
  }
};

// ---------------------------------------------------------------- //
// The read-only panes the commands open
// ---------------------------------------------------------------- //

const contentProvider = {
  get onDidChange() { return virtualEmitter.event; },
  provideTextDocumentContent(uri) {
    return virtualDocs.get(uri.toString()) || "";
  }
};

async function openPane(name, text) {
  const uri = vscode.Uri.parse(`koit-out:${name}`);
  virtualDocs.set(uri.toString(), text);
  virtualEmitter.fire(uri);
  const doc = await vscode.workspace.openTextDocument(uri);
  await vscode.window.showTextDocument(doc, {
    viewColumn: vscode.ViewColumn.Beside, preview: true, preserveFocus: true
  });
}

// The document a command acts on: the one the lens sits in, or the
// active editor when the command came from the palette.
function targetDoc(uri) {
  if (uri) {
    const open = vscode.workspace.textDocuments
      .find((d) => d.uri.toString() === uri.toString());
    if (open) return open;
  }
  const active = vscode.window.activeTextEditor;
  if (active && active.document.languageId === "koit") return active.document;
  return null;
}

async function emitPane(uri, args, suffix, title) {
  const doc = targetDoc(uri);
  if (!doc) return;
  const file = snapshot(doc);
  const r = await runKoitc(
    [...args, "--kernel", kernelTag(), file], workspaceOf(doc));
  if (r.code !== 0) {
    vscode.window.showErrorMessage(
      "koit: " + (r.stderr.trim().split("\n").pop() ||
                  "the unit did not compile"));
    return;
  }
  const base = path.basename(doc.fileName, ".ko");
  await openPane(`${base}${suffix}`, `// ${title}\n\n${r.stdout}`);
}

// ---------------------------------------------------------------- //

function activate(context) {
  diagnostics = vscode.languages.createDiagnosticCollection("koit");
  output = vscode.window.createOutputChannel("koit");
  status = vscode.window.createStatusBarItem(
    vscode.StatusBarAlignment.Left, 100);
  interfaces = new Map();
  virtualDocs = new Map();
  virtualEmitter = new vscode.EventEmitter();
  timers = new Map();

  const koit = { language: "koit" };
  context.subscriptions.push(
    diagnostics, output, status, virtualEmitter,
    vscode.languages.registerHoverProvider(koit, hoverProvider),
    vscode.languages.registerCodeLensProvider(koit, lensProvider),
    vscode.workspace.registerTextDocumentContentProvider(
      "koit-out", contentProvider)
  );

  // Check on open, on save, and while typing when asked to.
  context.subscriptions.push(
    vscode.workspace.onDidOpenTextDocument(check),
    vscode.workspace.onDidSaveTextDocument(check),
    vscode.workspace.onDidChangeTextDocument((e) => {
      if (vscode.workspace.getConfiguration("koit").get("checkOnType")) {
        scheduleCheck(e.document);
      }
    }),
    vscode.workspace.onDidCloseTextDocument((d) => diagnostics.delete(d.uri)),
    vscode.window.onDidChangeActiveTextEditor((e) => {
      if (e && e.document.languageId === "koit") check(e.document);
      else status.hide();
    }),
    // A new kernel tag means a new interface and a new check.
    vscode.workspace.onDidChangeConfiguration((e) => {
      if (e.affectsConfiguration("koit")) {
        interfaces.clear();
        vscode.workspace.textDocuments.forEach(check);
      }
    })
  );

  context.subscriptions.push(
    vscode.commands.registerCommand("koit.check", () => {
      const doc = targetDoc(null);
      if (doc) check(doc);
    }),

    vscode.commands.registerCommand("koit.showBytecode", (uri) =>
      emitPane(uri, ["emit", "--asm", "--cpu", cpuFlag()], ".bpf",
        `the bytecode of this unit, ${cpuFlag()}, in LLVM's syntax`)),

    vscode.commands.registerCommand("koit.showC", (uri) =>
      emitPane(uri, ["emit"], ".c", "the C this unit lowers to")),

    vscode.commands.registerCommand("koit.showInterface", async () => {
      const doc = targetDoc(null);
      const cwd = doc ? workspaceOf(doc) : undefined;
      const tag = kernelTag();
      const r = await runKoitc(["interface", "--kernel", tag], cwd);
      if (r.code !== 0) {
        vscode.window.showErrorMessage(`koit: ${r.stderr.trim()}`);
        return;
      }
      await openPane(`interface-${tag}.ko`, r.stdout);
    }),

    vscode.commands.registerCommand("koit.run", async (uri, program) => {
      const doc = targetDoc(uri);
      if (!doc) return;
      const hex = await vscode.window.showInputBox({
        title: program ? `Run \`${program}\` on a packet` : "Run on a packet",
        prompt: "The packet, in hex. Empty runs it on no packet at all.",
        value: "00112233445566778899aabb0800"
      });
      if (hex === undefined) return;
      const file = snapshot(doc);
      const args = ["run", "--kernel", kernelTag()];
      if (hex.trim()) args.push("--packet", hex.trim().replace(/\s+/g, ""));
      if (program) args.push("--program", program);
      args.push(file);

      output.clear();
      output.show(true);
      output.appendLine(`koitc ${args.join(" ")}`);
      output.appendLine("");
      const r = await runKoitc(args, workspaceOf(doc));
      output.append(r.stdout);
      if (r.stderr.trim()) output.append(r.stderr);
    })
  );

  // The file that is already open when the extension starts.
  const active = vscode.window.activeTextEditor;
  if (active && active.document.languageId === "koit") check(active.document);
}

function deactivate() {
  for (const t of timers.values()) clearTimeout(t);
}

module.exports = { activate, deactivate };
