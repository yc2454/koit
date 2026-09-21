# koit for Visual Studio Code

Syntax, live checking, and hover documentation for koit.

Everything the extension shows comes from `koitc`: the squiggles are
the checker's diagnostics, the hovers over calls and context fields
are the kernel interface the compiler carries, and the bytecode and
the C are what the back end emits. The extension reimplements nothing
about the language, so it cannot drift from it.

## What it does

- **Highlighting.** A TextMate grammar over the language's own
  keywords. The constructs that carry an obligation — `check`, `hold`,
  `where`, `fails`, and the `?` on a fallible operation — are coloured
  apart from ordinary control flow, so what the type system is doing
  is visible in the source.
- **Checking while you type.** The buffer is checked after a quarter
  second of quiet, saved or not, through `koitc check --json`, which
  reports both ends of the span. The squiggle covers the construct the
  diagnostic is about — the whole fallible expression, the whole
  packet access — not a point in it. The status bar says which kernel
  the unit was checked against.
- **Hover.** Over a construct, what the construct means. Over a call,
  a context field, a verdict, or a resource, its entry in the kernel
  interface: the signature, the effects, how it can fail, and which
  kinds may use it. Over a name the unit declares, its declaration.
- **Above each program**, three lenses: run it on a packet, show its
  bytecode, show its C.

## Running it

The extension needs a built `koitc`. From the repository root:

```
lake build koitc
```

Then either open this folder in VS Code and press <kbd>F5</kbd>, which
opens a second window with the extension loaded, or install it for
everyday use:

```
ln -s "$PWD/editor/vscode" ~/.vscode/extensions/koit
```

and restart VS Code. Open any `.ko` file.

## Settings

| setting | what it does |
| --- | --- |
| `koit.koitcPath` | the compiler to use; by default `.lake/build/bin/koitc` under the workspace, then `koitc` on `PATH` |
| `koit.kernel` | the kernel tag the file is checked against |
| `koit.checkOnType` | re-check while typing, rather than only on save |
| `koit.cpu` | the instruction set used for bytecode and for running |

## Layout

    package.json                 the manifest: language, grammar, commands, settings
    language-configuration.json  comments, brackets, indentation
    syntaxes/koit.tmLanguage.json  the grammar
    src/extension.js             diagnostics, hover, lenses, commands
    src/interface.js             `koitc interface`, indexed by name
    src/docs.js                  what each construct means
