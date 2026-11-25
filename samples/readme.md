# Koka Examples

* `learn`: start with this folder where each file
  describes a particular feature of Koka, like `with`-syntax, implicit parameters, local qualification, etc.
* `handlers`: examples of algebraic effect handlers.
* `basic`: some small Koka programs that demonstrate various features.  
* `wasi-web`: running Koka in the browser as a plain WebAssembly module with the
  `--target=wasi-web` backend — see `wasi-web/dom/readme.md` for a DOM interop demo
  where Koka drives browser elements through Perceus-owned references
  (requires [wasi-sdk](https://github.com/WebAssembly/wasi-sdk/releases) ≥ 34 and node ≥ 24).

## VS Code integration

Inside the VS Code editor, it can be useful to see the inferred types, fully qualified names, and implicit
parameters. Press and hold `ctrl+alt` (or `ctrl+option` on MacOS) to show these inlay hints.

If you hold `ctrl/cmd` while hovering over a type in VS Code you will also see the constructors or 
effect operations (and a further click will take you to the definition).

Moreover, you can execute any `main`, `test..`, and `example..` functions directly in the debug console by clicking on the `run debug | optimized` code lenses displayed above these functions.

