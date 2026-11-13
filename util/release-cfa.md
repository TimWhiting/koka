Koka with **control-flow analysis**: HMCFA (Whiting & Germane, ICFP 2026) and Demand m-CFA (Whiting & Germane,
ESOP 2025), on top of Koka `dev` after the v3.2.9 release (the compiler reports itself as Koka 3.3.0).

This is a research build, not an official Koka release. It installs side by side with the official Koka if you give it
its own prefix.

### Install the compiler

Linux and macOS:

```sh
curl -sSL https://github.com/TimWhiting/koka/releases/download/v3.2.9-cfa/install.sh | sh -s -- --minimal --prefix=$HOME/.koka-cfa
```

Windows (cmd): download `install.bat` from this release and run

```bat
install.bat --version v3.2.9-cfa -p %LOCALAPPDATA%\koka-cfa
```

### Install the VS Code extension

Download `language-koka-3.2.100.vsix` from this release, then `code --install-extension language-koka-3.2.100.vsix`
(or Extensions view, `...` menu, *Install from VSIX...*). Point it at the compiler above with the setting
`"koka.languageServer.compiler": "~/.koka-cfa/bin/koka"` (Windows: `%LOCALAPPDATA%\koka-cfa\bin\koka.exe`).

Open a Koka file and click the telescope button in the editor title bar for the HMCFA view.
