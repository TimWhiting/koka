// VFS bridge functions for the Koka playground
// Called from Haskell via foreign import javascript

function h$kokaVfsReadFile(p, cont) {
  var r = globalThis.kokaVFS.readFile(p);
  if (r && r.then) {
    r.then(cont);
  } else {
    cont(r);
  }
}

function h$kokaVfsFileExists(p) {
  return globalThis.kokaVFS.fileExists(p);
}

function h$kokaVfsFileSize(p) {
  return globalThis.kokaVFS.fileSize(p);
}

function h$kokaVfsWriteFile(p, c) {
  globalThis.kokaVFS.writeFile(p, c);
}

function h$kokaVfsRemoveFile(p) {
  globalThis.kokaVFS.removeFile(p);
}

// Playground entry point functions
function h$kokaSetCompiler(cb) {
  globalThis.kokaCompile = cb;
}

function h$kokaSetResult(s) {
  globalThis.kokaResult = s;
}

function h$kokaKeepAlive(cont) {
  // Never call cont - keeps the Haskell runtime alive for callbacks
}
