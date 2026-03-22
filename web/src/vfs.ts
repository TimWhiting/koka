/**
 * vfs.ts
 *
 * In-memory Virtual File System for the Koka playground.
 * Installed as `globalThis.kokaVFS` so the compiled WASM/JS compiler can
 * read and write files without touching the real disk.
 *
 * Preloading: call preloadFromManifest() and preloadPrecompiled() on startup
 * to seed the VFS with stdlib sources and precompiled .kki/.mjs files.
 */

export interface VFSEntry {
  content: string;
  /** Unix epoch milliseconds */
  time: number;
}

/** Shape exposed on globalThis.kokaVFS */
export interface KokaVFSGlobal {
  readFile(path: string): string | null | Promise<string | null>;
  fileExists(path: string): boolean;
  fileTime(path: string): number;
  writeFile(path: string, content: string): void;
  listDir(path: string): string[];
  createDir(path: string): void;
  dirExists(path: string): boolean;
  fileSize(path: string): number;
  removeFile(path: string): void;
}

export class KokaVFS {
  private files: Map<string, VFSEntry> = new Map();
  /** Set of directory paths that have been explicitly created */
  private dirs: Set<string> = new Set();
  /** In-flight fetch promises, keyed by normalised path */
  private pendingFetches: Map<string, Promise<string | null>> = new Map();

  /**
   * Set of VFS paths that came from precompiled files.
   * Used to distinguish precompiled .mjs from freshly generated ones.
   */
  private precompiledPaths: Set<string> = new Set();

  /**
   * Precompiled .mjs content keyed by filename (e.g. "std_core.mjs").
   * Used by the module runner to supply runtime modules.
   */
  public precompiledMjs: Map<string, string> = new Map();

  /** When true, VFS hits/misses for .kki/.mjs paths are sent to kokaOnCompilerLog */
  public logVfs: boolean = false;

  constructor() {
    // Always ensure the root exists
    this.dirs.add('/');
  }

  // ── Public helpers ────────────────────────────────────────────────────────

  /** Add / overwrite a file in the VFS. */
  addFile(path: string, content: string, time?: number): void {
    const key = this.normalize(path);
    this.files.set(key, { content, time: time ?? Date.now() });
    // Ensure all parent directories exist
    this.ensureParents(key);
  }

  /** Explicitly remove a file. */
  removeFile(path: string): void {
    this.files.delete(this.normalize(path));
  }

  /** Return every file written by the compiler (all files in VFS). */
  getWrittenFiles(): Map<string, string> {
    const out = new Map<string, string>();
    for (const [k, v] of this.files) {
      out.set(k, v.content);
    }
    return out;
  }

  /**
   * Return only newly generated .mjs files — those written by the compiler
   * during the current compile run, not preloaded precompiled files.
   */
  getGeneratedMjs(): Map<string, string> {
    const out = new Map<string, string>();
    for (const [k, v] of this.files) {
      if (k.endsWith('.mjs') && !this.precompiledPaths.has(k)) {
        out.set(k, v.content);
      }
    }
    return out;
  }

  /**
   * Clear compiler-generated output files (main.mjs, main.kki) so that the
   * next compilation starts fresh.
   */
  clearGeneratedOutput(): void {
    for (const key of [...this.files.keys()]) {
      if (!this.precompiledPaths.has(key) &&
          (key.endsWith('/main.mjs') || key.endsWith('/main.kki'))) {
        this.files.delete(key);
      }
    }
  }

  /**
   * Alias for clearGeneratedOutput — clears only user-module generated files.
   */
  clearGenerated(): void {
    this.clearGeneratedOutput();
  }

  /** Install this VFS as globalThis.kokaVFS. */
  install(): void {
    const self = this;
    const vfs: KokaVFSGlobal = {
      readFile:   (p) => self.readFile(p),
      fileExists: (p) => self.fileExists(p),
      fileTime:   (p) => self.fileTime(p),
      writeFile:  (p, c) => self.writeFile(p, c),
      listDir:    (p) => self.listDir(p),
      createDir:  (p) => self.createDir(p),
      dirExists:  (p) => self.dirExists(p),
      fileSize:   (p) => self.fileSize(p),
      removeFile: (p) => self.removeFile(p),
    };
    (globalThis as Record<string, unknown>)['kokaVFS'] = vfs;
  }

  // ── Preloading ────────────────────────────────────────────────────────────

  /**
   * Fetch a JSON manifest (array of relative paths) and load all listed files
   * into the VFS at `/share/lib/<path>`.
   *
   * @param baseUrl       URL prefix for fetching files (e.g. '/lib' or '')
   * @param manifestPath  URL/path to the JSON manifest file
   */
  async preloadSources(baseUrl: string, manifestPath: string): Promise<number> {
    const resp = await fetch(manifestPath);
    if (!resp.ok) throw new Error(`Failed to fetch manifest ${manifestPath}: ${resp.status}`);
    const manifest: string[] = await resp.json();

    const prefix = baseUrl ? baseUrl.replace(/\/$/, '') + '/lib/' : 'lib/';
    await Promise.all(manifest.map(async (f) => {
      try {
        const r = await fetch(prefix + f);
        if (r.ok) {
          const text = await r.text();
          this.addFile('/share/lib/' + f, text);
        }
      } catch {
        // ignore individual file failures
      }
    }));

    return manifest.length;
  }

  /**
   * Alias for preloadSources — accepts a baseUrl prefix and manifest URL.
   * @deprecated Use preloadSources instead.
   */
  async preloadFromManifest(baseUrl: string, manifestUrl: string): Promise<number> {
    const resp = await fetch(manifestUrl);
    if (!resp.ok) throw new Error(`Failed to fetch manifest ${manifestUrl}: ${resp.status}`);
    const manifest: string[] = await resp.json();

    await Promise.all(manifest.map(async (f) => {
      try {
        const r = await fetch(baseUrl + '/' + f);
        if (r.ok) {
          const text = await r.text();
          this.addFile('/share/lib/' + f, text);
        }
      } catch {
        // ignore individual file failures
      }
    }));

    return manifest.length;
  }

  /**
   * Return the precompiled .mjs modules keyed by filename (e.g. "std_core.mjs").
   * Used by the module runner to supply runtime modules.
   */
  getPrecompiledMjs(): Map<string, string> {
    return this.precompiledMjs;
  }

  /**
   * Fetch a precompiled manifest and load:
   *   - `.kki` files into `/lib/js-debug/<filename>` with a far-future timestamp
   *     so the compiler treats them as fresh cache entries.
   *   - `.mjs` files into `precompiledMjs` for use by the module runner,
   *     and also into the VFS so the compiler can find them.
   *
   * @param baseUrl       URL prefix for fetching files (e.g. '' or '/precompiled')
   * @param manifestPath  URL/path to the JSON manifest file
   */
  async preloadPrecompiled(baseUrl: string, manifestPath: string): Promise<number> {
    const resp = await fetch(manifestPath);
    if (!resp.ok) throw new Error(`Failed to fetch manifest ${manifestPath}: ${resp.status}`);
    const manifest: string[] = await resp.json();

    // Far-future timestamp so the compiler considers these files fresh cache
    const kkiTime = Date.now() + 100_000_000;

    const prefix = baseUrl ? baseUrl.replace(/\/$/, '') + '/precompiled/' : 'precompiled/';
    await Promise.all(manifest.map(async (f) => {
      try {
        const r = await fetch(prefix + f);
        if (!r.ok) return;
        const text = await r.text();

        if (f.endsWith('.kki')) {
          const vfsPath = '/lib/js-debug/' + f;
          this.files.set(this.normalize(vfsPath), { content: text, time: kkiTime });
          this.ensureParents(this.normalize(vfsPath));
          this.precompiledPaths.add(this.normalize(vfsPath));
        }

        if (f.endsWith('.mjs')) {
          // Store for module runner
          this.precompiledMjs.set(f, text);
          // Also place in VFS so compiler can reference it if needed
          const vfsPath = '/lib/js-debug/' + f;
          this.files.set(this.normalize(vfsPath), { content: text, time: kkiTime });
          this.ensureParents(this.normalize(vfsPath));
          this.precompiledPaths.add(this.normalize(vfsPath));
        }
      } catch {
        // ignore individual file failures
      }
    }));

    return manifest.length;
  }

  // ── VFS operations ────────────────────────────────────────────────────────

  readFile(path: string): string | null {
    const key = this.normalize(path);
    const entry = this.files.get(key);
    if (entry !== undefined) return entry.content;
    return null;
  }

  fileExists(path: string): boolean {
    const key = this.normalize(path);
    const exists = this.files.has(key);
    if (this.logVfs) {
      const interesting = key.endsWith('.kki') || key.endsWith('.mjs');
      if (interesting) {
        const logFn = (globalThis as Record<string, unknown>)['kokaOnCompilerLog'] as ((msg: string) => void) | undefined;
        if (logFn) {
          logFn(exists ? '[vfs HIT] ' + key : '[vfs miss] ' + key);
        }
      }
    }
    return exists;
  }

  /** Returns the modification time in milliseconds, or 0 if not found. */
  fileTime(path: string): number {
    return this.files.get(this.normalize(path))?.time ?? 0;
  }

  writeFile(path: string, content: string): void {
    this.addFile(path, content);
  }

  /** List direct children (files and directories) of a directory. */
  listDir(path: string): string[] {
    const dir = this.normalizeDir(path);
    const children = new Set<string>();

    for (const key of this.files.keys()) {
      if (key.startsWith(dir)) {
        const rest = key.slice(dir.length);
        const slash = rest.indexOf('/');
        children.add(slash === -1 ? rest : rest.slice(0, slash));
      }
    }
    for (const d of this.dirs) {
      if (d !== dir && d.startsWith(dir)) {
        const rest = d.slice(dir.length);
        const slash = rest.indexOf('/');
        if (slash === -1) children.add(rest);
        else children.add(rest.slice(0, slash));
      }
    }
    return [...children].sort();
  }

  createDir(path: string): void {
    this.dirs.add(this.normalizeDir(path));
    this.ensureParents(this.normalizeDir(path));
  }

  dirExists(path: string): boolean {
    const dir = this.normalizeDir(path);
    if (this.dirs.has(dir)) return true;
    // A directory implicitly exists if any file lives under it
    for (const key of this.files.keys()) {
      if (key.startsWith(dir)) return true;
    }
    return false;
  }

  fileSize(path: string): number {
    const entry = this.files.get(this.normalize(path));
    if (entry === undefined) return 0;
    // UTF-16 length is close enough for the compiler's purposes
    return entry.content.length;
  }

  // ── Internal helpers ──────────────────────────────────────────────────────

  /** Normalise a file path: ensure leading slash, collapse . / .., unify separators. */
  private normalize(path: string): string {
    // Replace back-slashes with forward slashes
    const p = path.replace(/\\/g, '/');
    // Split and resolve . and ..
    const parts = p.split('/');
    const resolved: string[] = [];
    for (const part of parts) {
      if (part === '' || part === '.') continue;
      if (part === '..') {
        resolved.pop();
      } else {
        resolved.push(part);
      }
    }
    return '/' + resolved.join('/');
  }

  /** Like normalize but always ends with a trailing slash. */
  private normalizeDir(path: string): string {
    const n = this.normalize(path);
    return n.endsWith('/') ? n : n + '/';
  }

  private ensureParents(normalizedPath: string): void {
    const parts = normalizedPath.split('/').slice(1); // remove leading ''
    let current = '';
    // Walk every parent segment (not the file itself)
    for (let i = 0; i < parts.length - 1; i++) {
      current += '/' + parts[i];
      this.dirs.add(current + '/');
    }
  }
}
