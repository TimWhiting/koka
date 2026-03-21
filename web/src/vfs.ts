/**
 * vfs.ts
 *
 * In-memory Virtual File System for the Koka playground.
 * Installed as `globalThis.kokaVFS` so the compiled WASM/JS compiler can
 * read and write files without touching the real disk.
 *
 * Async stdlib fetching: when a .kki / /share/lib/ path is requested and not
 * already cached, the VFS fetches it from the configured stdlib base URL and
 * caches the result.
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
  private stdlibBaseUrl: string;
  /** In-flight fetch promises, keyed by normalised path */
  private pendingFetches: Map<string, Promise<string | null>> = new Map();

  constructor(stdlibBaseUrl: string = '/stdlib') {
    this.stdlibBaseUrl = stdlibBaseUrl;
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

  /** Return every file written by the compiler (those written via writeFile). */
  getWrittenFiles(): Map<string, string> {
    const out = new Map<string, string>();
    for (const [k, v] of this.files) {
      out.set(k, v.content);
    }
    return out;
  }

  /** Install this VFS as globalThis.kokaVFS. */
  install(): void {
    const vfs: KokaVFSGlobal = {
      readFile:   (p) => this.readFile(p),
      fileExists: (p) => this.fileExists(p),
      fileTime:   (p) => this.fileTime(p),
      writeFile:  (p, c) => this.writeFile(p, c),
      listDir:    (p) => this.listDir(p),
      createDir:  (p) => this.createDir(p),
      dirExists:  (p) => this.dirExists(p),
      fileSize:   (p) => this.fileSize(p),
      removeFile: (p) => this.removeFile(p),
    };
    (globalThis as Record<string, unknown>)['kokaVFS'] = vfs;
  }

  // ── VFS operations ────────────────────────────────────────────────────────

  /**
   * Read a file.
   * - Returns the cached string synchronously if available.
   * - Returns a Promise<string | null> when the file needs to be fetched from
   *   the stdlib server (async).
   * - Returns null when the file is not found and is not fetchable.
   */
  readFile(path: string): string | null | Promise<string | null> {
    const key = this.normalize(path);
    const entry = this.files.get(key);
    if (entry !== undefined) return entry.content;

    if (this.isStdlibPath(key)) {
      return this.fetchStdlib(key);
    }
    return null;
  }

  fileExists(path: string): boolean {
    return this.files.has(this.normalize(path));
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

  private isStdlibPath(normalizedPath: string): boolean {
    return (
      normalizedPath.startsWith('/share/lib/') ||
      normalizedPath.endsWith('.kki') ||
      normalizedPath.includes('/std/')
    );
  }

  private fetchStdlib(normalizedPath: string): Promise<string | null> {
    // Deduplicate concurrent requests for the same path
    const inflight = this.pendingFetches.get(normalizedPath);
    if (inflight !== undefined) return inflight;

    const promise = (async (): Promise<string | null> => {
      try {
        const url = this.stdlibBaseUrl + normalizedPath;
        const response = await fetch(url);
        if (!response.ok) return null;
        const content = await response.text();
        this.addFile(normalizedPath, content);
        return content;
      } catch {
        return null;
      } finally {
        this.pendingFetches.delete(normalizedPath);
      }
    })();

    this.pendingFetches.set(normalizedPath, promise);
    return promise;
  }
}
