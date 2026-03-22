/**
 * module-runner.ts
 *
 * Loads and executes Koka-generated ES modules in the browser using blob URLs.
 *
 * Koka compiles to ES modules with relative imports like:
 *   import * as $std_core from './std_core.mjs'
 *
 * Since we can't serve these as actual files from the playground, we resolve
 * all imports by rewriting them to blob: URLs, processing modules in
 * topological order (dependencies before dependents).
 */

/** Map of filename (e.g. "std_core.mjs") to JS source text. */
export interface ModuleSet {
  [filename: string]: string;
}

/**
 * Load and execute Koka-generated ES modules.
 *
 * @param precompiledMjs  Standard library .mjs modules (Map of filename -> source)
 * @param generatedMjs    Freshly compiled .mjs modules (Map of filename -> source)
 * @param mainModuleName  Name of the entry module, without extension (e.g. "main")
 * @param onOutput        Callback for stdout lines
 * @param onError         Callback for stderr lines
 */
export async function runKokaModules(
  precompiledMjs: Map<string, string>,
  generatedMjs: Map<string, string>,
  mainModuleName: string,
  onOutput: (text: string) => void,
  onError: (text: string) => void,
): Promise<void> {
  // Combine all modules: precompiled std + freshly generated
  const allModules: ModuleSet = {};

  for (const [name, code] of precompiledMjs) {
    // Normalise to bare filename
    allModules[normalizeName(name)] = code;
  }

  for (const [path, code] of generatedMjs) {
    // path may be a full VFS path like /.koka/v3.2.4/.../main.mjs
    allModules[normalizeName(path)] = code;
  }

  const mainFilename = mainModuleName.endsWith('.mjs')
    ? mainModuleName
    : mainModuleName + '.mjs';

  if (!allModules[mainFilename]) {
    onError(`No module named "${mainFilename}" found in generated output.`);
    return;
  }

  // ── Resolve imports topologically via blob URLs ───────────────────────────
  //
  // Each module's source text contains lines like:
  //   import * as $std_core from './std_core.mjs'
  //
  // We rewrite those to blob: URLs once the dependency is resolved.

  const blobUrls: Record<string, string> = {};
  let remaining = Object.keys(allModules);
  const MAX_ROUNDS = 50;

  for (let round = 0; round < MAX_ROUNDS && remaining.length > 0; round++) {
    const nextRemaining: string[] = [];

    for (const name of remaining) {
      const code = allModules[name];
      let allResolved = true;

      const rewritten = code.replace(
        /from\s+['"]\.\/([^'"]+)['"]/g,
        (_match, importName: string) => {
          if (blobUrls[importName]) {
            return `from '${blobUrls[importName]}'`;
          } else if (allModules[importName] !== undefined) {
            // Dependency exists but not yet resolved — try next round
            allResolved = false;
            return _match;
          }
          // Unknown import — leave as-is (may fail at runtime)
          return _match;
        },
      );

      if (allResolved) {
        const blob = new Blob([rewritten], { type: 'application/javascript' });
        blobUrls[name] = URL.createObjectURL(blob);
      } else {
        nextRemaining.push(name);
      }
    }

    remaining = nextRemaining;
  }

  if (remaining.length > 0) {
    onOutput(`Warning: could not resolve all imports for: ${remaining.join(', ')}`);
  }

  if (!blobUrls[mainFilename]) {
    onError(`Could not create blob URL for main module — unresolved imports.`);
    // Clean up any URLs we did create
    for (const url of Object.values(blobUrls)) URL.revokeObjectURL(url);
    return;
  }

  // ── Patch console to capture output ──────────────────────────────────────
  const origLog   = console.log;
  const origError = console.error;
  const origWarn  = console.warn;

  console.log = (...args: unknown[]) => {
    origLog(...args);
    onOutput(args.map(String).join(' '));
  };
  console.error = (...args: unknown[]) => {
    origError(...args);
    onError(args.map(String).join(' '));
  };
  console.warn = (...args: unknown[]) => {
    origWarn(...args);
    onOutput('[warn] ' + args.map(String).join(' '));
  };

  try {
    onOutput('');
    onOutput('=== Output ===');
    onOutput(`Loading ${Object.keys(blobUrls).length} modules...`);
    const mod = await import(/* @vite-ignore */ blobUrls[mainFilename]);
    onOutput(`Module loaded. Exports: ${Object.keys(mod).join(', ')}`);
    if (typeof mod.main === 'function') {
      onOutput('Calling main()...');
      await mod.main();
      onOutput('main() returned.');
    } else {
      onOutput('No main() function found in module exports.');
    }
  } catch (e: unknown) {
    const msg = e instanceof Error ? e.message : String(e);
    onError('[runtime error] ' + msg);
    if (e instanceof Error && e.stack) {
      const shortStack = e.stack.split('\n').slice(0, 4).join('\n');
      onError(shortStack);
    }
  } finally {
    console.log   = origLog;
    console.error = origError;
    console.warn  = origWarn;
    for (const url of Object.values(blobUrls)) URL.revokeObjectURL(url);
  }
}

/** Extract the bare filename from a path or return as-is. */
function normalizeName(nameOrPath: string): string {
  const slash = nameOrPath.lastIndexOf('/');
  return slash === -1 ? nameOrPath : nameOrPath.slice(slash + 1);
}

/**
 * Load and execute Koka-generated ES modules.
 * Accepts plain ModuleSet objects (records) instead of Maps.
 *
 * @param precompiledMjs  Standard library .mjs modules (filename -> source)
 * @param generatedMjs    Freshly compiled .mjs modules (filename -> source)
 * @param mainModuleName  Filename of the entry module (e.g. "main.mjs")
 * @param onOutput        Callback for stdout lines
 * @param onError         Callback for stderr lines
 */
export async function runKokaProgram(
  precompiledMjs: ModuleSet,
  generatedMjs: ModuleSet,
  mainModuleName: string,
  onOutput: (text: string) => void,
  onError: (text: string) => void,
): Promise<void> {
  const precompiledMap = new Map<string, string>(Object.entries(precompiledMjs));
  const generatedMap   = new Map<string, string>(Object.entries(generatedMjs));
  // mainModuleName for runKokaModules should be without ".mjs" extension
  const mainName = mainModuleName.endsWith('.mjs')
    ? mainModuleName.slice(0, -4)
    : mainModuleName;
  return runKokaModules(precompiledMap, generatedMap, mainName, onOutput, onError);
}
