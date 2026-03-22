/**
 * github-integration.ts
 *
 * Utilities for fetching Koka samples from GitHub and saving/loading Gists.
 */

import type { FileEntry } from './file-browser';

export type { FileEntry };

export interface GistFile {
  filename: string;
  content: string;
  language?: string;
}

/**
 * Fetch the contents of a directory from a GitHub repository via the REST API.
 *
 * @param owner  Repository owner (e.g. 'koka-lang')
 * @param repo   Repository name (e.g. 'koka')
 * @param path   Path within the repository (e.g. 'samples')
 * @param ref    Git ref (branch/tag/commit); defaults to 'dev'
 */
export async function fetchGitHubDirectory(
  owner: string,
  repo: string,
  path: string,
  ref?: string,
): Promise<FileEntry[]> {
  const url = `https://api.github.com/repos/${owner}/${repo}/contents/${path}?ref=${ref ?? 'dev'}`;
  const resp = await fetch(url);
  if (!resp.ok) throw new Error(`GitHub API error ${resp.status} for ${url}`);
  const items = await resp.json() as Array<{
    name: string; path: string; type: string; download_url: string | null;
  }>;
  return items.map((item) => ({
    name: item.name,
    path: item.path,
    type: item.type === 'dir' ? 'directory' : 'file',
    download_url: item.download_url ?? undefined,
  }));
}

/**
 * Fetch the raw text of a single file from GitHub.
 *
 * @param owner  Repository owner
 * @param repo   Repository name
 * @param path   File path within the repository
 * @param ref    Git ref; defaults to 'dev'
 */
export async function fetchGitHubFile(
  owner: string,
  repo: string,
  path: string,
  ref?: string,
): Promise<string> {
  const url = `https://raw.githubusercontent.com/${owner}/${repo}/${ref ?? 'dev'}/${path}`;
  const resp = await fetch(url);
  if (!resp.ok) throw new Error(`GitHub fetch error ${resp.status} for ${url}`);
  return resp.text();
}

/**
 * Load the top-level sample directories from koka-lang/koka.
 * Each entry is a directory; expand lazily when the user clicks.
 */
export async function loadKokaSamples(): Promise<FileEntry[]> {
  return fetchGitHubDirectory('koka-lang', 'koka', 'samples');
}

/**
 * Save files to a GitHub Gist and return the Gist HTML URL.
 *
 * @param files        Map of filename -> content
 * @param description  Gist description
 * @param token        Optional GitHub personal access token for authenticated requests
 */
export async function saveToGist(
  files: Record<string, string>,
  description: string,
  token?: string,
): Promise<string> {
  const gistFiles: Record<string, { content: string }> = {};
  for (const [name, content] of Object.entries(files)) {
    gistFiles[name] = { content };
  }

  const resp = await fetch('https://api.github.com/gists', {
    method: 'POST',
    headers: {
      'Content-Type': 'application/json',
      ...(token ? { Authorization: `token ${token}` } : {}),
    },
    body: JSON.stringify({
      description,
      public: true,
      files: gistFiles,
    }),
  });

  if (!resp.ok) throw new Error(`Gist save failed: ${resp.status}`);
  const gist = await resp.json() as { html_url: string };
  return gist.html_url;
}

/**
 * Load all files from a GitHub Gist.
 *
 * @param gistId  The Gist ID (last path segment of the Gist URL)
 */
export async function loadFromGist(gistId: string): Promise<Record<string, string>> {
  const resp = await fetch(`https://api.github.com/gists/${gistId}`);
  if (!resp.ok) throw new Error(`Gist load failed: ${resp.status}`);
  const gist = await resp.json() as {
    files: Record<string, { content: string }>;
  };
  const result: Record<string, string> = {};
  for (const [name, file] of Object.entries(gist.files)) {
    result[name] = file.content;
  }
  return result;
}
