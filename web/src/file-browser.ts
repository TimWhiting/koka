/**
 * file-browser.ts
 *
 * A collapsible file browser sidebar for the Koka playground.
 * Supports lazy-loading directory contents and nested tree rendering.
 */

export interface FileEntry {
  name: string;
  path: string;
  type: 'file' | 'directory';
  children?: FileEntry[];
  /** Optional raw download URL (e.g. from GitHub API) */
  download_url?: string;
  /** If true, children need to be fetched on expand */
  lazyLoad?: boolean;
  /** File content if available (e.g. from VFS) */
  content?: string;
}

export interface FileBrowserConfig {
  /** Called when the user clicks a .kk file */
  onFileSelect: (path: string, content: string, name: string) => void;
  /** Called when the user clicks a .mjs/.js file (shows in JS output pane) */
  onJsFileSelect?: (path: string, content: string, name: string) => void;
  /** Called to lazily load directory children (e.g. from GitHub API) */
  onDirectoryExpand?: (entry: FileEntry) => Promise<FileEntry[]>;
}

interface Section {
  title: string;
  entries: FileEntry[];
  collapsed: boolean;
}

export class FileBrowser {
  private container: HTMLElement;
  private config: FileBrowserConfig;
  private sections: Map<string, Section> = new Map();
  /** Track which paths are expanded so they survive re-renders */
  private expandedPaths: Set<string> = new Set();
  /** Track per-section DOM elements for targeted updates */
  private sectionElements: Map<string, HTMLElement> = new Map();

  constructor(container: HTMLElement, config: FileBrowserConfig) {
    this.container = container;
    this.config = config;
    this.container.classList.add('file-browser');
  }

  addSection(title: string, entries: FileEntry[]): void {
    this.sections.set(title, { title, entries, collapsed: false });
    this.renderSection(title);
  }

  updateSection(title: string, entries: FileEntry[]): void {
    const existing = this.sections.get(title);
    if (existing) {
      existing.entries = entries;
    } else {
      this.sections.set(title, { title, entries, collapsed: false });
    }
    this.renderSection(title);
  }

  /** Re-render only one section, preserving others */
  private renderSection(title: string): void {
    const section = this.sections.get(title);
    if (!section) return;

    const newEl = this.buildSectionElement(section);

    const existingEl = this.sectionElements.get(title);
    if (existingEl && existingEl.parentNode) {
      existingEl.parentNode.replaceChild(newEl, existingEl);
    } else {
      this.container.appendChild(newEl);
    }
    this.sectionElements.set(title, newEl);
  }

  render(): void {
    this.container.innerHTML = '';
    this.sectionElements.clear();
    for (const section of this.sections.values()) {
      const el = this.buildSectionElement(section);
      this.container.appendChild(el);
      this.sectionElements.set(section.title, el);
    }
  }

  private buildSectionElement(section: Section): HTMLElement {
      const sectionEl = document.createElement('div');
      sectionEl.className = 'fb-section';

      const headerEl = document.createElement('div');
      headerEl.className = 'fb-section-header';
      headerEl.setAttribute('role', 'button');

      const arrow = document.createElement('span');
      arrow.className = 'fb-arrow';
      arrow.textContent = section.collapsed ? '▸' : '▾';

      const titleEl = document.createElement('span');
      titleEl.className = 'fb-section-title';
      titleEl.textContent = section.title;

      headerEl.appendChild(arrow);
      headerEl.appendChild(titleEl);

      const bodyEl = document.createElement('div');
      bodyEl.className = 'fb-section-body';
      if (section.collapsed) bodyEl.style.display = 'none';

      headerEl.addEventListener('click', () => {
        section.collapsed = !section.collapsed;
        arrow.textContent = section.collapsed ? '▸' : '▾';
        bodyEl.style.display = section.collapsed ? 'none' : '';
      });

      sectionEl.appendChild(headerEl);

      if (section.entries.length === 0) {
        const empty = document.createElement('div');
        empty.className = 'fb-empty';
        empty.textContent = '(empty)';
        bodyEl.appendChild(empty);
      } else {
        for (const entry of section.entries) {
          bodyEl.appendChild(this.renderEntry(entry, 0));
        }
      }

      sectionEl.appendChild(bodyEl);
      return sectionEl;
  }

  private renderEntry(entry: FileEntry, depth: number): HTMLElement {
    const wrapper = document.createElement('div');

    const item = document.createElement('div');
    item.className = 'fb-item';
    item.style.paddingLeft = `${8 + depth * 14}px`;
    item.setAttribute('title', entry.path);

    const icon = document.createElement('span');
    icon.className = 'fb-item-icon';

    const nameEl = document.createElement('span');
    nameEl.className = 'fb-item-name';
    nameEl.textContent = entry.name;

    item.appendChild(icon);
    item.appendChild(nameEl);
    wrapper.appendChild(item);

    if (entry.type === 'directory') {
      icon.textContent = '📁';
      item.classList.add('fb-item-dir');

      const childrenContainer = document.createElement('div');
      let expanded = this.expandedPaths.has(entry.path);
      childrenContainer.style.display = expanded ? '' : 'none';
      icon.textContent = expanded ? '📂' : '📁';
      let loaded = !!entry.children;

      // Pre-render children if available
      if (entry.children) {
        for (const child of entry.children) {
          childrenContainer.appendChild(this.renderEntry(child, depth + 1));
        }
      }

      item.addEventListener('click', async (e) => {
        e.stopPropagation();
        expanded = !expanded;
        if (expanded) this.expandedPaths.add(entry.path);
        else this.expandedPaths.delete(entry.path);
        icon.textContent = expanded ? '📂' : '📁';
        childrenContainer.style.display = expanded ? '' : 'none';

        // Lazy load on first expand
        if (expanded && !loaded && this.config.onDirectoryExpand) {
          const loadingEl = document.createElement('div');
          loadingEl.className = 'fb-empty';
          loadingEl.textContent = 'Loading...';
          childrenContainer.appendChild(loadingEl);

          try {
            const children = await this.config.onDirectoryExpand(entry);
            entry.children = children;
            loaded = true;
            childrenContainer.innerHTML = '';
            for (const child of children) {
              childrenContainer.appendChild(this.renderEntry(child, depth + 1));
            }
          } catch {
            childrenContainer.innerHTML = '';
            const errEl = document.createElement('div');
            errEl.className = 'fb-empty';
            errEl.textContent = '(failed to load)';
            childrenContainer.appendChild(errEl);
          }
        }
      });

      wrapper.appendChild(childrenContainer);
    } else {
      // File
      const isJs = entry.name.endsWith('.mjs') || entry.name.endsWith('.js');
      const isKk = entry.name.endsWith('.kk') || entry.name.endsWith('.kki');
      icon.textContent = isJs ? '🟨' : isKk ? '📄' : '📄';
      item.classList.add('fb-item-clickable');

      item.addEventListener('click', () => {
        if (entry.download_url) {
          fetch(entry.download_url)
            .then((r) => r.text())
            .then((content) => {
              if (isJs && this.config.onJsFileSelect) {
                this.config.onJsFileSelect(entry.path, content, entry.name);
              } else {
                this.config.onFileSelect(entry.path, content, entry.name);
              }
            })
            .catch(() => {
              this.config.onFileSelect(entry.path, `// Could not load ${entry.name}`, entry.name);
            });
        } else {
          // VFS file — content is available directly
          if (isJs && this.config.onJsFileSelect) {
            this.config.onJsFileSelect(entry.path, entry.content ?? '', entry.name);
          } else {
            this.config.onFileSelect(entry.path, entry.content ?? '', entry.name);
          }
        }
      });
    }

    return wrapper;
  }
}

/** Build a tree structure from flat VFS paths */
export function buildFileTree(files: Map<string, string>, filter?: (path: string) => boolean): FileEntry[] {
  const root: FileEntry = { name: '', path: '', type: 'directory', children: [] };

  for (const [path, content] of files) {
    if (filter && !filter(path)) continue;

    const parts = path.split('/').filter(Boolean);
    let current = root;

    for (let i = 0; i < parts.length; i++) {
      const part = parts[i];
      const isLast = i === parts.length - 1;

      if (isLast) {
        current.children!.push({
          name: part,
          path: path,
          type: 'file',
          content: content,
        } as FileEntry & { content: string });
      } else {
        let dir = current.children!.find(
          (c) => c.type === 'directory' && c.name === part,
        );
        if (!dir) {
          dir = { name: part, path: parts.slice(0, i + 1).join('/'), type: 'directory', children: [] };
          current.children!.push(dir);
        }
        current = dir;
      }
    }
  }

  // Sort: directories first, then alphabetical
  function sortTree(entries: FileEntry[]): void {
    entries.sort((a, b) => {
      if (a.type !== b.type) return a.type === 'directory' ? -1 : 1;
      return a.name.localeCompare(b.name);
    });
    for (const e of entries) {
      if (e.children) sortTree(e.children);
    }
  }

  sortTree(root.children!);
  return root.children!;
}
