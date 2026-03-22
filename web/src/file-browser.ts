/**
 * file-browser.ts
 *
 * A collapsible file browser sidebar for the Koka playground.
 * Renders three sections: Samples, Open Files, and VFS (debug).
 */

export interface FileEntry {
  name: string;
  path: string;
  type: 'file' | 'directory';
  children?: FileEntry[];
  /** Optional raw download URL (e.g. from GitHub API) */
  download_url?: string;
}

export interface FileBrowserConfig {
  /** Called when the user clicks a file entry */
  onFileSelect: (path: string, content: string, name: string) => void;
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

  constructor(container: HTMLElement, config: FileBrowserConfig) {
    this.container = container;
    this.config = config;
    this.container.classList.add('file-browser');
  }

  /** Add a new named section. */
  addSection(title: string, entries: FileEntry[]): void {
    this.sections.set(title, { title, entries, collapsed: false });
    this.render();
  }

  /** Replace entries in an existing section (creates it if absent). */
  updateSection(title: string, entries: FileEntry[]): void {
    const existing = this.sections.get(title);
    if (existing) {
      existing.entries = entries;
    } else {
      this.sections.set(title, { title, entries, collapsed: false });
    }
    this.render();
  }

  /** Re-render the entire file browser. */
  render(): void {
    this.container.innerHTML = '';

    for (const section of this.sections.values()) {
      const sectionEl = document.createElement('div');
      sectionEl.className = 'fb-section';

      // Section header
      const headerEl = document.createElement('div');
      headerEl.className = 'fb-section-header';
      headerEl.setAttribute('role', 'button');
      headerEl.setAttribute('tabindex', '0');
      headerEl.setAttribute('aria-expanded', String(!section.collapsed));

      const arrow = document.createElement('span');
      arrow.className = 'fb-arrow';
      arrow.textContent = section.collapsed ? '▸' : '▾';

      const titleEl = document.createElement('span');
      titleEl.className = 'fb-section-title';
      titleEl.textContent = section.title;

      headerEl.appendChild(arrow);
      headerEl.appendChild(titleEl);

      const toggleCollapse = (): void => {
        section.collapsed = !section.collapsed;
        arrow.textContent = section.collapsed ? '▸' : '▾';
        headerEl.setAttribute('aria-expanded', String(!section.collapsed));
        bodyEl.style.display = section.collapsed ? 'none' : '';
      };

      headerEl.addEventListener('click', toggleCollapse);
      headerEl.addEventListener('keydown', (e: KeyboardEvent) => {
        if (e.key === 'Enter' || e.key === ' ') { e.preventDefault(); toggleCollapse(); }
      });

      sectionEl.appendChild(headerEl);

      // Section body (tree)
      const bodyEl = document.createElement('div');
      bodyEl.className = 'fb-section-body';
      if (section.collapsed) bodyEl.style.display = 'none';

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
      this.container.appendChild(sectionEl);
    }
  }

  private renderEntry(entry: FileEntry, depth: number): HTMLElement {
    const item = document.createElement('div');
    item.className = 'fb-item';
    item.style.paddingLeft = `${8 + depth * 14}px`;
    item.setAttribute('title', entry.path);

    const icon = document.createElement('span');
    icon.className = 'fb-item-icon';

    if (entry.type === 'directory') {
      icon.textContent = '📁';
      item.classList.add('fb-item-dir');
    } else {
      icon.textContent = '📄';
      item.classList.add('fb-item-file');
    }

    const nameEl = document.createElement('span');
    nameEl.className = 'fb-item-name';
    nameEl.textContent = entry.name;

    item.appendChild(icon);
    item.appendChild(nameEl);

    if (entry.type === 'directory' && entry.children) {
      let open = false;
      const childrenContainer = document.createElement('div');
      childrenContainer.className = 'fb-children';
      childrenContainer.style.display = 'none';

      item.addEventListener('click', (e: MouseEvent) => {
        e.stopPropagation();
        open = !open;
        icon.textContent = open ? '📂' : '📁';
        childrenContainer.style.display = open ? '' : 'none';
      });

      for (const child of entry.children) {
        childrenContainer.appendChild(this.renderEntry(child, depth + 1));
      }

      // Wrap item and children together
      const wrapper = document.createElement('div');
      wrapper.appendChild(item);
      wrapper.appendChild(childrenContainer);
      return wrapper;
    } else if (entry.type === 'file') {
      item.setAttribute('role', 'button');
      item.setAttribute('tabindex', '0');
      item.classList.add('fb-item-clickable');

      const handleSelect = (): void => {
        if (entry.download_url) {
          // Fetch the file content from GitHub
          fetch(entry.download_url)
            .then((r) => r.text())
            .then((content) => { this.config.onFileSelect(entry.path, content, entry.name); })
            .catch(() => { this.config.onFileSelect(entry.path, `// Could not load ${entry.name}`, entry.name); });
        } else {
          // For VFS / open files, content is stored in path for now
          this.config.onFileSelect(entry.path, '', entry.name);
        }
      };

      item.addEventListener('click', handleSelect);
      item.addEventListener('keydown', (e: KeyboardEvent) => {
        if (e.key === 'Enter' || e.key === ' ') { e.preventDefault(); handleSelect(); }
      });
    }

    return item;
  }
}
