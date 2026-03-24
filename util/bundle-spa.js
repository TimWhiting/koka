#!/usr/bin/env node
//
// Post-process Madoko HTML output into a single-page application.
//
// Usage: node util/bundle-spa.js [outdir]
//
// Reads all .html files from outdir (default: "out"), extracts the
// content div from each, and produces a single spa.html that uses
// hash-based routing to swap content without page reloads.
// Works on both file:// and http:// protocols.
//

const fs = require("fs");
const path = require("path");

const outDir = process.argv[2] || "out";

// Collect all HTML files recursively
function collectHtmlFiles(dir, base) {
  let results = [];
  for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
    if (entry.name === "gen" || entry.name.startsWith(".")) continue;
    const full = path.join(dir, entry.name);
    const rel = path.join(base, entry.name);
    if (entry.isDirectory()) {
      results = results.concat(collectHtmlFiles(full, rel));
    } else if (entry.name.endsWith(".html") && entry.name !== "404.html" && entry.name !== "spa.html") {
      results.push({ fullPath: full, route: rel.replace(/\\/g, "/") });
    }
  }
  return results;
}

// Extract content between <div class="content" ...> and its closing </div>
function extractContent(html) {
  const startMatch = html.match(/<div\s+class="content"[^>]*>/);
  if (!startMatch) return null;
  const startIdx = startMatch.index + startMatch[0].length;

  let depth = 1;
  let i = startIdx;
  while (i < html.length && depth > 0) {
    const nextOpen = html.indexOf("<div", i);
    const nextClose = html.indexOf("</div>", i);
    if (nextClose === -1) break;
    if (nextOpen !== -1 && nextOpen < nextClose) {
      depth++;
      i = nextOpen + 4;
    } else {
      depth--;
      if (depth === 0) return html.substring(startIdx, nextClose);
      i = nextClose + 6;
    }
  }
  return null;
}

function extractTitle(html) {
  const match = html.match(/<title>([^<]*)<\/title>/);
  return match ? match[1] : "Koka";
}

console.log("Bundling SPA from", outDir);

const files = collectHtmlFiles(outDir, "");
console.log(`Found ${files.length} HTML files`);

// Use index.html as the shell template
const shellPath = path.join(outDir, "index.html");
const shellHtml = fs.readFileSync(shellPath, "utf8");

// Extract all content fragments, keyed by their file path
const routes = {};
for (const file of files) {
  const html = fs.readFileSync(file.fullPath, "utf8");
  const content = extractContent(html);
  const title = extractTitle(html);
  if (content) {
    // Key is the file path as-is: "index.html", "learn/basics.html", etc.
    routes[file.route] = { title, content };
  } else {
    console.warn(`  Warning: could not extract content from ${file.route}`);
  }
}

const routeData = JSON.stringify(routes);

const spaScript = `
<script>
(function() {
  var routes = ${routeData};
  var contentEl = document.querySelector('.content');
  var currentRoute = null;
  var useHistory = (location.protocol !== 'file:');
  // Detect base path for pushState (e.g., "/docs/" if served from a subdirectory)
  var basePath = '';
  if (useHistory) {
    // The SPA file's path is the base
    basePath = location.pathname.replace(/[^\\/]+$/, '');
  }

  // Convert a relative href from any page context to a route key
  // e.g., from "learn/basics.html", href="../tutorial/effects.html" -> "tutorial/effects.html"
  function resolveHref(href, fromRoute) {
    if (!fromRoute) fromRoute = 'index.html';
    // Get directory of the current route
    var dir = fromRoute.replace(/[^\\/]+$/, '');
    // Resolve relative path
    var parts = (dir + href).split('/');
    var resolved = [];
    for (var i = 0; i < parts.length; i++) {
      if (parts[i] === '..') resolved.pop();
      else if (parts[i] !== '.' && parts[i] !== '') resolved.push(parts[i]);
    }
    return resolved.join('/');
  }

  function navigate(route, pushState) {
    if (route === currentRoute) return;
    var data = routes[route];
    if (!data) {
      // Try index.html for directory routes
      if (!route.endsWith('.html')) {
        data = routes[route + '/index.html'] || routes[route + 'index.html'];
      }
    }
    if (!data) return; // unknown route, ignore

    currentRoute = route;
    contentEl.innerHTML = data.content;
    document.title = data.title;

    if (pushState) {
      if (useHistory) {
        history.pushState({ route: route }, data.title, basePath + route);
      } else {
        location.hash = '#/' + route;
      }
    }

    // Update active page in sidebar
    document.querySelectorAll('.sidebar a.active-page').forEach(function(a) {
      a.classList.remove('active-page');
    });
    document.querySelectorAll('.sidebar a').forEach(function(a) {
      var href = a.getAttribute('href');
      if (!href || href.startsWith('http') || href.startsWith('#')) return;
      var resolved = resolveHref(href, getSidebarContext());
      if (resolved === route) a.classList.add('active-page');
    });

    window.scrollTo(0, 0);
    initTooltips();
  }

  // The sidebar links are relative to the shell page (index.html at root)
  function getSidebarContext() {
    return 'index.html';
  }

  function initTooltips() {
    contentEl.querySelectorAll('.pp').forEach(function(host) {
      host.addEventListener('mouseenter', function() {
        requestAnimationFrame(function() {
          var tooltip = host.querySelector('.pc');
          if (!tooltip) return;
          tooltip.style.left = "50%";
          tooltip.style.right = "auto";
          tooltip.style.top = "";
          tooltip.style.bottom = "120%";
          tooltip.style.transform = "translateX(-50%)";
          var rect = tooltip.getBoundingClientRect();
          var offsetX = 0;
          if (rect.left < 8) offsetX = 8 - rect.left;
          else if (rect.right > window.innerWidth - 8) offsetX = (window.innerWidth - 8) - rect.right;
          if (offsetX !== 0) tooltip.style.transform = "translateX(calc(-50% + " + offsetX + "px))";
          if (rect.top < 8) { tooltip.style.bottom = "auto"; tooltip.style.top = "120%"; }
        });
      });
    });
  }

  // Intercept clicks on internal links
  document.addEventListener('click', function(e) {
    var target = e.target.closest('a');
    if (!target) return;
    var href = target.getAttribute('href');
    if (!href) return;
    if (href.startsWith('http') || href.startsWith('mailto:') || href.startsWith('javascript:')) return;
    if (href.startsWith('#') && !href.startsWith('#/')) return; // in-page anchor
    if (target.getAttribute('target')) return;

    e.preventDefault();

    // Is this link in the sidebar (root-relative) or in the content (relative to current route)?
    var inSidebar = !!target.closest('.sidebar');
    var context = inSidebar ? 'index.html' : currentRoute;
    var resolved = resolveHref(href, context);
    navigate(resolved, true);
  });

  // Handle back/forward
  if (useHistory) {
    window.addEventListener('popstate', function(e) {
      var route = (e.state && e.state.route) ? e.state.route : 'index.html';
      navigate(route, false);
    });
  } else {
    window.addEventListener('hashchange', function() {
      var hash = location.hash;
      if (hash.startsWith('#/')) {
        navigate(hash.substring(2), false);
      }
    });
  }

  // Initial navigation
  if (useHistory) {
    var initPath = location.pathname.substring(basePath.length);
    if (!initPath || initPath === 'spa.html' || initPath === 'index.html') {
      currentRoute = 'index.html';
      history.replaceState({ route: currentRoute }, document.title);
    } else {
      navigate(initPath, false);
      if (currentRoute) history.replaceState({ route: currentRoute }, document.title);
    }
  } else {
    var initialHash = location.hash;
    if (initialHash.startsWith('#/')) {
      navigate(initialHash.substring(2), false);
    } else {
      currentRoute = 'index.html';
    }
  }
})();
</script>
`;

// Inject the SPA script before </body>
const spaHtml = shellHtml.replace("</body>", spaScript + "\n</body>");

const spaPath = path.join(outDir, "spa.html");
fs.writeFileSync(spaPath, spaHtml, "utf8");
console.log(`Written SPA to ${spaPath} (${(Buffer.byteLength(spaHtml) / 1024 / 1024).toFixed(1)}MB)`);
console.log(`Routes: ${Object.keys(routes).length}`);
