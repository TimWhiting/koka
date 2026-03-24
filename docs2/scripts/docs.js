document.addEventListener("DOMContentLoaded", function () {
    function resetTooltipPosition(tooltip) {
        tooltip.style.left = "50%";
        tooltip.style.right = "auto";
        tooltip.style.top = "";
        tooltip.style.bottom = "120%";
        tooltip.style.transform = "translateX(-50%)";
    }

    function adjustTooltipPosition(host) {
        var tooltip = host.querySelector('.pc');
        if (!tooltip) return;

        resetTooltipPosition(tooltip);

        var margin = 8;
        var rect = tooltip.getBoundingClientRect();
        var offsetX = 0;

        if (rect.left < margin) {
            offsetX = margin - rect.left;
        } else if (rect.right > window.innerWidth - margin) {
            offsetX = (window.innerWidth - margin) - rect.right;
        }

        if (offsetX !== 0) {
            tooltip.style.transform = "translateX(calc(-50% + " + offsetX + "px))";
        }

        if (rect.top < margin) {
            tooltip.style.bottom = "auto";
            tooltip.style.top = "120%";
        }
    }

    // ---- Active page + tree expansion ----
    // Find all sidebar links and mark the one matching the current page
    var activeLink = null;
    var currentUrl = window.location.href.split('#')[0].split('?')[0];

    document.querySelectorAll('.sidebar a').forEach(function (a) {
        // a.href returns the absolute URL
        var linkUrl = a.href.split('#')[0].split('?')[0];
        if (linkUrl === currentUrl) {
            a.classList.add('active-page');
            activeLink = a;
        }
    });

    // Select all list items in the sidebar that have a nested unordered list
    var treeItems = document.querySelectorAll(".sidebar li:has(ul)");

    treeItems.forEach(function (item) {
        // Add a caret span before the text of the list item
        var anchor = item.querySelector("strong") || item.querySelector("a") || item.firstChild;
        if (anchor) {
            var caret = document.createElement("span");
            caret.classList.add("caret");
            item.insertBefore(caret, anchor);
        }

        // Check if this tree section contains the active link
        var containsActive = activeLink && item.contains(activeLink);

        if (containsActive) {
            // Expand sections that contain the current page
            item.classList.add("active");
        } else {
            // Collapse other sections by default
            item.classList.add("collapsed");
            var nestedList = item.querySelector("ul");
            if (nestedList) nestedList.classList.add("hidden");
        }

        // Toggle section when clicking the caret or the header text
        item.addEventListener("click", function (e) {
            // Only trigger if clicking the item itself or the caret/strong, 
            // but NOT if clicking inside the nested UL (to allow link navigation)
            var target = e.target;
            var isHeaderClick = target.classList.contains("caret") || 
                                target.tagName === "STRONG" || 
                                target === item;
            
            if (isHeaderClick) {
                e.preventDefault();
                e.stopPropagation();
                item.classList.toggle("active");
                item.classList.toggle("collapsed");
                var nestedList = item.querySelector("ul");
                if (nestedList) {
                    nestedList.classList.toggle("hidden");
                }
            }
        });
    });

    // Handle Mobile nav toggle button state
    var mobileToggle = document.querySelector('.mobile-nav-toggle');
    if (mobileToggle) {
        mobileToggle.addEventListener('click', function () {
            var sidebar = document.querySelector('.sidebar');
            var overlay = document.querySelector('.sidebar-overlay');
            if (sidebar) sidebar.classList.toggle('open');
            if (overlay) overlay.classList.toggle('open');
            document.body.classList.toggle('sidebar-open');
        });
    }

    // ---- Theme Switching ----
    var themeToggle = document.getElementById("theme-toggle");
    if (themeToggle) {
        var sunIcon = themeToggle.querySelector(".icon-sun");
        var moonIcon = themeToggle.querySelector(".icon-moon");

        function setTheme(theme, save) {
            document.documentElement.setAttribute("data-theme", theme);
            if (save !== false) {
              localStorage.setItem("theme", theme);
            }
            if (theme === "dark") {
                if (sunIcon) sunIcon.style.display = "none";
                if (moonIcon) moonIcon.style.display = "inline";
            } else {
                if (sunIcon) sunIcon.style.display = "inline";
                if (moonIcon) moonIcon.style.display = "none";
            }
        }

        // Initialize theme
        var savedTheme = localStorage.getItem("theme");
        var mediaQuery = window.matchMedia("(prefers-color-scheme: dark)");
        
        var initialTheme = savedTheme || (mediaQuery.matches ? "dark" : "light");
        setTheme(initialTheme, !!savedTheme);

        // Listen for system theme changes
        mediaQuery.addEventListener("change", function(e) {
            // Only follow system if user hasn't set a manual override
            if (!localStorage.getItem("theme")) {
                setTheme(e.matches ? "dark" : "light", false);
            }
        });

        themeToggle.addEventListener("click", function () {
            var currentTheme = document.documentElement.getAttribute("data-theme");
            setTheme(currentTheme === "dark" ? "light" : "dark", true);
        });
    }

    var sidebarOverlay = document.querySelector('.sidebar-overlay');
    if (sidebarOverlay) {
        sidebarOverlay.addEventListener('click', function () {
            var sidebar = document.querySelector('.sidebar');
            if (sidebar) sidebar.classList.remove('open');
            this.classList.remove('open');
            document.body.classList.remove('sidebar-open');
        });
    }

    document.querySelectorAll('.pp').forEach(function (host) {
        host.addEventListener('mouseenter', function () {
            requestAnimationFrame(function () {
                adjustTooltipPosition(host);
            });
        });
        host.addEventListener('focusin', function () {
            requestAnimationFrame(function () {
                adjustTooltipPosition(host);
            });
        });
    });

    window.addEventListener('resize', function () {
        document.querySelectorAll('.pp:hover').forEach(function (host) {
            adjustTooltipPosition(host);
        });
    });

    // ---- Reveal page after setup (prevents theme/sidebar flash) ----
    document.body.classList.add('ready');
    var bodyDiv = document.querySelector('.madoko div.body');
    if (bodyDiv) bodyDiv.classList.add('ready');

    // ---- Prefetch adjacent pages for instant navigation ----
    var prefetched = {};
    document.querySelectorAll('.sidebar a, a.learn').forEach(function(a) {
        var href = a.getAttribute('href');
        if (!href || href.startsWith('#') || href.startsWith('http') || href.startsWith('mailto')) return;
        // Resolve to absolute URL
        var url = a.href.split('#')[0].split('?')[0];
        if (prefetched[url]) return;
        prefetched[url] = true;
        var link = document.createElement('link');
        link.rel = 'prefetch';
        link.href = url;
        document.head.appendChild(link);
    });
});
