#!/usr/bin/env python3
# Static dev server for koka wasi-web output that sends the COOP/COEP headers
# required for SharedArrayBuffer (i.e. `--wasithreads` builds). The headers
# cross-origin-ISOLATE the page: embedded cross-origin resources then need
# CORS/CORP, which is why threaded builds get this server instead of a plain
# `python3 -m http.server`. Non-threaded builds work under any static server.
#
# usage: python3 serve.py [port]   (default 8080; serves the script's dir)
import http.server, os, sys

class COIHandler(http.server.SimpleHTTPRequestHandler):
    def end_headers(self):
        self.send_header("Cross-Origin-Opener-Policy", "same-origin")
        self.send_header("Cross-Origin-Embedder-Policy", "require-corp")
        self.send_header("Cache-Control", "no-store")
        super().end_headers()

if __name__ == "__main__":
    port = int(sys.argv[1]) if len(sys.argv) > 1 else 8080
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    http.server.ThreadingHTTPServer.address_family_ipv6 = False
    with http.server.ThreadingHTTPServer(("", port), COIHandler) as srv:
        print(f"serving (cross-origin isolated) at http://localhost:{port}/")
        srv.serve_forever()
