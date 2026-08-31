#!/usr/bin/env python3
"""Static server for development, which does not let the browser keep anything.

`python3 -m http.server` sends `Last-Modified` and no `Cache-Control`, which
leaves the browser free to reuse a file without asking whether it changed. That
is fine until two files that have to agree are cached differently: an edit to
`index.html` and an edit to the module it loads land in the page at different
times, and the result is a version of the app that never existed -- a three
column table drawn by code that builds five.

The browser tests never see this, because a fresh context starts with an empty
cache; only a real session accumulates one.

Named `.mmb` files are served too, under `/open/<name>`, which is what makes
`npm start path/to/file.mmb` land in the explorer with that file open. They are
served by name from a table fixed at startup rather than by path, so this
serves exactly the files it was told to and nothing else -- the rest of the tree
is still the working directory, as before. Each request re-reads from disk, so
recompiling and pressing `r` in the page shows the new file.

Bound to localhost: it now reads files from outside the directory it serves.
"""

import argparse
import sys
import webbrowser
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import unquote

PREFIX = '/open/'

# url name -> file on disk, fixed at startup. Empty unless files were named.
SERVED: dict[str, Path] = {}


def serve_as(path: Path) -> str:
    """The name to serve `path` under.

    The name goes in the page's address (`#/peano.mmb`), which cannot hold a
    `/`, so it is the basename -- and two files can share one. A collision is
    numbered rather than resolved in favour of either, since neither is more
    the file than the other.
    """
    name = path.name
    if name not in SERVED:
        return name
    stem, dot, ext = name.partition('.')
    n = 2
    while f'{stem}-{n}{dot}{ext}' in SERVED:
        n += 1
    return f'{stem}-{n}{dot}{ext}'


class NoStore(SimpleHTTPRequestHandler):
    def end_headers(self):
        self.send_header('Cache-Control', 'no-store, must-revalidate')
        super().end_headers()

    def served_file(self) -> Path | None:
        """The file this request names, if it is a request for a served one."""
        path = self.path.split('?', 1)[0]
        if not path.startswith(PREFIX):
            return None
        return SERVED.get(unquote(path[len(PREFIX):]))

    def send_served(self, body: bool) -> None:
        """Send a served file, read fresh so a recompile is picked up."""
        path = self.served_file()
        if path is None:
            # A name that was never served, or one whose file has gone: both are
            # "not here", and the page falls back to its other ways in.
            self.send_error(404, 'not served')
            return
        try:
            data = path.read_bytes()
        except OSError as e:
            # Named but unreadable -- typically not compiled yet. Say which file
            # and why, because the page can only report what it is given.
            self.send_error(404, f'{path}: {e.strerror}')
            return
        self.send_response(200)
        self.send_header('Content-Type', 'application/octet-stream')
        self.send_header('Content-Length', str(len(data)))
        self.end_headers()
        if body:
            self.wfile.write(data)

    def do_GET(self) -> None:
        if self.path.split('?', 1)[0].startswith(PREFIX):
            self.send_served(True)
        else:
            super().do_GET()

    def do_HEAD(self) -> None:
        if self.path.split('?', 1)[0].startswith(PREFIX):
            self.send_served(False)
        else:
            super().do_HEAD()


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    ap.add_argument('files', nargs='*', type=Path,
                    help='.mmb files to serve under /open/, and open the first of')
    ap.add_argument('-p', '--port', type=int, default=8731)
    ap.add_argument('--open', action='store_true', dest='open_browser',
                    help='open the page in a browser')
    args = ap.parse_args()

    for f in args.files:
        # Resolved now, so the table is absolute paths and a later request
        # cannot be steered anywhere else by the name it asks for.
        SERVED[serve_as(f)] = f.resolve()

    url = f'http://localhost:{args.port}/'
    # `?served` tells the page that `/open/` is here, so it looks there for the
    # file the address names instead of asking for one that is not there on
    # every page it draws. The address itself names the file, and the page
    # already resolves what the address names, so opening at that file's own
    # declaration list needs nothing further on the client.
    first = next(iter(SERVED), None)
    if first is not None:
        url += f'?served#/{first}'
    # Flushed, because this is the only output until the server stops, and a
    # pipe would otherwise hold it all until then.
    print(f'serving on {url} (no-store)', flush=True)
    for name, path in SERVED.items():
        print(f'  /open/{name} -> {path}', flush=True)
        if not path.exists():
            print('    (not there yet -- compile it and press r in the page)',
                  file=sys.stderr, flush=True)
    if args.open_browser:
        webbrowser.open(url)
    ThreadingHTTPServer(('127.0.0.1', args.port), NoStore).serve_forever()


if __name__ == '__main__':
    main()
