#!/usr/bin/env python3
"""`make check` runs on the canonical host only.

    python3 tools/host_guard.py   # exit 0 on hub.toml's canonical_host, 1 elsewhere

The laptop edits through Dropbox and never runs lake or the gates; a green `make check` from
a host whose Lean build is absent or different would certify nothing. The hostname is read
from the kernel (`socket.gethostname`), with the environment variable `LEANARTICLES_HOSTNAME`
as the override the selftest fixture uses to make this gate fail on purpose.
"""
import os
import socket
import sys
import tomllib

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def main():
    with open(os.path.join(ROOT, "hub.toml"), "rb") as fh:
        want = tomllib.load(fh)["hub"]["canonical_host"]
    have = os.environ.get("LEANARTICLES_HOSTNAME") or socket.gethostname()
    if have != want:
        print("host_guard: FAIL this is %r; the gates run on %r only" % (have, want))
        return 1
    print("host_guard: %s" % have)
    return 0


if __name__ == "__main__":
    sys.exit(main())
