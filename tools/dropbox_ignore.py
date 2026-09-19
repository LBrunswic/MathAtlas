#!/usr/bin/env python3
"""Keep the Lean build out of Dropbox.

    python3 tools/dropbox_ignore.py          # create each listed dir if absent and set the xattr
    python3 tools/dropbox_ignore.py --check  # exit 1 if a listed dir exists without the xattr

The directories come from `hub.toml` `[hub].dropbox_ignored`. Dropbox honours the extended
attribute `user.com.dropbox.ignored = 1` on Linux; node1 has no `setfattr`, so this uses
`os.setxattr`. Run it BEFORE the first `lake build`: Dropbox picks up a fresh directory within
seconds, and an 8 GB `.lake` that starts syncing is hard to stop. Exit 2 if the repository is
not under a Dropbox folder at all (then there is nothing to ignore, and saying so is the point).
"""
import os
import sys
import tomllib

ROOT = os.environ.get("LEANARTICLES_ROOT") or os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ATTR = "user.com.dropbox.ignored"


def main():
    check = "--check" in sys.argv
    with open(os.path.join(ROOT, "hub.toml"), "rb") as fh:
        dirs = tomllib.load(fh)["hub"]["dropbox_ignored"]
    if "/Dropbox/" not in os.path.realpath(ROOT) + "/":
        print("dropbox_ignore: %s is not under a Dropbox folder" % ROOT)
        return 2
    bad = 0
    for d in dirs:
        p = os.path.join(ROOT, d)
        if not os.path.isdir(p):
            if check:
                print("dropbox_ignore: %s does not exist yet (fine; set on creation)" % d)
                continue
            os.makedirs(p, exist_ok=True)
        try:
            val = os.getxattr(p, ATTR)
        except OSError:
            val = None
        if val == b"1":
            print("dropbox_ignore: %s ignored" % d)
            continue
        if check:
            print("dropbox_ignore: FAIL %s exists without %s=1" % (d, ATTR))
            bad += 1
            continue
        os.setxattr(p, ATTR, b"1")
        print("dropbox_ignore: set %s on %s" % (ATTR, d))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
