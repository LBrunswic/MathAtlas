#!/usr/bin/env bash
# A listed directory that exists WITHOUT the xattr must fail --check. The temp root must be
# under Dropbox for the gate to apply, so it lives in the hub's gitignored .selftest-tmp/.
set -u
T="$LEANARTICLES_HUB/.selftest-tmp/dropbox-ignore"; rm -rf "$T"; mkdir -p "$T/lean/.lake"
printf '[hub]\nname="x"\ncanonical_host="node1"\ndropbox_ignored=["lean/.lake"]\n' > "$T/hub.toml"
LEANARTICLES_ROOT="$T" python3 "$LEANARTICLES_HUB/tools/dropbox_ignore.py" --check; s=$?
rm -rf "$T"; exit $s
