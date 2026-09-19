#!/usr/bin/env bash
# A lakefile require with no DEPS.md row must fail.
set -u
T=$(mktemp -d); mkdir -p "$T/lean" "$T/registers"; cp "$LEANARTICLES_HUB/registers/DEPS.md" "$T/registers/"
printf '[[require]]\nname = "mathlib"\n[[require]]\nname = "unregistered_lib"\n' > "$T/lean/lakefile.toml"
LEANARTICLES_ROOT="$T" python3 "$LEANARTICLES_HUB/tools/deps_register.py"; s=$?
rm -rf "$T"; exit $s
