#!/usr/bin/env bash
# Twelve consecutive words pasted from the legacy abstract must fail.
set -u
T=$(mktemp -d); cp -r "$LEANARTICLES_HUB/papers/egf" "$T/egf"; chmod -R u+w "$T/egf"
printf '\nPasted: Generative Flow Networks (GFNs) were initially introduced on directed acyclic graphs to sample from an unnormalized distribution density.\n' >> "$T/egf/STORY.md"
python3 "$LEANARTICLES_HUB/tools/no_legacy_prose.py" --paper "$T/egf"; s=$?
rm -rf "$T"; exit $s
