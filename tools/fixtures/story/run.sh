#!/usr/bin/env bash
# A fragment citing a label the ledger does not have must fail.
set -u
T=$(mktemp -d); cp -r "$LEANARTICLES_HUB/papers/egf" "$T/egf"; chmod -R u+w "$T/egf"
printf '\n## S-egf-5 A fragment on nothing\n\nRests on `thm:nope`.\n' >> "$T/egf/STORY.md"
python3 "$LEANARTICLES_HUB/tools/story_lint.py" --paper "$T/egf"; s=$?
rm -rf "$T"; exit $s
