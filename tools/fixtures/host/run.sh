#!/usr/bin/env bash
# The gate must refuse a host that is not the canonical one.
LEANARTICLES_HOSTNAME=hyperlolipop python3 "$LEANARTICLES_HUB/tools/host_guard.py"
