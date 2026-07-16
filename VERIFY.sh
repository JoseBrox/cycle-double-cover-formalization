#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT"
sha256sum -c SHA256SUMS
./audit/source_scan.sh
python3 ./audit/finite_algebra_check.py
lake build
lake env lean RequestProject/Audit.lean
