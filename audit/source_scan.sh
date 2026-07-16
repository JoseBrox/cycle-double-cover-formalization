#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
pattern='\b(sorry|admit|axiom|native_decide|opaque|unsafe|implemented_by)\b|\bexact\?'
if grep -R -nE "$pattern" RequestProject CycleDoubleCover.lean; then
  echo 'Forbidden proof mechanism found.' >&2
  exit 1
fi
printf '%s\n' 'Source scan passed: no forbidden proof placeholders or proof-producing escape hatches found.'
