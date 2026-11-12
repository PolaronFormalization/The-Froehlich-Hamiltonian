#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

# In a fresh clone, run 'lake exe cache get' first.
# Builds the public Lean library, including the three targets and their proof dependencies.
lake build GW
lake build GW.All

# Reject extra axioms in the transitive closure of the three public target theorems.
LOG="$(mktemp)"
trap 'rm -f "$LOG"' EXIT
lake env lean verification/CheckAxioms.lean | tee "$LOG"
python3 - "$LOG" <<'PY'
from pathlib import Path
import re,sys
s=Path(sys.argv[1]).read_text()
allowed={'propext','Classical.choice','Quot.sound'}
for target in ['GW.Main.construction','GW.Main.domain','GW.Main.regularity']:
    pat=re.escape("'"+target+"' depends on axioms: ")+r'\[([^]]*)\]'
    m=re.search(pat,s)
    if not m:
        raise SystemExit('MISSING AXIOM REPORT: '+target)
    found={v.strip() for v in m.group(1).split(',') if v.strip()}
    if not found.issubset(allowed):
        raise SystemExit('UNAPPROVED AXIOMS '+target+': '+repr(sorted(found - allowed)))
    print('PASS '+target+': '+repr(sorted(found)))
print('Three main target axiom checks passed.')
PY
