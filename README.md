# Self-adjointness and domain of the three-dimensional Fröhlich Hamiltonian — Lean 4 formalization

This repository formalizes the three specified results for the three-dimensional Fröhlich kernel, following the mathematical specification in [`source/GW-paper-formalization.tex`](source/GW-paper-formalization.tex), based on Griesemer and Wünsch, [*Self-Adjointness and Domain of the Froehlich Hamiltonian*](https://arxiv.org/abs/1508.02533v2).

The mathematical specification is fixed to SHA-256 `cc5d3975c3b0450758f4bc79e7f1f86ac00a148a03f424427cef42a16ed4815f`.

## Main results

| Result | Lean theorem | Location |
| --- | --- | --- |
| Hamiltonian construction and form domain | `GW.Main.construction` | [`GW/Main/TargetConstruction.lean`](GW/Main/TargetConstruction.lean) |
| Exact operator domain via Gross transformation | `GW.Main.domain` | [`GW/Main/TargetDomain.lean`](GW/Main/TargetDomain.lean) |
| Sharp regularity and critical nonregularity | `GW.Main.regularity` | [`GW/Main/TargetRegularity.lean`](GW/Main/TargetRegularity.lean) |

All proof modules are imported by the original `GW.lean`. The formalization uses **Lean 4.36.0-rc2** and **Mathlib at commit `9bac2d0692944a775113f7c130fd5e5b4608a854`**, pinned in `lean-toolchain`, `lakefile.toml`, and the original `lake-manifest.json`.

## Verify on your machine

Install [`elan`](https://lean-lang.org/install/), Git, and Python 3. From the root of this repository, run:

```bash
lake exe cache get
bash scripts/check.sh
```

The verification script builds the **entire public library** (via the original full-import `GW.lean`), builds `GW.All`, and uses Lean's own `#print axioms` to check the three final theorem dependencies. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. To inspect the statement and axiom output manually:

```bash
lake env lean verification/CheckAxioms.lean
```

The original development reported 108/108 supporting units, 3/3 main targets, 24/24 target clauses, and no unfinished proof debt. This source-only release package has been **statically checked** against the uploaded completed project, but has **not yet been freshly built in an independent Lean environment**. Perform the commands above before treating this repackaging as separately verified; the archived review reports are supporting evidence, not a substitute.

## Repository layout

- `GW/` — mathematical development (Fock, functional analysis, Gross transform, regularity, main theorems).
- `GW.lean` — **original full-import root module**, unchanged from the completed project.
- `GW/All.lean` — optional umbrella module importing `GW`.
- `source/` — immutable expanded mathematical proof specification.
- `verification/CheckAxioms.lean` and `scripts/check.sh` — small public reproducibility checks.
- `.github/workflows/lean.yml` — GitHub Actions build and proof/axiom check.
- `reviews/` — concise historical semantic-review evidence.

No downloaded Mathlib, Lake build caches, Codex session transcripts, scratch proofs, development ledger, or bulk verification logs are included. The completed project's original `lakefile.toml` was simplified **only** by dropping its obsolete `verification` library target; the independent public proof check above replaces it. The original manifest, toolchain, root imports and all retained mathematical proof files are unchanged.

## Attribution and licensing

Please cite the original paper for the mathematical results. The formalization and mathematical specification are distinct works; attribution and the license for this Lean source need to be set by the responsible copyright holder before general reuse. No open-source license has been assigned here.
