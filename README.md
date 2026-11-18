
# Self-adjointness and domain of the three-dimensional Fröhlich Hamiltonian — Lean 4 formalization

[![Lean verification](https://github.com/PolaronFormalization/The-Froehlich-Hamiltonian/actions/workflows/lean.yml/badge.svg)](https://github.com/PolaronFormalization/The-Froehlich-Hamiltonian/actions/workflows/lean.yml)

A Lean 4 / Mathlib formalization of three results concerning the three-dimensional Fröhlich Hamiltonian, based on

> M. Griesemer and A. Wünsch, *Self-Adjointness and Domain of the Froehlich Hamiltonian*, [arXiv:1508.02533](https://arxiv.org/abs/1508.02533).

The formalization follows the mathematical specification in [`source/GW-paper-formalization.tex`](source/GW-paper-formalization.tex). The specification is fixed to SHA-256 `cc5d3975c3b0450758f4bc79e7f1f86ac00a148a03f424427cef42a16ed4815f`.

## Main results

The formalization establishes three results for the three-dimensional Fröhlich Hamiltonian:

1. **Hamiltonian construction and form domain:** construction of the self-adjoint Hamiltonian from its quadratic form, including its form domain.
2. **Exact operator domain:** characterization of the operator domain using the Gross transformation.
3. **Regularity:** sharp regularity and critical nonregularity properties of vectors in the operator domain.

## Results

| Mathematical object or result | Type | Lean declaration | Source file |
| --- | --- | --- | --- |
| Hamiltonian construction and form domain | Theorem | `GW.Main.construction` | [`TargetConstruction.lean`](GW/Main/TargetConstruction.lean) |
| Exact operator domain via Gross transformation | Theorem | `GW.Main.domain` | [`TargetDomain.lean`](GW/Main/TargetDomain.lean) |
| Sharp regularity and critical nonregularity | Theorem | `GW.Main.regularity` | [`TargetRegularity.lean`](GW/Main/TargetRegularity.lean) |

## How to read the formalization

The three final theorems are stated in the source files linked above. The mathematical development is contained in [`GW/`](GW/), including the Fock-space framework, functional analysis, Gross transformation, and regularity theory. The original root module [`GW.lean`](GW.lean) imports the full development, while [`GW/All.lean`](GW/All.lean) is an additional umbrella module.

The expanded mathematical specification is available in [`source/GW-paper-formalization.tex`](source/GW-paper-formalization.tex). The [`reviews/`](reviews/) directory contains historical semantic-review reports of the original development.

This source release omits downloaded Mathlib files, build caches, session transcripts, scratch proofs, and bulk verification logs. The original `lakefile.toml` was simplified only by removing its obsolete `verification` library target; the manifest, toolchain, root imports, and retained mathematical proof files are unchanged.

Part of this functional-analytic framework is also used in our separate [Lean formalization of the absence of excited eigenvalues at weak coupling](https://github.com/PolaronFormalization/Absence-of-eigenvalues-at-weak-coupling). That project concerns the spectral properties of the fiber Hamiltonians, rather than the domain and regularity of the full Hamiltonian.

## Build and check

Install Lean with [elan](https://lean-lang.org/install/), as well as Git and Python 3. The project uses Lean `v4.36.0-rc2` and Mathlib at commit `9bac2d0692944a775113f7c130fd5e5b4608a854`, with dependency versions pinned by the project files.

Clone the repository and enter its directory:

```bash
git clone https://github.com/PolaronFormalization/The-Froehlich-Hamiltonian.git
cd The-Froehlich-Hamiltonian
```

Then download the available Mathlib cache and run the verification script:

```bash
lake exe cache get
bash scripts/check.sh
```

The script builds the entire public library through the original full-import [`GW.lean`](GW.lean), builds `GW.All`, and checks the axioms of the three final theorems. Only Lean's standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`) are permitted. To inspect the theorem statements and axiom output directly, run:

```bash
lake env lean verification/CheckAxioms.lean
```

**Verification status.** The original completed development reported 108/108 supporting units, 3/3 main targets, 24/24 target clauses, and no unfinished proof debt. This source-only release was statically checked against that development, but **has not yet been freshly built in an independent Lean environment**. The archived review reports provide supporting evidence, not a substitute for a fresh build of this repository.

## License and citation

Please cite the Griesemer–Wünsch paper above for the mathematical results and reference this repository when discussing the Lean formalization. The formalization and its mathematical specification are distinct works. **No open-source license has currently been assigned to this repository**; terms for general reuse must be established by the responsible copyright holder.
