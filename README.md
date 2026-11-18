# Self-adjointness and domain of the three-dimensional Fröhlich Hamiltonian — Lean 4 formalization

[![Lean verification](https://github.com/PolaronFormalization/The-Froehlich-Hamiltonian/actions/workflows/lean.yml/badge.svg)](https://github.com/PolaronFormalization/The-Froehlich-Hamiltonian/actions/workflows/lean.yml)

A **Lean 4 / Mathlib** formalization of the main results from

> M. Griesemer and A. Wünsch, *Self-Adjointness and Domain of the Froehlich Hamiltonian*, [arXiv:1508.02533](https://arxiv.org/abs/1508.02533).

This formalization project establishes the self-adjointness, domain characterization, and regularity properties of the three-dimensional Fröhlich Hamiltonian. The code was obtained with assistance from ChatGPT and Codex. An expanded natural-language proof blueprint is included in [`source/GW-paper-formalization.pdf`](source/GW-paper-formalization.pdf).

## Scope of the formalization

The designated theorems are [`GW.Main.construction`](GW/Main/TargetConstruction.lean), [`GW.Main.domain`](GW/Main/TargetDomain.lean), and [`GW.Main.regularity`](GW/Main/TargetRegularity.lean). Together, they establish the following three results:

1. **Hamiltonian construction and form domain:** The three-dimensional Fröhlich Hamiltonian is constructed as a self-adjoint operator from its associated quadratic form, with the corresponding form-domain characterization.

2. **Exact operator domain:** The operator domain is characterized using the unitary Gross transformation.

3. **Regularity:** Sharp regularity and critical nonregularity properties of vectors in the operator domain are established.

The formalization addresses only the Fröhlich Hamiltomnian, and does **not** treat the more general form factors considered in the original paper.

## Results

The three main theorems are formalized in Lean 4 using Mathlib. The verification checks allow only Lean's standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`). The completed development reported no unfinished proof debt.

The following table lists the main proved results, together with their corresponding Lean declarations and source files.

| Mathematical object or result | Type | Lean declaration | Source file |
| --- | --- | --- | --- |
| Hamiltonian construction and form domain | Theorem | `GW.Main.construction` | [`TargetConstruction.lean`](GW/Main/TargetConstruction.lean) |
| Exact operator domain via Gross transformation | Theorem | `GW.Main.domain` | [`TargetDomain.lean`](GW/Main/TargetDomain.lean) |
| Sharp regularity and critical nonregularity | Theorem | `GW.Main.regularity` | [`TargetRegularity.lean`](GW/Main/TargetRegularity.lean) |

## How to read the formalization

The statements of the three main theorems are contained in [`TargetConstruction.lean`](GW/Main/TargetConstruction.lean), [`TargetDomain.lean`](GW/Main/TargetDomain.lean), and [`TargetRegularity.lean`](GW/Main/TargetRegularity.lean). The mathematical development is contained in [`GW/`](GW/), including the Fock-space construction, functional analysis, Gross transformation, and regularity theory.

The original root module [`GW.lean`](GW.lean) imports the complete mathematical development. An expanded and modified natural-language proof blueprint is available in [`source/GW-paper-formalization.pdf`](source/GW-paper-formalization.pdf).

### Construction of the Fröhlich Hamiltonian

The construction of the Fröhlich Hamiltonian is part of the formalization. The Fröhlich form factor is not square-integrable, so the interaction cannot be defined directly as an ordinary field operator.

Instead, the formalized construction uses ultraviolet cutoffs and the corresponding quadratic forms to define the Hamiltonian. The resulting closed, semibounded quadratic form determines a self-adjoint operator. The formalization further establishes its exact operator domain through the Gross transformation and proves the associated regularity and critical nonregularity results.

Part of the functional-analytic framework developed in this project is also used in our separate [Lean formalization of the absence of excited eigenvalues at weak coupling](https://github.com/PolaronFormalization/Absence-of-eigenvalues-at-weak-coupling). That project concerns the spectral properties of the Fröhlich fiber Hamiltonians and incorporates the present framework under `GW/`.

## Build and check

Install Lean with [elan](https://lean-lang.org/install/), Git, and Python 3. The project uses Lean `v4.36.0-rc2` (`lean-toolchain`), and the exact dependency revisions are pinned in `lake-manifest.json`.

Clone the repository and enter its directory:

```bash
git clone https://github.com/PolaronFormalization/The-Froehlich-Hamiltonian.git
cd The-Froehlich-Hamiltonian
```

Then prepare the dependencies and build the formalization:

```bash
lake exe cache get
bash scripts/check.sh
```

The verification script builds the complete public library through `GW.lean`, builds `GW.All`, and checks the axioms of the three final theorems.

To inspect the theorem statements and their foundational axioms, run:

```bash
lake env lean verification/CheckAxioms.lean
```

The axiom check permits only `propext`, `Classical.choice`, and `Quot.sound`, the standard foundational axioms of Lean.

The source-only release has been statically checked against the original completed development but has not yet been freshly built in an independent Lean environment.

## License and citation

The Lean code is released under the Apache License 2.0 license (see [`LICENSE`](LICENSE)). The mathematical results are described in the paper cited above. If you use this formalization, please cite the corresponding paper and reference this repository.
