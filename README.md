# Self-adjointness and domain of the three-dimensional Fröhlich Hamiltonian — Lean 4 formalization

[![Lean verification](https://github.com/PolaronFormalization/The-Froehlich-Hamiltonian/actions/workflows/lean.yml/badge.svg)](https://github.com/PolaronFormalization/The-Froehlich-Hamiltonian/actions/workflows/lean.yml)

A **Lean 4 / Mathlib** formalization of the main results from

> M. Griesemer and A. Wünsch, *Self-Adjointness and Domain of the Froehlich Hamiltonian*, [arXiv:1508.02533](https://arxiv.org/abs/1508.02533).

This formalization project establishes the self-adjointness, domain characterization, and regularity properties of the three-dimensional Fröhlich Hamiltonian. The code was obtained with assistance from ChatGPT and Codex. An expanded natural-language proof blueprint is included in [`source/GW-paper-formalization.pdf`](source/GW-paper-formalization.pdf).

## Scope of the formalization

The designated theorems are [`GW.Main.construction`](GW/Main/TargetConstruction.lean), [`GW.Main.domain`](GW/Main/TargetDomain.lean), and [`GW.Main.regularity`](GW/Main/TargetRegularity.lean).

Here `H_α` denotes the three-dimensional Fröhlich Hamiltonian on the Hilbert space `L²(ℝ³_x; ℱ)`, formally given by

`H_α = p² + N + Φ(G_{α,x})`   with form factor   `G_{α,x}(k) = e^{-ik·x} √α / |k|`,

where `α ≥ 0`, `p = -i∇_x` is the electron momentum operator, `N` the phonon number operator, `ℱ` the bosonic Fock space, and `Φ(G) = a*(G) + a(G)` the field operator. Since the form factor is not square-integrable at large momenta, the interaction is defined as a limit of ultraviolet-cutoff quadratic forms.

The three theorems establish the following results:

1. **Hamiltonian construction and form domain:** The ultraviolet-cutoff interaction forms converge to a limiting form, and the resulting closed, semibounded quadratic form determines a unique self-adjoint Hamiltonian `H_α` with form domain

   `Q(H_α) = D(|p|) ∩ D(N^{1/2})`.

2. **Exact operator domain:** For sufficiently large `K`, the unitary Gross transformation `U_{α,K}` gives

   `H_α = U_{α,K}* H'_{α,K} U_{α,K}`,

   where the dressed Hamiltonian `H'_{α,K}` is self-adjoint on `D(H_0)`, with `H_0 = p² + N`. In particular,

   `D(H_α) = U_{α,K}* D(H_0)`.

3. **Regularity:** The operator domain satisfies

   `D(H_α) ⊆ D(N) ∩ ⋂_{0 ≤ s < 3/2} D(|p|^s)`.

   For every `α > 0`, the critical exponent is excluded:

   `D(H_α) ∩ D(|p|^{3/2}) = {0}`.

The formalization treats the Fröhlich Hamiltomnian, and does **not** address the general form factors considered in the original paper.

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
