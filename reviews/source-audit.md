# GW formalization — independent source-level semantic review

**Review basis:** user-supplied `GW-Lean-source.zip` (116 Lean source files, 55,457 lines); the previously supplied `final-public-targets.log`, `completion.json`, and `final-semantic-review.md`; and the original revision-10 LaTeX target statements. **Method:** direct inspection and cross-referencing of definitions and main theorem source; static scan for unproved-proof tokens and suspicious bypasses. This is not a fresh Lean compilation, exhaustive proof review, or independent kernel run.

## Main finding

**No material mismatch was identified in the main mathematical interfaces examined.** The names used by the three published target lemmas resolve through concrete definitions to the physical Fock-space and free/interacting operators described in the mathematical specification. The reported successful build and allowed-axiom audit provide strong additional evidence, but were not independently rerun here.

## Concrete definition chain

1. **Physical space and coupling.** `GW/Conventions.lean` defines the momentum/position space as `EuclideanSpace ℝ (Fin 3)` and the one-phonon Hilbert space as complex L². `GW/Fock/Sectors.lean` defines vacuum sector `ℂ`, higher symmetric L² sectors, their dependent ℓ² sum, and physical Bochner L² over electron position. `GW/Model/Coefficient.lean` defines `v α k = Real.sqrt α / ‖k‖`, with zero value at zero, and `b α K k` as `-v/(1+‖k‖²)` above the low-momentum cutoff. Both match the fixed-model conventions.
2. **Free Hamiltonian and domains.** `GW/Operators/BasicFree.lean` defines `freeFourierRepresentation` as the physical Bochner-sector equivalence followed by the sectorwise Fourier equivalence, `freeEnergySymbol n p = ‖p‖² + n`, and `freeHamiltonian` as the *maximal* corresponding physical multiplier. The same file defines the canonical free form and graph weights, and proves `freeHamiltonian.domain = freeMomentumSquare.domain ⊓ physicalNumberOperator.domain`.
3. **Self-adjointness is not weakened.** `GW/Conventions.lean` defines `GW.IsSelfAdjointOperator T` as density of the partial operator domain **and** `T.adjoint = T`. `GW/Operators/FormRepresentation.lean` defines the form-representing operator via an inverse-resolvent partial map on its actual range, with the actual form equation, uniqueness, and lower bounds.
4. **The physical interacting Hamiltonian is the form-representation operator.** `GW/Gross/MainFormH.lean` defines `constructionLimitForm` from a limit of the original cutoff perturbation forms; `constructionClosedData` from the uniform coercive form data; and `constructionHamiltonian α hα := GW.Operators.formOperator (constructionClosedData α hα none)`. The same source proves that this named operator is self-adjoint, represents the actual full form, and is the unique such operator. This resolves the specific concern that the printed main target only quantified a unique operator without naming it.
5. **Gross transform and domain.** `GW/Analysis/BridgePhaseDerivative.lean` defines `phaseAt` by multiplication with the physical phase; `GW/Analysis/Fourier.lean` defines that phase as `exp(-i ⟪x,k⟫)`. `GW/Fock/FockWeyl.lean` defines the Weyl action from exponential vectors, with the stated normalization. `GW/Gross/MainGrossConvergence.lean` defines the physical Weyl action fiberwise; `GW/Gross/MainDomain.lean` defines `domainGrossUnitary` as its inverse and proves equality of the *named construction Hamiltonian* with the unitary transport of the dressed operator. `GW/Operators/ResolventAlgebra.lean` defines unitary transport on the preimage domain, with action `U⁻¹ T U` and domain `U⁻¹ D(T)`.
6. **Regularity operators and endpoints.** `GW/Regularity/RegMixedDomains.lean` defines `electronRadialPower r` as the maximal Fourier-sector multiplier `‖q‖^r`; `GW/Regularity/RegMainCorollary.lean` defines `electronLaplacianPower t` as `(‖q‖²)^t` and proves equality with radial power `2t`. `GW/Main/TargetRegularity.lean` uses these actual domains, with `α > 0` for the critical obstruction, and preserves the free-operator identity at `α = 0`.

## Three main targets

- `GW/Main/TargetConstruction.lean`: verified against the LaTeX construction target. Cutoff-form norm convergence, form identity, self-adjoint representation, domain of the form, and zero-coupling behavior are present.
- `GW/Main/TargetDomain.lean`: correct Gross sign and full transported domain/operator identities are present, including actual graph witnesses for the product terms and independence of sufficiently large cutoff.
- `GW/Main/TargetRegularity.lean`: `s<3/2`, `t<3/4`, number-domain membership, `α>0` endpoint exclusion, higher exponents, and zero-coupling exception are present.

## Static scan

- 116 `.lean` files, 55,457 source lines, ~3.03 MB uncompressed, in the supplied `GW/` directory.
- Static keyword scan found no occurrence of `sorry`, `admit`, `sorryAx`, `native_decide`, `unsafe`, or `opaque` in these files. This is an *additional heuristic*, not a substitute for the reported transitive `#print axioms` results.
- Imports seen in this subtree reference `GW`, `GW.*`, or `Mathlib.*`, not another external mathematics library.

## Remaining verification boundary

1. The archive is **not the entire Lake project**: at least the root `GW.lean`, toolchain/manifest, and `.lake` are not included. The audit report mentions 119 retained modules, while 116 `.lean` files are present under `GW/`. This is explainable by separately located root modules, but the full retained module inventory was not independently reconciled from this archive.
2. I could not rerun `lake build` or the Lean kernel against the pinned toolchain and mathlib in this environment. Those successful checks are evidenced by the uploaded logs and final completion report, not by a new run here.
3. This review traced the main defining objects and inspected their interfaces; it is not a line-by-line independent analysis of all 5,003 helper proofs or a formal proof that every mathematical claim made in the audit report follows from the sources.

**Assessment:** The particular semantic concerns previously identified are resolved by actual definitions in the uploaded source. On the evidence available, no source-level red flag warrants altering the completed proof. For research release, preserve a reproducible source snapshot including `GW.lean`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, the main `GW/` tree, and essential final-verification records; consider a clean build on another machine as an additional check.
