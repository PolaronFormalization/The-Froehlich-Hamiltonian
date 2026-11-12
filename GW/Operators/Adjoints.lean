module

public import GW.Conventions

/-! Adjoint witnesses and reversal of inclusion, from
basic:partial-operator-bridge and basic:selfadjoint-inclusion.
No graph-domain or resolvent existence claim is assumed here. -/
@[expose] public section
noncomputable section
namespace GW.Operators
open scoped ComplexInnerProductSpace
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Conjugation reconciles the manuscript pairing with M132. -/
lemma adjoint_mem_of_witness (T : E →ₗ.[ℂ] F) {y : F} {h : E}
    (hw : ∀ x : T.domain, ⟪T x, y⟫ = ⟪(x : E), h⟫) :
    y ∈ T.adjoint.domain := by
  apply LinearPMap.mem_adjoint_domain_of_exists
  refine ⟨h, fun x => ?_⟩
  rw [← inner_conj_symm h (x : E), ← inner_conj_symm (y : F) (T x), hw x]

/-- M133 needs density separately from membership. -/
lemma adjoint_eq_of_witness (T : E →ₗ.[ℂ] F) (hd : Dense (T.domain : Set E))
    (y : T.adjoint.domain) {h : E}
    (hw : ∀ x : T.domain, ⟪T x, (y : F)⟫ = ⟪(x : E), h⟫) :
    T.adjoint y = h := by
  apply LinearPMap.adjoint_apply_eq hd
  intro x
  rw [← inner_conj_symm h (x : E), ← inner_conj_symm (y : F) (T x), hw x]

/-- The manuscript orientation of the pairing on the full adjoint domain. -/
lemma adjoint_pairing (T : E →ₗ.[ℂ] F) (hd : Dense (T.domain : Set E))
    (x : T.domain) (y : T.adjoint.domain) :
    ⟪T x, (y : F)⟫ = ⟪(x : E), T.adjoint y⟫ := by
  exact (LinearPMap.adjoint_isFormalAdjoint hd).symm x y

/-- Restriction of the adjoint witness gives the reversed full-domain inclusion. -/
lemma adjoint_inclusion {A B : E →ₗ.[ℂ] F}
    (hA : Dense (A.domain : Set E)) (hB : Dense (B.domain : Set E))
    (hAB : A ≤ B) : B.adjoint ≤ A.adjoint := by
  apply LinearPMap.IsFormalAdjoint.le_adjoint hA
  intro x y
  obtain ⟨z, hz, hval⟩ := LinearPMap.exists_of_le hAB x
  rw [hval, hz]
  exact (LinearPMap.adjoint_isFormalAdjoint hB).symm z y

/-- Two self-adjoint operators cannot be proper extensions of one another. -/
lemma selfadjoint_eq_of_inclusion {A B : E →ₗ.[ℂ] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    (hAB : A ≤ B) : A = B := by
  apply le_antisymm hAB
  have h := adjoint_inclusion hA.1 hB.1 hAB
  simpa only [hA.2, hB.2] using h

end GW.Operators
