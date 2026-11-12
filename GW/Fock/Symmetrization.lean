module
public import GW.Fock.Coordinates
public import Mathlib.Data.Fintype.Perm
@[expose] public section
noncomputable section
open MeasureTheory
open scoped Topology InnerProductSpace ENNReal
namespace GW.Fock

/-- The source's normalized sum over all coordinate permutations. -/
def symmetrizer (n : ℕ) : AmbientSector n →L[ℂ] AmbientSector n :=
  ((n.factorial : ℂ)⁻¹) • ∑ τ : Equiv.Perm (Fin n), (permutationL2 n τ).toContinuousLinearMap

lemma symmetrizer_apply (n : ℕ) (u : AmbientSector n) :
    symmetrizer n u = ((n.factorial : ℂ)⁻¹) • ∑ τ : Equiv.Perm (Fin n), permutationL2 n τ u := by
  simp only [symmetrizer,smul_apply,sum_apply]
  rfl

lemma symmetrizer_fixed (n : ℕ) (τ : Equiv.Perm (Fin n)) (u : AmbientSector n) :
    permutationL2 n τ (symmetrizer n u) = symmetrizer n u := by
  rw [symmetrizer_apply,map_smul,map_sum]
  simp_rw [permutationL2_comp]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun _ => rfl)

lemma symmetrizer_mem (n : ℕ) (u : AmbientSector n) : symmetrizer n u ∈ symmetricSector n :=
  fun τ => symmetrizer_fixed n τ u

lemma symmetrizer_of_fixed (n : ℕ) (u : AmbientSector n) (hu : u ∈ symmetricSector n) :
    symmetrizer n u = u := by
  change (∀ τ : Equiv.Perm (Fin n), permutationL2 n τ u = u) at hu
  rw [symmetrizer_apply]
  simp_rw [hu]
  rw [Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ,smul_smul]
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [inv_mul_cancel₀ hn,one_smul]

lemma symmetrizer_idempotent (n : ℕ) : (symmetrizer n).comp (symmetrizer n) = symmetrizer n := by
  apply ContinuousLinearMap.ext
  intro u
  exact symmetrizer_of_fixed n _ (symmetrizer_mem n u)

lemma symmetrizer_pairing (n : ℕ) (u v : AmbientSector n) :
    ⟪symmetrizer n u,v⟫_ℂ = ⟪u,symmetrizer n v⟫_ℂ := by
  rw [symmetrizer_apply,symmetrizer_apply,inner_smul_left,inner_smul_right,
    sum_inner,inner_sum]
  simp only [map_inv₀,map_natCast]
  congr 1
  simp_rw [permutation_pairing]
  exact Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n))) _ _ (fun _ => rfl)

lemma symmetrizer_norm_le (n : ℕ) (u : AmbientSector n) : ‖symmetrizer n u‖ ≤ ‖u‖ := by
  have hi := symmetrizer_pairing n u (symmetrizer n u)
  have he := symmetrizer_of_fixed n _ (symmetrizer_mem n u)
  rw [he] at hi
  have hb : ‖symmetrizer n u‖ ^ 2 ≤ ‖u‖ * ‖symmetrizer n u‖ := by
    calc
      ‖symmetrizer n u‖ ^ 2 = (⟪symmetrizer n u,symmetrizer n u⟫_ℂ).re :=
        norm_sq_eq_re_inner (𝕜 := ℂ) (symmetrizer n u)
      _ = (⟪u,symmetrizer n u⟫_ℂ).re := congrArg Complex.re hi
      _ ≤ ‖⟪u,symmetrizer n u⟫_ℂ‖ := Complex.re_le_norm _
      _ ≤ ‖u‖ * ‖symmetrizer n u‖ := norm_inner_le_norm _ _
  nlinarith [norm_nonneg (symmetrizer n u),norm_nonneg u]

lemma symmetrizer_opNorm_le (n : ℕ) : ‖symmetrizer n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa only [one_mul] using symmetrizer_norm_le n u

lemma symmetrizer_range (n : ℕ) : Set.range (symmetrizer n) = (symmetricSector n : Set (AmbientSector n)) := by
  ext u
  constructor
  · rintro ⟨v,rfl⟩
    exact symmetrizer_mem n v
  · intro hu
    exact ⟨u,symmetrizer_of_fixed n u hu⟩

set_option backward.isDefEq.respectTransparency.types false in
lemma symmetrizer_selfadjoint (n : ℕ) :
    ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := AmbientSector n) (F := AmbientSector n)
      (symmetrizer n) = symmetrizer n := by
  apply Eq.symm
  apply (ContinuousLinearMap.eq_adjoint_iff (𝕜 := ℂ) _ _).mpr
  exact symmetrizer_pairing n

set_option backward.isDefEq.respectTransparency.types false in
lemma symmetrizer_isStarProjection (n : ℕ) : IsStarProjection (symmetrizer n) := by
  constructor
  · exact symmetrizer_idempotent n
  · exact symmetrizer_selfadjoint n

lemma symmetrizer_orthogonal (n : ℕ) (u v : AmbientSector n) (hv : v ∈ symmetricSector n) :
    ⟪v,u-symmetrizer n u⟫_ℂ = 0 := by
  rw [inner_sub_right,← symmetrizer_pairing,symmetrizer_of_fixed n v hv,sub_self]

lemma carrier_inner_absolute (u v : Carrier) : Summable (fun n => ‖⟪u n,v n⟫_ℂ‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun _ => norm_inner_le_norm _ _)
  exact lp.summable_mul (by rw [Real.holderConjugate_iff]; norm_num) u v

lemma dense_finite_sectors (E : ℕ → Type*) [∀ n, NormedAddCommGroup (E n)]
    [∀ n, NormedSpace ℂ (E n)] : Dense (⋃ m, Set.range (cutoff E m)) := by
  intro u
  apply mem_closure_of_tendsto (cutoff_tendsto E u)
  exact Filter.Eventually.of_forall (fun m => Set.mem_iUnion.mpr ⟨m,⟨u,rfl⟩⟩)

lemma carrier_finite_sectors_dense : Dense (⋃ m, Set.range (P m)) := dense_finite_sectors Sector
lemma electron_finite_sectors_dense : Dense (⋃ m, Set.range (electronP m)) := dense_finite_sectors ElectronSector

end GW.Fock
