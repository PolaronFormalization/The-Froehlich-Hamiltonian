module
public import GW.Fock.Sectors
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
@[expose] public section
noncomputable section
open MeasureTheory
open scoped Topology InnerProductSpace ENNReal
namespace GW.Fock

lemma sectorMeasure_zero : sectorMeasure 0 = Measure.dirac (fun i => Fin.elim0 i) :=
  Measure.pi_of_empty _ _

instance zeroSectorProbability : IsProbabilityMeasure (sectorMeasure 0) where
  measure_univ := Measure.pi_empty_univ _

/-- The scalar-to-empty-product adapter; Sector 0 itself stays ℂ. -/
def vacuumAdapterIsometry : ℂ →ₗᵢ[ℂ] AmbientSector 0 where
  toLinearMap := Lp.constₗ 2 (sectorMeasure 0) ℂ
  norm_map' c := by
    change ‖Lp.const 2 (sectorMeasure 0) c‖ = ‖c‖
    have h := Lp.norm_const' (p := (2 : ℝ≥0∞)) (μ := sectorMeasure 0) (c := c)
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    simpa [measureReal_def] using h

lemma vacuumAdapter_ae (c : ℂ) : vacuumAdapterIsometry c =ᵐ[sectorMeasure 0] (fun _ => c) :=
  Lp.coeFn_const _ _ _

lemma vacuumAdapter_surjective : Function.Surjective vacuumAdapterIsometry := by
  intro u
  refine ⟨u (fun i => Fin.elim0 i), ?_⟩
  apply Lp.ext
  apply (vacuumAdapter_ae _).trans
  exact Filter.Eventually.of_forall (fun k => congrArg u (Subsingleton.elim _ k))

def vacuumAdapter : ℂ ≃ₗᵢ[ℂ] AmbientSector 0 :=
  LinearIsometryEquiv.ofSurjective vacuumAdapterIsometry vacuumAdapter_surjective

lemma vacuumAdapter_eval (u : AmbientSector 0) :
    vacuumAdapter (u (fun i => Fin.elim0 i)) = u := by
  apply Lp.ext
  exact (vacuumAdapter_ae _).trans
    (Filter.Eventually.of_forall (fun k => congrArg u (Subsingleton.elim _ k)))

lemma vacuumAdapter_symm_apply (u : AmbientSector 0) :
    vacuumAdapter.symm u = u (fun i => Fin.elim0 i) := by
  apply vacuumAdapter.injective
  rw [vacuumAdapter.apply_symm_apply,vacuumAdapter_eval]

/-- Inclusion of each positive fixed subspace into the ambient product L² space. -/
def sectorInclusion (n : ℕ) : Sector (n+1) →ₗᵢ[ℂ] AmbientSector (n+1) :=
  (symmetricSector (n+1)).toSubmodule.subtypeₗᵢ

lemma permutationL2_one (n : ℕ) (u : AmbientSector n) : permutationL2 n 1 u = u := by
  change Lp.compMeasurePreserving _ _ u = u
  have he : (coordinatePermutation n 1 : Coordinates n → Coordinates n) = id := by
    funext k i
    simp [coordinatePermutation_apply]
  simp only [he,Lp.compMeasurePreserving_id_apply]

lemma permutationL2_zero (τ : Equiv.Perm (Fin 0)) (c : ℂ) :
    permutationL2 0 τ (vacuumAdapter c) = vacuumAdapter c := by
  have hτ : τ = 1 := Subsingleton.elim _ _
  rw [hτ,permutationL2_one]

lemma permutationL2_comp (n : ℕ) (τ σ : Equiv.Perm (Fin n)) (u : AmbientSector n) :
    permutationL2 n τ (permutationL2 n σ u) = permutationL2 n (τ * σ) u := by
  change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ u) = _
  rw [← Lp.compMeasurePreserving_comp_apply]
  have he : (coordinatePermutation n σ : Coordinates n → Coordinates n) ∘ coordinatePermutation n τ =
      coordinatePermutation n (τ * σ) := by
    funext k i
    simp only [Function.comp_apply,coordinatePermutation_apply,Equiv.Perm.mul_apply]
  simp only [he]
  rfl

lemma permutationL2_inverse (n : ℕ) (τ : Equiv.Perm (Fin n)) (u : AmbientSector n) :
    permutationL2 n τ⁻¹ (permutationL2 n τ u) = u := by
  rw [permutationL2_comp,inv_mul_cancel,permutationL2_one]

def permutationUnitary (n : ℕ) (τ : Equiv.Perm (Fin n)) : AmbientSector n ≃ₗᵢ[ℂ] AmbientSector n :=
  LinearIsometryEquiv.ofSurjective (permutationL2 n τ) (fun u =>
    ⟨permutationL2 n τ⁻¹ u, by rw [permutationL2_comp,mul_inv_cancel,permutationL2_one]⟩)

lemma permutation_pairing (n : ℕ) (τ : Equiv.Perm (Fin n)) (u v : AmbientSector n) :
    ⟪permutationL2 n τ u,v⟫_ℂ = ⟪u,permutationL2 n τ⁻¹ v⟫_ℂ := by
  have h := (permutationL2 n τ).inner_map_map u (permutationL2 n τ⁻¹ v)
  rw [permutationL2_comp,mul_inv_cancel,permutationL2_one] at h
  exact h

set_option backward.isDefEq.respectTransparency.types false in
lemma permutation_adjoint (n : ℕ) (τ : Equiv.Perm (Fin n)) :
    ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := AmbientSector n) (F := AmbientSector n)
      (permutationL2 n τ).toContinuousLinearMap =
      (permutationL2 n τ⁻¹).toContinuousLinearMap := by
  apply Eq.symm
  apply (ContinuousLinearMap.eq_adjoint_iff (𝕜 := ℂ) _ _).mpr
  intro u v
  have h := permutation_pairing n τ⁻¹ u v
  simpa only [LinearIsometry.coe_toContinuousLinearMap,inv_inv] using h

/-- Distinguished-coordinate split in the source's fixed order. -/
def splitCoordinates (n : ℕ) (j : Fin (n+1)) : Coordinates (n+1) ≃ᵐ GW.Space × Coordinates n :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => GW.Space) j

lemma splitCoordinates_apply (n : ℕ) (j : Fin (n+1)) (k : Coordinates (n+1)) :
    splitCoordinates n j k = (k j, fun i => k (j.succAbove i)) := rfl

lemma splitCoordinates_preserving (n : ℕ) (j : Fin (n+1)) :
    MeasurePreserving (splitCoordinates n j) (sectorMeasure (n+1))
      ((volume : Measure GW.Space).prod (sectorMeasure n)) :=
  measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => (volume : Measure GW.Space)) j

lemma splitCoordinates_inverse_preserving (n : ℕ) (j : Fin (n+1)) :
    MeasurePreserving (splitCoordinates n j).symm
      ((volume : Measure GW.Space).prod (sectorMeasure n)) (sectorMeasure (n+1)) :=
  (splitCoordinates_preserving n j).symm _

section Pullback
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β}

lemma pullback_inverse (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν) (u : Lp ℂ 2 μ) :
    Lp.compMeasurePreserving e he
      (Lp.compMeasurePreserving e.symm (he.symm e) u) = u := by
  rw [← Lp.compMeasurePreserving_comp_apply]
  have hi : (e.symm : β → α) ∘ e = id := funext e.symm_apply_apply
  simp only [hi,Lp.compMeasurePreserving_id_apply]

/-- Actual quotient-class unitary pullback by a measure-preserving equivalence. -/
def pullbackUnitary (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν) :
    Lp ℂ 2 ν ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
  LinearIsometryEquiv.ofSurjective (Lp.compMeasurePreservingₗᵢ ℂ e he)
    (fun u => ⟨Lp.compMeasurePreserving e.symm (he.symm e) u, pullback_inverse e he u⟩)

lemma pullbackUnitary_ae (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν) (u : Lp ℂ 2 ν) :
    pullbackUnitary e he u =ᵐ[μ] (fun x => u (e x)) :=
  Lp.coeFn_compMeasurePreserving u he
end Pullback

def splitUnitary (n : ℕ) (j : Fin (n+1)) : AmbientSector (n+1) ≃ₗᵢ[ℂ]
    Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure n)) :=
  pullbackUnitary (splitCoordinates n j).symm (splitCoordinates_inverse_preserving n j)

lemma splitUnitary_ae (n : ℕ) (j : Fin (n+1)) (u : AmbientSector (n+1)) :
    splitUnitary n j u =ᵐ[(volume : Measure GW.Space).prod (sectorMeasure n)]
      (fun z => u ((splitCoordinates n j).symm z)) :=
  pullbackUnitary_ae _ _ _

lemma insertCoordinate_same (n : ℕ) (j : Fin (n+1)) (z : GW.Space) (k : Coordinates n) :
    (splitCoordinates n j).symm (z,k) j = z := by
  simp [splitCoordinates,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]

lemma insertCoordinate_succAbove (n : ℕ) (j : Fin (n+1)) (z : GW.Space) (k : Coordinates n)
    (i : Fin n) : (splitCoordinates n j).symm (z,k) (j.succAbove i) = k i := by
  simp [splitCoordinates,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]

end GW.Fock
