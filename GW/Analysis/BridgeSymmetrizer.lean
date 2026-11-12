module
public import GW.Fock.Symmetrization
public import GW.Fock.FockAmplification
public import Mathlib.Algebra.Group.Subgroup.Basic
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace GW.Fock
attribute [local instance] Classical.propDecidable
section GroupAverage
variable {G H : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- The finite normalized average of the given actual bounded representation. -/
def groupAverage (ρ : G →* (H →L[ℂ] H)) : H →L[ℂ] H :=
  ((Fintype.card G : ℂ)⁻¹) • ∑ g : G, ρ g

lemma groupAverage_apply (ρ : G →* (H →L[ℂ] H)) (x : H) :
    groupAverage ρ x = ((Fintype.card G : ℂ)⁻¹) • ∑ g : G, ρ g x := by
  simp only [groupAverage,smul_apply,sum_apply]

lemma groupAverage_mul_element (ρ : G →* (H →L[ℂ] H)) (h : G) :
    groupAverage ρ * ρ h = groupAverage ρ := by
  apply ContinuousLinearMap.ext
  intro x
  change groupAverage ρ (ρ h x) = groupAverage ρ x
  rw [groupAverage_apply,groupAverage_apply]
  have he (g : G) : ρ g (ρ h x) = ρ (g*h) x := by rw [map_mul]; rfl
  simp_rw [he]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulRight h) (fun g => ρ (g*h) x) (fun g => ρ g x) (fun _ => rfl)

lemma element_mul_groupAverage (ρ : G →* (H →L[ℂ] H)) (h : G) :
    ρ h * groupAverage ρ = groupAverage ρ := by
  apply ContinuousLinearMap.ext
  intro x
  change ρ h (groupAverage ρ x) = groupAverage ρ x
  simp only [groupAverage_apply,map_smul,map_sum]
  have he (g : G) : ρ h (ρ g x) = ρ (h*g) x := by rw [map_mul]; rfl
  simp_rw [he]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft h) (fun g => ρ (h*g) x) (fun g => ρ g x) (fun _ => rfl)

lemma groupAverage_mul_subgroup (ρ : G →* (H →L[ℂ] H)) (K : Subgroup G) :
    groupAverage ρ * groupAverage (ρ.comp K.subtype) = groupAverage ρ := by
  classical
  apply ContinuousLinearMap.ext
  intro x
  change groupAverage ρ (groupAverage (ρ.comp K.subtype) x) = _
  rw [groupAverage_apply (ρ.comp K.subtype) x,map_smul,map_sum]
  have he (k : K) : groupAverage ρ (ρ k x) = groupAverage ρ x :=
    congrArg (fun T : H →L[ℂ] H => T x) (groupAverage_mul_element ρ k)
  simp only [MonoidHom.comp_apply,Subgroup.coe_subtype] 
  simp_rw [he]
  rw [Finset.sum_const,Finset.card_univ,← Nat.cast_smul_eq_nsmul ℂ,smul_smul]
  have hc : (Fintype.card K : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [inv_mul_cancel₀ hc,one_smul]

lemma subgroup_mul_groupAverage (ρ : G →* (H →L[ℂ] H)) (K : Subgroup G) :
    groupAverage (ρ.comp K.subtype) * groupAverage ρ = groupAverage ρ := by
  classical
  apply ContinuousLinearMap.ext
  intro x
  change groupAverage (ρ.comp K.subtype) (groupAverage ρ x) = _
  rw [groupAverage_apply]
  have he (k : K) : ρ k (groupAverage ρ x) = groupAverage ρ x :=
    congrArg (fun T : H →L[ℂ] H => T x) (element_mul_groupAverage ρ k)
  simp only [MonoidHom.comp_apply,Subgroup.coe_subtype]
  simp_rw [he]
  rw [Finset.sum_const,Finset.card_univ,← Nat.cast_smul_eq_nsmul ℂ,smul_smul]
  have hc : (Fintype.card K : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [inv_mul_cancel₀ hc,one_smul]
end GroupAverage
/-- The spectator subgroup fixes the explicitly distinguished coordinate zero. -/
def fixesZero (n : ℕ) : Subgroup (Equiv.Perm (Fin (n+1))) where
  carrier := {σ | σ 0 = 0}
  one_mem' := rfl
  mul_mem' := by
    intro σ τ hσ hτ
    change σ (τ 0) = 0
    rw [hτ,hσ]
  inv_mem' := by
    intro σ hσ
    apply σ.injective
    change σ (σ.symm 0) = σ 0
    rw [Equiv.apply_symm_apply,hσ]

def swapZero (n : ℕ) (j : Fin (n+1)) : Equiv.Perm (Fin (n+1)) := Equiv.swap 0 j

lemma swapZero_zero (n : ℕ) (j : Fin (n+1)) : swapZero n j 0 = j := Equiv.swap_apply_left _ _
lemma swapZero_self (n : ℕ) (j : Fin (n+1)) : swapZero n j j = 0 := Equiv.swap_apply_right _ _
lemma swapZero_inverse (n : ℕ) (j : Fin (n+1)) : (swapZero n j)⁻¹ = swapZero n j := Equiv.swap_inv _ _

/-- The source's explicit coset bijection σ ↔ (σ(0), t_(σ(0))⁻¹ σ). -/
def permutationSpectatorEquiv (n : ℕ) :
    Equiv.Perm (Fin (n+1)) ≃ (Fin (n+1) × fixesZero n) where
  toFun σ := (σ 0, ⟨(swapZero n (σ 0))⁻¹ * σ,by
    change (swapZero n (σ 0))⁻¹ (σ 0) = 0
    rw [swapZero_inverse,swapZero_self]⟩)
  invFun p := swapZero n p.1 * p.2
  left_inv σ := by
    change swapZero n (σ 0) * ((swapZero n (σ 0))⁻¹ * σ) = σ
    exact mul_inv_cancel_left _ _
  right_inv p := by
    rcases p with ⟨j,h⟩
    have hh : (h : Equiv.Perm (Fin (n+1))) 0 = 0 := h.property
    have he : (swapZero n j * (h : Equiv.Perm (Fin (n+1)))) 0 = j := by
      change swapZero n j ((h : Equiv.Perm (Fin (n+1))) 0) = j
      rw [hh,swapZero_zero]
    apply Prod.ext
    · exact he
    · apply Subtype.ext
      change (swapZero n ((swapZero n j * (h : Equiv.Perm (Fin (n+1)))) 0))⁻¹ *
        (swapZero n j * (h : Equiv.Perm (Fin (n+1)))) = h
      rw [he]
      exact inv_mul_cancel_left _ _

lemma permutationSpectator_card (n : ℕ) :
    Fintype.card (Equiv.Perm (Fin (n+1))) = (n+1) * Fintype.card (fixesZero n) := by
  simpa only [Fintype.card_prod,Fintype.card_fin] using Fintype.card_congr (permutationSpectatorEquiv n)

section SpectatorAverage
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

lemma spectator_coset_sum (n : ℕ) (ρ : Equiv.Perm (Fin (n+1)) →* (H →L[ℂ] H)) (z : H)
    (hz : ∀ h : fixesZero n, ρ h z = z) :
    (∑ σ : Equiv.Perm (Fin (n+1)), ρ σ z) =
      (Fintype.card (fixesZero n) : ℂ) • ∑ j : Fin (n+1), ρ (swapZero n j) z := by
  classical
  calc
    _ = ∑ p : Fin (n+1) × fixesZero n, ρ ((permutationSpectatorEquiv n).symm p) z :=
      Fintype.sum_equiv (permutationSpectatorEquiv n) _ _ (fun σ => by rw [Equiv.symm_apply_apply])
    _ = ∑ j : Fin (n+1), ∑ h : fixesZero n, ρ (swapZero n j * (h : Equiv.Perm (Fin (n+1)))) z := by
      rw [Fintype.sum_prod_type]; rfl
    _ = ∑ j : Fin (n+1), ∑ _h : fixesZero n, ρ (swapZero n j) z := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro h _
      rw [map_mul]
      change ρ (swapZero n j) (ρ h z) = _
      rw [hz h]
    _ = (Fintype.card (fixesZero n) : ℂ) • ∑ j : Fin (n+1), ρ (swapZero n j) z := by
      simp only [Finset.sum_const,Finset.card_univ,← Nat.cast_smul_eq_nsmul ℂ,Finset.smul_sum]

lemma spectator_average (n : ℕ) (ρ : Equiv.Perm (Fin (n+1)) →* (H →L[ℂ] H)) (z : H)
    (hz : ∀ h : fixesZero n, ρ h z = z) :
    groupAverage ρ z = ((n+1 : ℕ) : ℂ)⁻¹ • ∑ j : Fin (n+1), ρ (swapZero n j) z := by
  rw [groupAverage_apply,spectator_coset_sum n ρ z hz,smul_smul,permutationSpectator_card,Nat.cast_mul]
  have hk : (Fintype.card (fixesZero n) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hn : ((n+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  congr 1
  field_simp

lemma creation_sqrt_coefficient (n : ℕ) :
    Real.sqrt (n+1 : ℕ) * ((n+1 : ℕ) : ℝ)⁻¹ = (Real.sqrt (n+1 : ℕ))⁻¹ := by
  have hn : (0 : ℝ) < (n+1 : ℕ) := by positivity
  have hs : 0 < Real.sqrt (n+1 : ℕ) := Real.sqrt_pos.mpr hn
  have hsq := Real.sq_sqrt hn.le
  rw [← one_div (Real.sqrt (n+1 : ℕ))]
  apply (eq_div_iff (ne_of_gt hs)).mpr
  calc
    _ = (Real.sqrt (n+1 : ℕ))^2 * ((n+1 : ℕ) : ℝ)⁻¹ := by ring
    _ = 1 := by rw [hsq,mul_inv_cancel₀ hn.ne']
end SpectatorAverage

/-- The established actual coordinate permutations as a bounded representation. -/
def permutationRepresentation (n : ℕ) : Equiv.Perm (Fin n) →* (AmbientSector n →L[ℂ] AmbientSector n) where
  toFun τ := (permutationL2 n τ).toContinuousLinearMap
  map_one' := by
    apply ContinuousLinearMap.ext
    intro u
    exact permutationL2_one n u
  map_mul' τ σ := by
    apply ContinuousLinearMap.ext
    intro u
    exact (permutationL2_comp n τ σ u).symm

lemma permutation_groupAverage (n : ℕ) : groupAverage (permutationRepresentation n) = symmetrizer n := by
  simp only [groupAverage,symmetrizer,permutationRepresentation,Fintype.card_perm,Fintype.card_fin]
  rfl

lemma symmetrizer_subgroup_right (n : ℕ) (K : Subgroup (Equiv.Perm (Fin n))) :
    symmetrizer n * groupAverage ((permutationRepresentation n).comp K.subtype) = symmetrizer n := by
  rw [← permutation_groupAverage]
  exact groupAverage_mul_subgroup _ _

lemma symmetrizer_subgroup_left (n : ℕ) (K : Subgroup (Equiv.Perm (Fin n))) :
    groupAverage ((permutationRepresentation n).comp K.subtype) * symmetrizer n = symmetrizer n := by
  rw [← permutation_groupAverage]
  exact subgroup_mul_groupAverage _ _

lemma symmetrizer_spectator_average (n : ℕ) (z : AmbientSector (n+1))
    (hz : ∀ h : fixesZero n, permutationL2 (n+1) h z = z) :
    symmetrizer (n+1) z = (((n+1 : ℕ) : ℂ)⁻¹) •
      ∑ j : Fin (n+1), permutationL2 (n+1) (swapZero n j) z := by
  rw [← permutation_groupAverage]
  exact spectator_average n (permutationRepresentation (n+1)) z hz

/-- The remaining indices in their source order, including the empty vacuum list. -/
def nonzeroIndexEquiv (n : ℕ) : Fin n ≃ {i : Fin (n+1) // i ≠ 0} where
  toFun i := ⟨i.succ,Fin.succ_ne_zero i⟩
  invFun i := i.val.pred i.property
  left_inv i := Fin.pred_succ i
  right_inv i := Subtype.ext (Fin.succ_pred i.val i.property)

lemma fixesZero_preserves_nonzero (n : ℕ) (h : fixesZero n) (i : Fin (n+1)) :
    (h : Equiv.Perm (Fin (n+1))) i ≠ 0 ↔ i ≠ 0 := by
  have hz : (h : Equiv.Perm (Fin (n+1))) 0 = 0 := h.property
  constructor
  · intro hi hi0
    apply hi
    rw [hi0]
    exact hz
  · intro hi hzero
    apply hi
    exact (h : Equiv.Perm (Fin (n+1))).injective (hzero.trans hz.symm)

def spectatorRestriction (n : ℕ) (h : fixesZero n) : Equiv.Perm (Fin n) :=
  ((nonzeroIndexEquiv n).trans
    ((h : Equiv.Perm (Fin (n+1))).subtypePerm (fixesZero_preserves_nonzero n h))).trans (nonzeroIndexEquiv n).symm

lemma spectatorRestriction_apply (n : ℕ) (h : fixesZero n) (i : Fin n) :
    (h : Equiv.Perm (Fin (n+1))) i.succ = (spectatorRestriction n h i).succ := by
  have hm : (h : Equiv.Perm (Fin (n+1))) i.succ ≠ 0 :=
    (fixesZero_preserves_nonzero n h i.succ).mpr (Fin.succ_ne_zero i)
  change (h : Equiv.Perm (Fin (n+1))) i.succ =
    (((h : Equiv.Perm (Fin (n+1))) i.succ).pred hm).succ
  exact (Fin.succ_pred _ _).symm

lemma splitUnitary_symm_ae (n : ℕ) (j : Fin (n+1))
    (v : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure n))) :
    (splitUnitary n j).symm v =ᵐ[sectorMeasure (n+1)] fun k => v (splitCoordinates n j k) := by
  have he : (splitUnitary n j).symm v =
      Lp.compMeasurePreserving (splitCoordinates n j) (splitCoordinates_preserving n j) v := by
    apply (splitUnitary n j).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    symm
    change Lp.compMeasurePreserving (splitCoordinates n j).symm (splitCoordinates_inverse_preserving n j)
      (Lp.compMeasurePreserving (splitCoordinates n j) (splitCoordinates_preserving n j) v) = v
    rw [← Lp.compMeasurePreserving_comp_apply]
    have hc : (splitCoordinates n j : Coordinates (n+1) → _) ∘ (splitCoordinates n j).symm = id :=
      funext (splitCoordinates n j).apply_symm_apply
    simp only [hc,Lp.compMeasurePreserving_id_apply]
  rw [he]
  exact Lp.coeFn_compMeasurePreserving _ _

def prependProduct (n : ℕ) (f : Lp ℂ 2 (volume : Measure GW.Space)) (u : AmbientSector n) : AmbientSector (n+1) :=
  (splitUnitary n 0).symm (productFunction volume (sectorMeasure n) f u)

lemma prependProduct_ae (n : ℕ) (f : Lp ℂ 2 (volume : Measure GW.Space)) (u : AmbientSector n) :
    prependProduct n f u =ᵐ[sectorMeasure (n+1)] fun k => f (k 0) * u (fun i => k i.succ) := by
  apply (splitUnitary_symm_ae n 0 _).trans
  have h := (splitCoordinates_preserving n 0).quasiMeasurePreserving.ae
    (productFunction_ae volume (sectorMeasure n) f u)
  filter_upwards [h] with k hk
  simpa only [splitCoordinates_apply,Fin.zero_succAbove,smul_eq_mul] using hk

lemma prependProduct_fixed (n : ℕ) (f : Lp ℂ 2 (volume : Measure GW.Space))
    (u : AmbientSector n) (hu : u ∈ symmetricSector n) (h : fixesZero n) :
    permutationL2 (n+1) h (prependProduct n f u) = prependProduct n f u := by
  let τ := spectatorRestriction n h
  have huτ := (permutation_fixed_iff n τ u).mp (hu τ)
  have htail := (splitCoordinates_preserving n 0).quasiMeasurePreserving.ae
    ((Measure.quasiMeasurePreserving_snd (μ := (volume : Measure GW.Space)) (ν := sectorMeasure n)).ae huτ)
  apply Lp.ext
  filter_upwards [permutationL2_ae (n+1) h (prependProduct n f u),
    (coordinatePermutation_preserving (n+1) h).quasiMeasurePreserving.ae (prependProduct_ae n f u),
    prependProduct_ae n f u,htail] with k h₁ h₂ h₃ ht
  rw [h₁,h₂,h₃]
  have hz : (h : Equiv.Perm (Fin (n+1))) 0 = 0 := h.property
  simp only [coordinatePermutation_apply,hz]
  congr 1
  have he : (fun i : Fin n => k ((h : Equiv.Perm (Fin (n+1))) i.succ)) =
      coordinatePermutation n τ (fun i => k i.succ) := by
    funext i
    rw [coordinatePermutation_apply,spectatorRestriction_apply]
  rw [he]
  simpa only [splitCoordinates_apply,Fin.zero_succAbove] using ht

/-- Every deleted-slot list is given its declared increasing source order. -/
def deletedIndexEquiv (n : ℕ) (j : Fin (n+1)) : Fin n ≃ {i : Fin (n+1) // i ≠ j} :=
  Equiv.ofBijective (fun i => ⟨j.succAbove i,Fin.succAbove_ne j i⟩)
    ⟨fun _ _ h => Fin.succAbove_right_injective (congrArg Subtype.val h),fun k => by
      obtain ⟨i,hi⟩ := Fin.exists_succAbove_eq k.property
      exact ⟨i,Subtype.ext hi⟩⟩

def swapDeletedEquiv (n : ℕ) (j : Fin (n+1)) :
    {i : Fin (n+1) // i ≠ 0} ≃ {i : Fin (n+1) // i ≠ j} :=
  (swapZero n j).subtypeEquiv (fun i => by
    constructor
    · intro hi hz
      apply hi
      exact (swapZero n j).injective (hz.trans (swapZero_zero n j).symm)
    · intro hi hz
      apply hi
      rw [hz,swapZero_zero])

def swapSpectatorOrder (n : ℕ) (j : Fin (n+1)) : Equiv.Perm (Fin n) :=
  ((nonzeroIndexEquiv n).trans (swapDeletedEquiv n j)).trans (deletedIndexEquiv n j).symm

lemma swapSpectatorOrder_apply (n : ℕ) (j : Fin (n+1)) (i : Fin n) :
    swapZero n j i.succ = j.succAbove (swapSpectatorOrder n j i) := by
  have he := congrArg Subtype.val ((deletedIndexEquiv n j).apply_symm_apply
    (swapDeletedEquiv n j (nonzeroIndexEquiv n i)))
  change j.succAbove (swapSpectatorOrder n j i) = swapZero n j i.succ at he
  exact he.symm

lemma swap_prependProduct_ae (n : ℕ) (j : Fin (n+1)) (f : Lp ℂ 2 (volume : Measure GW.Space))
    (u : AmbientSector n) (hu : u ∈ symmetricSector n) :
    permutationL2 (n+1) (swapZero n j) (prependProduct n f u) =ᵐ[sectorMeasure (n+1)]
      fun k => f (k j) * u (fun i => k (j.succAbove i)) := by
  let τ := swapSpectatorOrder n j
  have huτ := (permutation_fixed_iff n τ u).mp (hu τ)
  have htail := (splitCoordinates_preserving n j).quasiMeasurePreserving.ae
    ((Measure.quasiMeasurePreserving_snd (μ := (volume : Measure GW.Space)) (ν := sectorMeasure n)).ae huτ)
  filter_upwards [permutationL2_ae (n+1) (swapZero n j) (prependProduct n f u),
    (coordinatePermutation_preserving (n+1) (swapZero n j)).quasiMeasurePreserving.ae (prependProduct_ae n f u),
    htail] with k h₁ h₂ ht
  rw [h₁,h₂]
  simp only [coordinatePermutation_apply,swapZero_zero]
  congr 1
  have he : (fun i : Fin n => k (swapZero n j i.succ)) =
      coordinatePermutation n τ (fun i => k (j.succAbove i)) := by
    funext i
    rw [coordinatePermutation_apply,swapSpectatorOrder_apply]
  rw [he]
  simpa only [splitCoordinates_apply] using ht

lemma finite_lp_sum_ae {X I : Type*} [MeasurableSpace X] (μ : Measure X)
    (s : Finset I) (v : I → Lp ℂ 2 μ) :
    (∑ i ∈ s, v i) =ᵐ[μ] fun x => ∑ i ∈ s, v i x := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero ℂ 2 μ] with x hx
    exact hx
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (v i) (∑ j ∈ s,v j),ih] with x hx hs
    simp only [Pi.add_apply] at hx
    rw [hx,hs]

def creationAverage (n : ℕ) (f : Lp ℂ 2 (volume : Measure GW.Space)) (u : AmbientSector n) : AmbientSector (n+1) :=
  ((Real.sqrt (n+1 : ℕ) : ℝ) : ℂ) • symmetrizer (n+1) (prependProduct n f u)

lemma creationAverage_sum (n : ℕ) (f : Lp ℂ 2 (volume : Measure GW.Space))
    (u : AmbientSector n) (hu : u ∈ symmetricSector n) :
    creationAverage n f u = (((Real.sqrt (n+1 : ℕ) : ℝ) : ℂ)⁻¹) •
      ∑ j : Fin (n+1), permutationL2 (n+1) (swapZero n j) (prependProduct n f u) := by
  unfold creationAverage
  rw [symmetrizer_spectator_average n _ (prependProduct_fixed n f u hu),smul_smul]
  congr 1
  have h := congrArg (fun r : ℝ => (r : ℂ)) (creation_sqrt_coefficient n)
  push_cast at h
  simpa only [Nat.cast_add,Nat.cast_one] using h

lemma creationAverage_ae (n : ℕ) (f : Lp ℂ 2 (volume : Measure GW.Space))
    (u : AmbientSector n) (hu : u ∈ symmetricSector n) :
    creationAverage n f u =ᵐ[sectorMeasure (n+1)] fun k =>
      (((Real.sqrt (n+1 : ℕ) : ℝ) : ℂ)⁻¹) *
        ∑ j : Fin (n+1), f (k j) * u (fun i => k (j.succAbove i)) := by
  rw [creationAverage_sum n f u hu]
  filter_upwards [Lp.coeFn_smul (((Real.sqrt (n+1 : ℕ) : ℝ) : ℂ)⁻¹)
      (∑ j : Fin (n+1), permutationL2 (n+1) (swapZero n j) (prependProduct n f u)),
    finite_lp_sum_ae (sectorMeasure (n+1)) Finset.univ
      (fun j => permutationL2 (n+1) (swapZero n j) (prependProduct n f u)),
    ae_all_iff.mpr (fun j => swap_prependProduct_ae n j f u hu)] with k hs hsum hj
  simp only [Pi.smul_apply] at hs
  rw [hs,hsum,smul_eq_mul]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => hj j)

lemma vacuum_spectator_trivial (h : fixesZero 0) : h = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  exact (Fin.eq_zero _).trans (Fin.eq_zero i).symm

end GW.Fock
