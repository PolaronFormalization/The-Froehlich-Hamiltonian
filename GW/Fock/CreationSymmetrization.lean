module
public import GW.Fock.FockGeneralized
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ENNReal
namespace GW.Fock
attribute [local instance] Classical.propDecidable

/-- The source finite spectator counting, including n=0. -/
def creationSpectatorEquiv (n : ℕ) : Equiv.Perm (Fin n) ≃ fixesZero n where
  toFun := extendSpectator n
  invFun := spectatorRestriction n
  left_inv τ := by
    apply Equiv.ext
    intro i
    apply Fin.succ_injective n
    exact (spectatorRestriction_apply n (extendSpectator n τ) i).symm.trans
      (extendSpectator_succ n τ i)
  right_inv h := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (extendSpectator n (spectatorRestriction n h)).property.trans h.property.symm
    · exact (extendSpectator_succ n (spectatorRestriction n h) j).trans
        (spectatorRestriction_apply n h j).symm

lemma creationSpectator_card (n : ℕ) : Fintype.card (fixesZero n) = n.factorial := by
  rw [← Fintype.card_congr (creationSpectatorEquiv n),Fintype.card_perm,Fintype.card_fin]

set_option maxHeartbeats 1000000 in
lemma creationRaw_spectator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (F : BosonKernel E) (n : ℕ) (τ : Equiv.Perm (Fin n)) (u : KernelSector E n) :
    kernelPermutation (n+1) (extendSpectator n τ) (kernelCreationRaw F n u) =
      kernelCreationRaw F n (kernelPermutation n τ u) := by
  have hsplit (v : KernelSector E n) :
      kernelSplit (E := E) n (kernelCreationRaw F n v) = amplify (sectorMeasure n) F v := by
    change (kernelSplit (E := E) n) ((kernelSplit (E := E) n).symm (amplify (sectorMeasure n) F v)) = _
    exact (kernelSplit (E := E) n).apply_symm_apply _
  apply (kernelSplit (E := E) n).injective
  rw [kernelSplit_spectator,hsplit,hsplit]
  exact vectorPullback_amplify (coordinatePermutation n τ) (coordinatePermutation_preserving n τ) F u

lemma creationRaw_ordinary_spectator (f : OneBoson) (n : ℕ)
    (τ : Equiv.Perm (Fin n)) (u : AmbientSector n) :
    permutationL2 (n+1) (extendSpectator n τ) (kernelCreationRaw (ordinaryKernel f) n u) =
      kernelCreationRaw (ordinaryKernel f) n (permutationL2 n τ u) :=
  creationRaw_spectator (ordinaryKernel f) n τ u

lemma creationRaw_spectator_average (f : OneBoson) (n : ℕ) (u : AmbientSector n) :
    kernelCreationRaw (ordinaryKernel f) n (symmetrizer n u) =
      groupAverage ((permutationRepresentation (n+1)).comp (fixesZero n).subtype)
        (kernelCreationRaw (ordinaryKernel f) n u) := by
  rw [symmetrizer_apply,map_smul,map_sum,groupAverage_apply,creationSpectator_card]
  congr 1
  apply Fintype.sum_equiv (creationSpectatorEquiv n)
  intro τ
  exact (creationRaw_ordinary_spectator f n τ u).symm

/-- Averaging over spectators and then all slots repeats each full permutation
with the same multiplicity, as required by the source bridge. -/
lemma creationRaw_symmetrizer_absorb (f : OneBoson) (n : ℕ) (u : AmbientSector n) :
    symmetrizer (n+1) (kernelCreationRaw (ordinaryKernel f) n (symmetrizer n u)) =
      symmetrizer (n+1) (kernelCreationRaw (ordinaryKernel f) n u) := by
  rw [creationRaw_spectator_average]
  exact congrArg (fun T : AmbientSector (n+1) →L[ℂ] AmbientSector (n+1) =>
    T (kernelCreationRaw (ordinaryKernel f) n u))
      (symmetrizer_subgroup_right (n+1) (fixesZero n))

lemma creationPrepend_symmetrizer_absorb (f : OneBoson) (n : ℕ) (u : AmbientSector n) :
    symmetrizer (n+1) (prependProduct n f (symmetrizer n u)) =
      symmetrizer (n+1) (prependProduct n f u) := by
  simpa only [ordinaryKernelCreationRaw] using creationRaw_symmetrizer_absorb f n u

lemma rawTensor_permutation (n : ℕ) (f : Fin n → OneBoson) (τ : Equiv.Perm (Fin n)) :
    permutationL2 n τ (rawTensor n f) = rawTensor n (fun i => f (τ.symm i)) := by
  apply Lp.ext
  filter_upwards [permutationL2_ae n τ (rawTensor n f),
    (coordinatePermutation_preserving n τ).quasiMeasurePreserving.ae (rawTensor_ae n f),
    rawTensor_ae n (fun i => f (τ.symm i))] with k h₁ h₂ h₃
  rw [h₁,h₂,h₃]
  simp only [rawTensorRep,coordinatePermutation_apply]
  exact Fintype.prod_equiv τ _ _ (fun i => by simp)

lemma creationPrepend_tensor (n : ℕ) (f : OneBoson) (h : Fin n → OneBoson) :
    prependProduct n f (rawTensor n h) = rawTensor (n+1) (Fin.cons f h) := by
  have he : rawPrepend n f (rawTensor n h) = prependProduct n f (rawTensor n h) := by
    change (splitUnitary n 0).symm (productUnitary volume (sectorMeasure n)
      (tensorEmbedding volume f (rawTensor n h))) = _
    rw [productUnitary_tensor]
    rfl
  rw [← he,rawPrepend_tensor]

lemma creationSymmetrizer_permutation_right (n : ℕ) (τ : Equiv.Perm (Fin n)) (u : AmbientSector n) :
    symmetrizer n (permutationL2 n τ u) = symmetrizer n u := by
  simp only [symmetrizer_apply,permutationL2_comp]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulRight τ) _ _ (fun _ => rfl)

/-- Source exchange of the two distinct created positions, first on product
vectors and then on each complete sector by boundedness. -/
lemma creationRaw_two_swap (n : ℕ) (f g : OneBoson) (u : AmbientSector n) :
    permutationL2 (n+2) (Equiv.swap 0 1)
      (kernelCreationRaw (ordinaryKernel f) (n+1) (kernelCreationRaw (ordinaryKernel g) n u)) =
    kernelCreationRaw (ordinaryKernel g) (n+1) (kernelCreationRaw (ordinaryKernel f) n u) := by
  let A := (permutationL2 (n+2) (Equiv.swap 0 1)).toContinuousLinearMap.comp
    ((kernelCreationRaw (ordinaryKernel f) (n+1)).comp (kernelCreationRaw (ordinaryKernel g) n))
  let B := (kernelCreationRaw (ordinaryKernel g) (n+1)).comp (kernelCreationRaw (ordinaryKernel f) n)
  have hker : LinearMap.ker (A-B).toLinearMap = ⊤ := by
    apply rawTensor_dense_criterion n _ (A-B).isClosed_ker
    intro h
    change A (rawTensor n h)-B (rawTensor n h) = 0
    apply sub_eq_zero.mpr
    change permutationL2 (n+2) (Equiv.swap 0 1)
        (kernelCreationRaw (ordinaryKernel f) (n+1)
          (kernelCreationRaw (ordinaryKernel g) n (rawTensor n h))) =
      kernelCreationRaw (ordinaryKernel g) (n+1)
        (kernelCreationRaw (ordinaryKernel f) n (rawTensor n h))
    simp only [ordinaryKernelCreationRaw,creationPrepend_tensor]
    rw [rawTensor_permutation]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
    · simp
    · simp
    · simp only [Equiv.symm_swap,Equiv.swap_apply_of_ne_of_ne
        (Fin.succ_ne_zero k.succ)
        (by
          intro he
          have hv := congrArg Fin.val he
          simp only [Fin.val_succ,Fin.val_one] at hv
          omega : k.succ.succ ≠ (1 : Fin (n+2))),Fin.cons_succ]
  have hu : u ∈ LinearMap.ker (A-B).toLinearMap := by rw [hker]; trivial
  exact sub_eq_zero.mp hu

lemma creationRaw_symmetrized_commute (n : ℕ) (f g : OneBoson) (u : AmbientSector n) :
    symmetrizer (n+2) (kernelCreationRaw (ordinaryKernel f) (n+1)
      (symmetrizer (n+1) (kernelCreationRaw (ordinaryKernel g) n u))) =
    symmetrizer (n+2) (kernelCreationRaw (ordinaryKernel g) (n+1)
      (symmetrizer (n+1) (kernelCreationRaw (ordinaryKernel f) n u))) := by
  rw [creationRaw_symmetrizer_absorb,creationRaw_symmetrizer_absorb]
  rw [← creationRaw_two_swap n f g u,creationSymmetrizer_permutation_right]

lemma creationKernel_commute (n : ℕ) (f g : OneBoson) (u : kernelFixed (E := ℂ) n) :
    kernelCreation (ordinaryKernel f) (n+1) (kernelCreation (ordinaryKernel g) n u) =
    kernelCreation (ordinaryKernel g) (n+1) (kernelCreation (ordinaryKernel f) n u) := by
  apply Subtype.ext
  simp only [kernelCreation_value,map_smul,ordinaryKernelSymmetrizer]
  rw [creationRaw_symmetrized_commute]

lemma creationSector_commute (n : ℕ) (f g : OneBoson) (u : Sector n) :
    sectorCreation ordinarySectorKernel (ordinaryKernel f) (n+1)
      (sectorCreation ordinarySectorKernel (ordinaryKernel g) n u) =
    sectorCreation ordinarySectorKernel (ordinaryKernel g) (n+1)
      (sectorCreation ordinarySectorKernel (ordinaryKernel f) n u) := by
  apply (ordinarySectorKernel (n+2)).injective
  simp only [sectorCreation,ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.apply_symm_apply]
  exact creationKernel_commute n f g (ordinarySectorKernel n u)

end GW.Fock
