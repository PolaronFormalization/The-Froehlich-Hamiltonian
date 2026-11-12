module
public import GW.Analysis.BridgeSymmetrizer
public import GW.Operators.BasicFree
public import GW.Fock.FockProductTensors
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ENNReal
namespace GW.Fock

section VectorPullback
variable {X Y E G : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  {μ : Measure X} {ν : Measure Y}

def vectorPullback (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν) :
    Lp E 2 ν ≃ₗᵢ[ℂ] Lp E 2 μ :=
  LinearIsometryEquiv.ofSurjective (Lp.compMeasurePreservingₗᵢ ℂ e he)
    (fun u => ⟨Lp.compMeasurePreserving e.symm (he.symm e) u, by
      change Lp.compMeasurePreserving e he (Lp.compMeasurePreserving e.symm (he.symm e) u) = u
      rw [← Lp.compMeasurePreserving_comp_apply]
      have h : (e.symm : Y → X) ∘ e = id := funext e.symm_apply_apply
      simp only [h,Lp.compMeasurePreserving_id_apply]⟩)

lemma vectorPullback_ae (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν) (u : Lp E 2 ν) :
    vectorPullback e he u =ᵐ[μ] fun x => u (e x) :=
  Lp.coeFn_compMeasurePreserving u he

lemma vectorPullback_amplify (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν)
    (F : E →L[ℂ] G) (u : Lp E 2 ν) :
    vectorPullback e he (amplify ν F u) = amplify μ F (vectorPullback e he u) := by
  apply Lp.ext
  filter_upwards [vectorPullback_ae e he (amplify ν F u),
    he.quasiMeasurePreserving.ae (amplify_ae ν F u), amplify_ae μ F (vectorPullback e he u),
    vectorPullback_ae e he u] with x h₁ h₂ h₃ h₄
  rw [h₁,h₃,h₄]
  exact h₂

end VectorPullback

section OuterPullback
variable {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {μ : Measure X} {ν : Measure Y} [SigmaFinite μ] [SigmaFinite ν]

lemma productUnitary_outerPullback (ρ : X ≃ᵐ X) (hρ : MeasurePreserving ρ μ μ)
    (u : Lp (Lp E 2 ν) 2 μ) :
    productUnitary μ ν (vectorPullback ρ hρ u) =
      Lp.compMeasurePreserving (Prod.map ρ id) (hρ.prod (MeasurePreserving.id ν))
        (productUnitary μ ν u) := by
  let R : Lp E 2 (μ.prod ν) →L[ℂ] Lp E 2 (μ.prod ν) :=
    (Lp.compMeasurePreservingₗᵢ ℂ (Prod.map ρ id) (hρ.prod (MeasurePreserving.id ν))).toContinuousLinearMap
  let U := productUnitary (E := E) μ ν
  have h : U.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((vectorPullback ρ hρ).toContinuousLinearEquiv.toContinuousLinearMap.comp
        U.symm.toContinuousLinearEquiv.toContinuousLinearMap) = R := by
    apply product_map_ext μ ν
    intro A B hA hB hAf hBf e
    let hf : (μ.prod ν) (A ×ˢ B) ≠ ∞ := by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hAf hBf
    have hA' := hA.preimage hρ.measurable
    have hAf' : μ (ρ ⁻¹' A) ≠ ∞ := by rwa [hρ.measure_preimage hA.nullMeasurableSet]
    have hi : U.symm (indicatorConstLp 2 (hA.prod hB) hf e) =
        indicatorConstLp 2 hA hAf (indicatorConstLp 2 hB hBf e) := by
      apply U.injective
      exact (U.apply_symm_apply _).trans (productUnitary_rectangle μ ν A B hA hB hAf hBf e).symm
    change productUnitary μ ν (vectorPullback ρ hρ (U.symm (indicatorConstLp 2 (hA.prod hB) hf e))) = _
    rw [hi]
    have houter : vectorPullback ρ hρ (indicatorConstLp 2 hA hAf (indicatorConstLp 2 hB hBf e)) =
        indicatorConstLp 2 hA' hAf' (indicatorConstLp 2 hB hBf e) :=
      Lp.indicatorConstLp_compMeasurePreserving hA hAf _ hρ
    rw [houter,productUnitary_rectangle]
    symm
    change Lp.compMeasurePreserving (Prod.map ρ id) (hρ.prod (MeasurePreserving.id ν)) _ = _
    rw [Lp.indicatorConstLp_compMeasurePreserving]
    apply indicatorLp_set_congr
    ext p; rfl
  have hv := congrArg (fun L => L (U u)) h
  change U (vectorPullback ρ hρ (U.symm (U u))) = _ at hv
  rw [U.symm_apply_apply] at hv
  exact hv

end OuterPullback

section SectorKernels
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
abbrev KernelSector (E : Type*) [NormedAddCommGroup E] (n : ℕ) := Lp E 2 (sectorMeasure n)
abbrev BosonKernel (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] :=
  E →L[ℂ] Lp E 2 (volume : Measure GW.Space)

def kernelSplit (n : ℕ) : KernelSector E (n+1) ≃ₗᵢ[ℂ]
    Lp (Lp E 2 (volume : Measure GW.Space)) 2 (sectorMeasure n) :=
  (vectorPullback (splitCoordinates n 0).symm (splitCoordinates_inverse_preserving n 0)).trans
    ((swapProduct volume (sectorMeasure n)).trans (productUnitary (sectorMeasure n) volume).symm)

def kernelCreationRaw (F : BosonKernel E) (n : ℕ) :
    KernelSector E n →L[ℂ] KernelSector E (n+1) :=
  (kernelSplit (E := E) n).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (amplify (sectorMeasure n) F)

def kernelAnnihilationRaw (F : BosonKernel E) (n : ℕ) :
    KernelSector E (n+1) →L[ℂ] KernelSector E n :=
  (amplify (sectorMeasure n) F.adjoint).comp
    (kernelSplit (E := E) n).toContinuousLinearEquiv.toContinuousLinearMap

lemma kernelCreationRaw_norm (F : BosonKernel E) (n : ℕ) : ‖kernelCreationRaw F n‖ ≤ ‖F‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (M := ‖F‖) F.opNorm_nonneg ?_
  intro u
  change ‖(kernelSplit (E := E) n).symm (amplify (sectorMeasure n) F u)‖ ≤ ‖F‖ * ‖u‖
  rw [LinearIsometryEquiv.norm_map]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (amplify_norm_le (sectorMeasure n) F) (norm_nonneg u))

lemma kernelAnnihilationRaw_norm (F : BosonKernel E) (n : ℕ) : ‖kernelAnnihilationRaw F n‖ ≤ ‖F‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (M := ‖F‖) F.opNorm_nonneg ?_
  intro u
  let v := kernelSplit (E := E) n u
  change ‖amplify (sectorMeasure n) F.adjoint v‖ ≤ ‖F‖ * ‖u‖
  calc
    _ ≤ ‖amplify (sectorMeasure n) F.adjoint‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖F.adjoint‖ * ‖v‖ := mul_le_mul_of_nonneg_right (amplify_norm_le (sectorMeasure n) F.adjoint) (norm_nonneg v)
    _ = _ := by rw [LinearIsometryEquiv.norm_map]; exact congrArg (‖F‖ * ·) ((kernelSplit (E := E) n).norm_map u)

lemma kernelRaw_pairing (F : BosonKernel E) (n : ℕ)
    (u : KernelSector E n) (v : KernelSector E (n+1)) :
    ⟪kernelCreationRaw F n u,v⟫_ℂ = ⟪u,kernelAnnihilationRaw F n v⟫_ℂ := by
  change ⟪(kernelSplit (E := E) n).symm (amplify (sectorMeasure n) F u),v⟫_ℂ =
    ⟪u,amplify (sectorMeasure n) F.adjoint (kernelSplit (E := E) n v)⟫_ℂ
  calc
    _ = ⟪amplify (sectorMeasure n) F u,kernelSplit (E := E) n v⟫_ℂ := by
      have h := (kernelSplit (E := E) n).inner_map_map
        ((kernelSplit (E := E) n).symm (amplify (sectorMeasure n) F u)) v
      rw [LinearIsometryEquiv.apply_symm_apply] at h
      exact h.symm
    _ = _ := by
      let T := amplify (sectorMeasure n) F
      let w := kernelSplit (E := E) n v
      calc
        _ = ⟪u,T.adjoint w⟫_ℂ := (T.adjoint_inner_right u w).symm
        _ = _ := congrArg (fun A : Lp (Lp E 2 volume) 2 (sectorMeasure n) →L[ℂ] KernelSector E n =>
          ⟪u,A w⟫_ℂ) (amplify_adjoint (sectorMeasure n) F)

def kernelPermutation (n : ℕ) (τ : Equiv.Perm (Fin n)) :
    KernelSector E n ≃ₗᵢ[ℂ] KernelSector E n :=
  vectorPullback (coordinatePermutation n τ) (coordinatePermutation_preserving n τ)

lemma kernelPermutation_ae (n : ℕ) (τ : Equiv.Perm (Fin n)) (u : KernelSector E n) :
    kernelPermutation n τ u =ᵐ[sectorMeasure n] fun k => u (coordinatePermutation n τ k) :=
  vectorPullback_ae _ _ _

def extendSpectator (n : ℕ) (τ : Equiv.Perm (Fin n)) : fixesZero n :=
  ⟨(finSuccEquiv n).trans (τ.optionCongr.trans (finSuccEquiv n).symm), by
    change ((finSuccEquiv n).trans (τ.optionCongr.trans (finSuccEquiv n).symm)) 0 = 0
    simp [Equiv.optionCongr]⟩

lemma extendSpectator_succ (n : ℕ) (τ : Equiv.Perm (Fin n)) (i : Fin n) :
    (extendSpectator n τ : Equiv.Perm (Fin (n+1))) i.succ = (τ i).succ := by
  simp [extendSpectator,Equiv.optionCongr]

lemma kernelSplit_spectator (n : ℕ) (τ : Equiv.Perm (Fin n)) (v : KernelSector E (n+1)) :
    kernelSplit n (kernelPermutation (n+1) (extendSpectator n τ) v) =
      vectorPullback (coordinatePermutation n τ) (coordinatePermutation_preserving n τ) (kernelSplit n v) := by
  let μ : Measure GW.Space := volume
  let ν := sectorMeasure n
  let e := (splitCoordinates n 0).symm
  let he := splitCoordinates_inverse_preserving n 0
  let ρ := coordinatePermutation n τ
  let hρ := coordinatePermutation_preserving n τ
  let P := productUnitary (E := E) ν μ
  let S := swapProduct (E := E) μ ν
  let V := vectorPullback (E := E) e he
  apply P.injective
  change P (P.symm (S (V (kernelPermutation (n+1) (extendSpectator n τ) v)))) =
    P (vectorPullback ρ hρ (P.symm (S (V v))))
  rw [P.apply_symm_apply,productUnitary_outerPullback,P.apply_symm_apply]
  have heq (p : Coordinates n × GW.Space) :
      coordinatePermutation (n+1) (extendSpectator n τ) (e p.swap) = e (p.2,ρ p.1) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · have hz := (extendSpectator n τ).property
      change (extendSpectator n τ : Equiv.Perm (Fin (n+1))) 0 = 0 at hz
      simp only [coordinatePermutation_apply,hz]
      exact (insertCoordinate_same n 0 p.2 p.1).trans (insertCoordinate_same n 0 p.2 (ρ p.1)).symm
    · simp only [coordinatePermutation_apply,extendSpectator_succ]
      change (splitCoordinates n 0).symm (p.2,p.1) ((τ j).succ) =
        (splitCoordinates n 0).symm (p.2,ρ p.1) j.succ
      calc
        _ = p.1 (τ j) := by simpa only [Fin.zero_succAbove] using insertCoordinate_succAbove n 0 p.2 p.1 (τ j)
        _ = ρ p.1 j := (coordinatePermutation_apply n τ p.1 j).symm
        _ = _ := by simpa only [Fin.zero_succAbove] using (insertCoordinate_succAbove n 0 p.2 (ρ p.1) j).symm
  have hp := hρ.prod (MeasurePreserving.id μ)
  have hs : MeasurePreserving (Prod.swap : Coordinates n × GW.Space → GW.Space × Coordinates n)
      (ν.prod μ) (μ.prod ν) := Measure.measurePreserving_swap
  have hve (w : KernelSector E (n+1)) : S (V w) =ᵐ[ν.prod μ] fun p => w (e p.swap) :=
    (swapProduct_ae μ ν (V w)).trans (hs.quasiMeasurePreserving.ae (vectorPullback_ae e he w))
  apply Lp.ext
  filter_upwards [hve (kernelPermutation (n+1) (extendSpectator n τ) v),
    (he.comp hs).quasiMeasurePreserving.ae (kernelPermutation_ae (n+1) (extendSpectator n τ) v),
    Lp.coeFn_compMeasurePreserving (S (V v)) hp,
    hp.quasiMeasurePreserving.ae (hve v)] with p h₁ h₂ h₃ h₄
  exact h₁.trans (h₂.trans ((congrArg (fun k => v k) (heq p)).trans
    (h₄.symm.trans h₃.symm)))

lemma kernelAnnihilation_spectator (F : BosonKernel E) (n : ℕ)
    (τ : Equiv.Perm (Fin n)) (v : KernelSector E (n+1)) :
    kernelAnnihilationRaw F n (kernelPermutation (n+1) (extendSpectator n τ) v) =
      kernelPermutation n τ (kernelAnnihilationRaw F n v) := by
  change amplify (sectorMeasure n) F.adjoint (kernelSplit n (kernelPermutation (n+1) (extendSpectator n τ) v)) =
    vectorPullback (coordinatePermutation n τ) (coordinatePermutation_preserving n τ)
      (amplify (sectorMeasure n) F.adjoint (kernelSplit n v))
  exact (congrArg (amplify (sectorMeasure n) F.adjoint) (kernelSplit_spectator n τ v)).trans
    (vectorPullback_amplify (coordinatePermutation n τ) (coordinatePermutation_preserving n τ)
      F.adjoint (kernelSplit n v)).symm

def kernelPermutationRepresentation (n : ℕ) :
    Equiv.Perm (Fin n) →* (KernelSector E n →L[ℂ] KernelSector E n) where
  toFun τ := (kernelPermutation n τ).toContinuousLinearEquiv.toContinuousLinearMap
  map_one' := by
    apply ContinuousLinearMap.ext
    intro u
    change kernelPermutation n 1 u = u
    apply Lp.ext
    filter_upwards [kernelPermutation_ae n 1 u] with k hk
    rw [hk]
    exact congrArg (fun z : Coordinates n => u z) (by
      funext i
      simp [coordinatePermutation_apply])
  map_mul' τ σ := by
    apply ContinuousLinearMap.ext
    intro u
    change kernelPermutation n (τ * σ) u = kernelPermutation n τ (kernelPermutation n σ u)
    apply Lp.ext
    filter_upwards [kernelPermutation_ae n (τ*σ) u,
      kernelPermutation_ae n τ (kernelPermutation n σ u),
      (coordinatePermutation_preserving n τ).quasiMeasurePreserving.ae (kernelPermutation_ae n σ u)]
      with k h₁ h₂ h₃
    rw [h₁,h₂,h₃]
    congr 1
    funext i
    simp [coordinatePermutation_apply,Equiv.Perm.mul_apply]

def kernelFixed (n : ℕ) : ClosedSubmodule ℂ (KernelSector E n) where
  toSubmodule := ⨅ τ : Equiv.Perm (Fin n),
    (kernelPermutationRepresentation (E := E) n τ - 1).ker
  isClosed' := by
    change IsClosed (((⨅ τ : Equiv.Perm (Fin n),
      (kernelPermutationRepresentation (E := E) n τ - 1).ker) :
      Submodule ℂ (KernelSector E n)) : Set (KernelSector E n))
    rw [Submodule.coe_iInf]
    exact isClosed_iInter (fun _ => ContinuousLinearMap.isClosed_ker _)

lemma mem_kernelFixed (n : ℕ) (u : KernelSector E n) :
    u ∈ kernelFixed n ↔ ∀ τ : Equiv.Perm (Fin n), kernelPermutation n τ u = u := by
  change u ∈ (⨅ τ : Equiv.Perm (Fin n), (kernelPermutationRepresentation (E := E) n τ - 1).ker) ↔ _
  rw [Submodule.mem_iInf]
  apply forall_congr'
  intro τ
  change kernelPermutation n τ u - u = 0 ↔ _
  exact sub_eq_zero

def kernelSymmetrizer (n : ℕ) : KernelSector E n →L[ℂ] KernelSector E n :=
  groupAverage (kernelPermutationRepresentation n)

lemma kernelSymmetrizer_mem (n : ℕ) (u : KernelSector E n) : kernelSymmetrizer n u ∈ kernelFixed n :=
  (mem_kernelFixed n _).mpr (fun τ =>
    congrArg (fun A : KernelSector E n →L[ℂ] KernelSector E n => A u)
      (element_mul_groupAverage (kernelPermutationRepresentation n) τ))

lemma kernelAnnihilationRaw_mem (F : BosonKernel E) (n : ℕ) (v : KernelSector E (n+1))
    (hv : v ∈ kernelFixed (n+1)) : kernelAnnihilationRaw F n v ∈ kernelFixed n := by
  apply (mem_kernelFixed n _).mpr
  intro τ
  rw [← kernelAnnihilation_spectator,(mem_kernelFixed _ _).mp hv (extendSpectator n τ)]

lemma kernelSymmetrizer_of_fixed (n : ℕ) (u : KernelSector E n) (hu : u ∈ kernelFixed n) :
    kernelSymmetrizer n u = u := by
  let G := Equiv.Perm (Fin n)
  have he (τ : G) : kernelPermutationRepresentation n τ u = u := (mem_kernelFixed n u).mp hu τ
  change groupAverage (kernelPermutationRepresentation n) u = u
  rw [groupAverage_apply]
  simp_rw [he]
  rw [Finset.sum_const,Finset.card_univ,← Nat.cast_smul_eq_nsmul ℂ,smul_smul]
  have hn : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [inv_mul_cancel₀ hn,one_smul]

lemma kernelPermutation_pairing (n : ℕ) (τ : Equiv.Perm (Fin n)) (u v : KernelSector E n) :
    ⟪kernelPermutation n τ u,v⟫_ℂ = ⟪u,kernelPermutation n τ⁻¹ v⟫_ℂ := by
  let R := kernelPermutationRepresentation (E := E) n
  have he : kernelPermutation n τ (kernelPermutation n τ⁻¹ v) = v := by
    change (R τ * R τ⁻¹) v = v
    rw [← map_mul,mul_inv_cancel,map_one]
    rfl
  have h := (kernelPermutation (E := E) n τ).inner_map_map u (kernelPermutation n τ⁻¹ v)
  rw [he] at h
  exact h

lemma kernelSymmetrizer_pairing (n : ℕ) (u v : KernelSector E n) :
    ⟪kernelSymmetrizer n u,v⟫_ℂ = ⟪u,kernelSymmetrizer n v⟫_ℂ := by
  change ⟪groupAverage (kernelPermutationRepresentation n) u,v⟫_ℂ =
    ⟪u,groupAverage (kernelPermutationRepresentation n) v⟫_ℂ
  rw [groupAverage_apply,groupAverage_apply,inner_smul_left,inner_smul_right,sum_inner,inner_sum]
  simp only [map_inv₀,map_natCast]
  congr 1
  change (∑ τ : Equiv.Perm (Fin n), ⟪kernelPermutation n τ u,v⟫_ℂ) =
    ∑ τ : Equiv.Perm (Fin n), ⟪u,kernelPermutation n τ v⟫_ℂ
  simp_rw [kernelPermutation_pairing]
  exact Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n))) _ _ (fun _ => rfl)

lemma kernelSymmetrizer_norm_le (n : ℕ) (u : KernelSector E n) :
    ‖kernelSymmetrizer n u‖ ≤ ‖u‖ := by
  let w := kernelSymmetrizer n u
  have h : ⟪w,w⟫_ℂ = ⟪u,w⟫_ℂ :=
    (kernelSymmetrizer_pairing n u w).trans
      (congrArg (fun z => ⟪u,z⟫_ℂ) (kernelSymmetrizer_of_fixed n w (kernelSymmetrizer_mem n u)))
  have hb : ‖w‖^2 ≤ ‖u‖ * ‖w‖ := by
    calc
      _ = (⟪w,w⟫_ℂ).re := norm_sq_eq_re_inner (𝕜 := ℂ) w
      _ = (⟪u,w⟫_ℂ).re := congrArg Complex.re h
      _ ≤ ‖⟪u,w⟫_ℂ‖ := Complex.re_le_norm _
      _ ≤ _ := norm_inner_le_norm _ _
  exact (show ‖w‖ ≤ ‖u‖ by nlinarith [norm_nonneg w,norm_nonneg u])

def kernelFixedInclusion (n : ℕ) :
    kernelFixed (E := E) n →ₗᵢ[ℂ] KernelSector E n :=
  (kernelFixed n).toSubmodule.subtypeₗᵢ

def kernelFixedProjection (n : ℕ) : KernelSector E n →L[ℂ] kernelFixed (E := E) n :=
  (kernelSymmetrizer n).codRestrict (kernelFixed n).toSubmodule (kernelSymmetrizer_mem n)

def kernelCreation (F : BosonKernel E) (n : ℕ) :
    kernelFixed (E := E) n →L[ℂ] kernelFixed (E := E) (n+1) :=
  (Real.sqrt (n+1 : ℕ) : ℂ) •
    ((kernelFixedProjection (n+1)).comp ((kernelCreationRaw F n).comp (kernelFixedInclusion n).toContinuousLinearMap))

def kernelAnnihilation (F : BosonKernel E) (n : ℕ) :
    kernelFixed (E := E) (n+1) →L[ℂ] kernelFixed (E := E) n :=
  (Real.sqrt (n+1 : ℕ) : ℂ) •
    (((kernelAnnihilationRaw F n).comp (kernelFixedInclusion (n+1)).toContinuousLinearMap).codRestrict
      (kernelFixed n).toSubmodule (fun v => kernelAnnihilationRaw_mem F n v v.property))

lemma kernelCreation_value (F : BosonKernel E) (n : ℕ) (u : kernelFixed (E := E) n) :
    (kernelCreation F n u : KernelSector E (n+1)) =
      (Real.sqrt (n+1 : ℕ) : ℂ) • kernelSymmetrizer (n+1) (kernelCreationRaw F n u) := rfl

lemma kernelAnnihilation_value (F : BosonKernel E) (n : ℕ) (v : kernelFixed (E := E) (n+1)) :
    (kernelAnnihilation F n v : KernelSector E n) =
      (Real.sqrt (n+1 : ℕ) : ℂ) • kernelAnnihilationRaw F n v := rfl

lemma kernelCreation_norm (F : BosonKernel E) (n : ℕ) :
    ‖kernelCreation F n‖ ≤ Real.sqrt (n+1 : ℕ) * ‖F‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Real.sqrt_nonneg _) F.opNorm_nonneg) ?_
  intro u
  change ‖(kernelCreation F n u : KernelSector E (n+1))‖ ≤ _ * ‖(u : KernelSector E n)‖
  rw [kernelCreation_value,norm_smul,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _),mul_assoc]
  refine mul_le_mul_of_nonneg_left ((kernelSymmetrizer_norm_le _ _).trans ?_) (Real.sqrt_nonneg _)
  exact ((kernelCreationRaw F n).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (kernelCreationRaw_norm F n) (norm_nonneg (u : KernelSector E n)))

lemma kernelAnnihilation_norm (F : BosonKernel E) (n : ℕ) :
    ‖kernelAnnihilation F n‖ ≤ Real.sqrt (n+1 : ℕ) * ‖F‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Real.sqrt_nonneg _) F.opNorm_nonneg) ?_
  intro v
  change ‖(kernelAnnihilation F n v : KernelSector E n)‖ ≤ _ * ‖(v : KernelSector E (n+1))‖
  rw [kernelAnnihilation_value,norm_smul,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _),mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  exact ((kernelAnnihilationRaw F n).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (kernelAnnihilationRaw_norm F n) (norm_nonneg (v : KernelSector E (n+1))))

lemma kernelCreation_pairing (F : BosonKernel E) (n : ℕ)
    (u : kernelFixed (E := E) n) (v : kernelFixed (E := E) (n+1)) :
    ⟪kernelCreation F n u,v⟫_ℂ = ⟪u,kernelAnnihilation F n v⟫_ℂ := by
  change ⟪(kernelCreation F n u : KernelSector E (n+1)),(v : KernelSector E (n+1))⟫_ℂ =
    ⟪(u : KernelSector E n),(kernelAnnihilation F n v : KernelSector E n)⟫_ℂ
  rw [kernelCreation_value,kernelAnnihilation_value,inner_smul_left,inner_smul_right,
    Complex.conj_ofReal,kernelSymmetrizer_pairing,kernelSymmetrizer_of_fixed _ _ v.property,kernelRaw_pairing]

lemma kernelAnnihilation_eq_adjoint (F : BosonKernel E) (n : ℕ) :
    kernelAnnihilation F n = (kernelCreation F n).adjoint :=
  (ContinuousLinearMap.eq_adjoint_iff _ _).mpr (by
    intro v u
    calc
      _ = starRingEnd ℂ ⟪u,kernelAnnihilation F n v⟫_ℂ := (inner_conj_symm _ _).symm
      _ = starRingEnd ℂ ⟪kernelCreation F n u,v⟫_ℂ :=
        congrArg (starRingEnd ℂ) (kernelCreation_pairing F n u v).symm
      _ = _ := inner_conj_symm _ _)

end SectorKernels

section KernelIdentification

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def isometryIntoSubmodule {H G : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup G] [NormedSpace ℂ G] (T : H →ₗᵢ[ℂ] G) (V : Submodule ℂ G)
    (h : ∀ u, T u ∈ V) : H →ₗᵢ[ℂ] V where
  toLinearMap := T.toLinearMap.codRestrict V h
  norm_map' := T.norm_map

def kernelVacuumIsometry : E →ₗᵢ[ℂ] KernelSector E 0 where
  toFun c := Lp.const 2 (sectorMeasure 0) c
  map_add' c d := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_const 2 (sectorMeasure 0) (c+d),
      Lp.coeFn_const 2 (sectorMeasure 0) c,Lp.coeFn_const 2 (sectorMeasure 0) d,
      Lp.coeFn_add (Lp.const 2 (sectorMeasure 0) c) (Lp.const 2 (sectorMeasure 0) d)]
      with k h₁ h₂ h₃ h₄
    exact h₁.trans ((congrArg₂ (· + ·) h₂ h₃).symm.trans h₄.symm)
  map_smul' c d := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_const 2 (sectorMeasure 0) (c • d),
      Lp.coeFn_const 2 (sectorMeasure 0) d,Lp.coeFn_smul c (Lp.const 2 (sectorMeasure 0) d)]
      with k h₁ h₂ h₃
    exact h₁.trans ((congrArg (c • ·) h₂).symm.trans h₃.symm)
  norm_map' c := by
    change ‖Lp.const 2 (sectorMeasure 0) c‖ = ‖c‖
    have h := Lp.norm_const' (p := (2 : ℝ≥0∞)) (μ := sectorMeasure 0) (c := c)
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    simpa [measureReal_def] using h

lemma kernelVacuum_ae (c : E) : kernelVacuumIsometry c =ᵐ[sectorMeasure 0] fun _ => c :=
  Lp.coeFn_const _ _ _

def kernelVacuum : E ≃ₗᵢ[ℂ] KernelSector E 0 :=
  LinearIsometryEquiv.ofSurjective kernelVacuumIsometry (fun u => ⟨u (fun i => Fin.elim0 i), by
    apply Lp.ext
    exact (kernelVacuum_ae _).trans
      (Filter.Eventually.of_forall (fun k => congrArg u (Subsingleton.elim _ k)))⟩)

lemma kernelVacuum_fixed (u : KernelSector E 0) : u ∈ kernelFixed 0 := by
  apply (mem_kernelFixed 0 _).mpr
  intro τ
  apply Lp.ext
  exact (kernelPermutation_ae 0 τ u).trans
    (Filter.Eventually.of_forall (fun k => congrArg u (Subsingleton.elim _ _)))

def kernelFixedVacuumIsometry : E →ₗᵢ[ℂ] kernelFixed (E := E) 0 :=
  isometryIntoSubmodule (kernelVacuumIsometry (E := E)) (kernelFixed 0).toSubmodule
    (fun u => kernelVacuum_fixed (kernelVacuumIsometry u))

lemma kernelFixedVacuum_surjective : Function.Surjective (kernelFixedVacuumIsometry (E := E)) := by
  intro v
  refine ⟨(kernelVacuum (E := E)).symm (v : KernelSector E 0), Subtype.ext ?_⟩
  change kernelVacuum ((kernelVacuum (E := E)).symm (v : KernelSector E 0)) = _
  exact (kernelVacuum (E := E)).apply_symm_apply _

def kernelFixedVacuum : E ≃ₗᵢ[ℂ] kernelFixed (E := E) 0 :=
  LinearIsometryEquiv.ofSurjective kernelFixedVacuumIsometry kernelFixedVacuum_surjective

lemma ordinaryKernelPermutation (n : ℕ) (τ : Equiv.Perm (Fin n)) (v : AmbientSector n) :
    kernelPermutation n τ v = permutationL2 n τ v := rfl

lemma ordinaryKernelFixed_iff (n : ℕ) (v : AmbientSector n) :
    v ∈ kernelFixed (E := ℂ) n ↔ v ∈ symmetricSector n := by
  rw [mem_kernelFixed]
  change (∀ τ, kernelPermutation n τ v = v) ↔ ∀ τ, permutationL2 n τ v = v
  simp only [ordinaryKernelPermutation]

def ordinarySectorKernel (n : ℕ) : Sector n ≃ₗᵢ[ℂ] kernelFixed (E := ℂ) n :=
  match n with
  | 0 => kernelFixedVacuum
  | n+1 => LinearIsometryEquiv.ofSurjective
      (isometryIntoSubmodule (sectorInclusion n) (kernelFixed (n+1)).toSubmodule
        (fun u => (ordinaryKernelFixed_iff _ _).mpr u.property))
      (fun v => ⟨⟨v,(ordinaryKernelFixed_iff _ _).mp v.property⟩,Subtype.ext rfl⟩)

abbrev ElectronL2 := Lp ℂ 2 (volume : Measure GW.Space)

def physicalKernelProduct (n : ℕ) :
    Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure n)) ≃ₗᵢ[ℂ] KernelSector ElectronL2 n :=
  (swapProduct volume (sectorMeasure n)).trans (productUnitary (sectorMeasure n) volume).symm

lemma physicalKernelProduct_permutation (n : ℕ) (τ : Equiv.Perm (Fin n))
    (v : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure n))) :
    physicalKernelProduct n (productPermutation volume n τ v) =
      kernelPermutation n τ (physicalKernelProduct n v) := by
  let μ : Measure GW.Space := volume
  let ν := sectorMeasure n
  let ρ := coordinatePermutation n τ
  let hρ := coordinatePermutation_preserving n τ
  let U := productUnitary (E := ℂ) ν μ
  let S := swapProduct (E := ℂ) μ ν
  apply U.injective
  change U (U.symm (S (productPermutation μ n τ v))) = U (vectorPullback ρ hρ (U.symm (S v)))
  rw [U.apply_symm_apply,productUnitary_outerPullback,U.apply_symm_apply]
  have hs : MeasurePreserving (Prod.swap : Coordinates n × GW.Space → GW.Space × Coordinates n)
      (ν.prod μ) (μ.prod ν) := Measure.measurePreserving_swap
  have hp := hρ.prod (MeasurePreserving.id μ)
  apply Lp.ext
  filter_upwards [swapProduct_ae μ ν (productPermutation μ n τ v),
    hs.quasiMeasurePreserving.ae (productPermutation_ae μ n τ v),
    Lp.coeFn_compMeasurePreserving (S v) hp,
    hp.quasiMeasurePreserving.ae (swapProduct_ae μ ν v)] with p h₁ h₂ h₃ h₄
  have he : (p.2, fun i => p.1 (τ i)) = (p.2, ρ p.1) :=
    Prod.ext rfl ((coordinatePermutation_eq n τ p.1).symm)
  exact h₁.trans (h₂.trans ((congrArg (fun q : GW.Space × Coordinates n => v q) he).trans
    (h₄.symm.trans h₃.symm)))

lemma physicalKernelProduct_fixed_iff (n : ℕ)
    (v : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure (n+1)))) :
    physicalKernelProduct (n+1) v ∈ kernelFixed (n+1) ↔
      v ∈ Set.range (electronSectorProduct n) := by
  rw [mem_kernelFixed,electronSectorProduct_range]
  constructor
  · intro h τ
    apply (physicalKernelProduct (n+1)).injective
    exact (physicalKernelProduct_permutation _ τ v).trans (h τ)
  · intro h τ
    exact (physicalKernelProduct_permutation _ τ v).symm.trans
      (congrArg (physicalKernelProduct (n+1)) (h τ))

def physicalPositiveKernelIsometry (n : ℕ) :
    ElectronSector (n+1) →ₗᵢ[ℂ] kernelFixed (E := ElectronL2) (n+1) :=
  isometryIntoSubmodule ((physicalKernelProduct (n+1)).toLinearIsometry.comp (electronSectorProduct n))
    (kernelFixed (n+1)).toSubmodule (fun v => (physicalKernelProduct_fixed_iff n _).mpr ⟨v,rfl⟩)

set_option maxHeartbeats 1800000 in
set_option backward.isDefEq.respectTransparency.types false in
lemma physicalPositiveKernel_surjective (n : ℕ) : Function.Surjective (physicalPositiveKernelIsometry n) := by
  intro v
  let P := physicalKernelProduct (n+1)
  let w := P.symm (v : KernelSector ElectronL2 (n+1))
  have hw : P w = (v : KernelSector ElectronL2 (n+1)) := P.apply_symm_apply _
  have hmem : P w ∈ kernelFixed (n+1) := hw.symm ▸ v.property
  obtain ⟨z,hz⟩ := (physicalKernelProduct_fixed_iff n w).mp hmem
  refine ⟨z,Subtype.ext ?_⟩
  change P (electronSectorProduct n z) = _
  exact (congrArg P hz).trans hw

def physicalSectorKernel (n : ℕ) : ElectronSector n ≃ₗᵢ[ℂ] kernelFixed (E := ElectronL2) n :=
  match n with
  | 0 => vacuumElectronIdentification.trans kernelFixedVacuum
  | n+1 => LinearIsometryEquiv.ofSurjective (physicalPositiveKernelIsometry n)
      (physicalPositiveKernel_surjective n)

end KernelIdentification

section MaximalSectorMap
variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℂ (E n)]

/-- The output family is specified first; its graph only includes actual square-summable outputs. -/
def sectorOutputGraph (W : lp E 2 →ₗ[ℂ] (∀ n, E n)) : Submodule ℂ (lp E 2 × lp E 2) where
  carrier := {p | ∀ n, p.2 n = W p.1 n}
  zero_mem' := by intro n; change (0 : lp E 2) n = W 0 n; rw [map_zero]; rfl
  add_mem' := by
    intro p q hp hq n
    change p.2 n + q.2 n = W (p.1 + q.1) n
    rw [map_add]
    exact congrArg₂ (· + ·) (hp n) (hq n)
  smul_mem' := by
    intro c p hp n
    change c • p.2 n = W (c • p.1) n
    rw [map_smul]
    exact congrArg (c • ·) (hp n)

lemma sectorOutputGraph_single_valued (W : lp E 2 →ₗ[ℂ] (∀ n, E n))
    (p : lp E 2 × lp E 2) (hp : p ∈ sectorOutputGraph W) (h0 : p.1 = 0) : p.2 = 0 := by
  apply lp.ext
  funext n
  have h : p.2 n = W p.1 n := hp n
  rw [h0,map_zero] at h
  exact h

def sectorOutputMap (W : lp E 2 →ₗ[ℂ] (∀ n, E n)) : lp E 2 →ₗ.[ℂ] lp E 2 :=
  (sectorOutputGraph W).toLinearPMap

lemma sectorOutputMap_graph (W : lp E 2 →ₗ[ℂ] (∀ n, E n)) :
    (sectorOutputMap W).graph = sectorOutputGraph W :=
  Submodule.toLinearPMap_graph_eq _ (sectorOutputGraph_single_valued W)

lemma sectorOutputMap_action (W : lp E 2 →ₗ[ℂ] (∀ n, E n)) (u : (sectorOutputMap W).domain)
    (n : ℕ) : sectorOutputMap W u n = W u n := by
  have h := (sectorOutputMap W).mem_graph u
  rw [sectorOutputMap_graph] at h
  exact h n

lemma sectorOutputMap_domain (W : lp E 2 →ₗ[ℂ] (∀ n, E n)) (u : lp E 2) :
    u ∈ (sectorOutputMap W).domain ↔ Summable (fun n => ‖W u n‖^2) := by
  rw [LinearPMap.mem_domain_iff]
  constructor
  · rintro ⟨v,hv⟩
    rw [sectorOutputMap_graph] at hv
    have he : (fun n => v n) = W u := funext (fun n => hv n)
    rw [← he]
    exact (GW.Analysis.memℓp_two_iff_sq _).mp v.property
  · intro h
    let v : lp E 2 := ⟨W u,(GW.Analysis.memℓp_two_iff_sq _).mpr h⟩
    exact ⟨v,(sectorOutputMap_graph W).symm ▸ (show (u,v) ∈ sectorOutputGraph W from fun _ => rfl)⟩

def creationSectorOutput (C : ∀ n, E n →L[ℂ] E (n+1)) : lp E 2 →ₗ[ℂ] (∀ n, E n) where
  toFun u := fun n => match n with | 0 => 0 | n+1 => C n (u n)
  map_add' u v := by
    funext n
    cases n with
    | zero => exact (zero_add (0 : E 0)).symm | succ n => exact map_add (C n) (u n) (v n)
  map_smul' c u := by
    funext n
    cases n with
    | zero => exact (smul_zero c).symm | succ n => exact map_smul (C n) c (u n)

def annihilationSectorOutput (A : ∀ n, E (n+1) →L[ℂ] E n) : lp E 2 →ₗ[ℂ] (∀ n, E n) where
  toFun u n := A n (u (n+1))
  map_add' u v := funext (fun n => map_add (A n) (u (n+1)) (v (n+1)))
  map_smul' c u := funext (fun n => map_smul (A n) c (u (n+1)))

def maximalSectorCreation (C : ∀ n, E n →L[ℂ] E (n+1)) : lp E 2 →ₗ.[ℂ] lp E 2 :=
  sectorOutputMap (creationSectorOutput C)

def maximalSectorAnnihilation (A : ∀ n, E (n+1) →L[ℂ] E n) : lp E 2 →ₗ.[ℂ] lp E 2 :=
  sectorOutputMap (annihilationSectorOutput A)

lemma maximalSectorCreation_domain (C : ∀ n, E n →L[ℂ] E (n+1)) (u : lp E 2) :
    u ∈ (maximalSectorCreation C).domain ↔ Summable (fun n => ‖C n (u n)‖^2) :=
  (sectorOutputMap_domain (creationSectorOutput C) u).trans (summable_nat_add_iff 1).symm

lemma maximalSectorAnnihilation_domain (A : ∀ n, E (n+1) →L[ℂ] E n) (u : lp E 2) :
    u ∈ (maximalSectorAnnihilation A).domain ↔ Summable (fun n => ‖A n (u (n+1))‖^2) :=
  sectorOutputMap_domain (annihilationSectorOutput A) u

lemma maximalSectorCreation_zero (C : ∀ n, E n →L[ℂ] E (n+1)) (u : (maximalSectorCreation C).domain) :
    maximalSectorCreation C u 0 = 0 := sectorOutputMap_action (creationSectorOutput C) u 0

lemma maximalSectorCreation_succ (C : ∀ n, E n →L[ℂ] E (n+1)) (u : (maximalSectorCreation C).domain) (n : ℕ) :
    maximalSectorCreation C u (n+1) = C n ((u : lp E 2) n) :=
  sectorOutputMap_action (creationSectorOutput C) u (n+1)

lemma maximalSectorAnnihilation_apply (A : ∀ n, E (n+1) →L[ℂ] E n)
    (u : (maximalSectorAnnihilation A).domain) (n : ℕ) :
    maximalSectorAnnihilation A u n = A n ((u : lp E 2) (n+1)) :=
  sectorOutputMap_action (annihilationSectorOutput A) u n

end MaximalSectorMap
section SectorTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {G : ℕ → Type*} [∀ n, NormedAddCommGroup (G n)] [∀ n, InnerProductSpace ℂ (G n)]
  (R : ∀ n, G n ≃ₗᵢ[ℂ] kernelFixed (E := E) n)

def sectorCreation (F : BosonKernel E) (n : ℕ) : G n →L[ℂ] G (n+1) :=
  (R (n+1)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((kernelCreation F n).comp (R n).toContinuousLinearEquiv.toContinuousLinearMap)

def sectorAnnihilation (F : BosonKernel E) (n : ℕ) : G (n+1) →L[ℂ] G n :=
  (R n).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((kernelAnnihilation F n).comp (R (n+1)).toContinuousLinearEquiv.toContinuousLinearMap)

lemma sectorCreation_norm (F : BosonKernel E) (n : ℕ) :
    ‖sectorCreation R F n‖ ≤ Real.sqrt (n+1 : ℕ) * ‖F‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Real.sqrt_nonneg _) F.opNorm_nonneg) ?_
  intro u
  change ‖(R (n+1)).symm (kernelCreation F n (R n u))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map,← (R n).norm_map u]
  exact ((kernelCreation F n).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (kernelCreation_norm F n) (norm_nonneg (R n u)))

lemma sectorAnnihilation_norm (F : BosonKernel E) (n : ℕ) :
    ‖sectorAnnihilation R F n‖ ≤ Real.sqrt (n+1 : ℕ) * ‖F‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Real.sqrt_nonneg _) F.opNorm_nonneg) ?_
  intro u
  change ‖(R n).symm (kernelAnnihilation F n (R (n+1) u))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map,← (R (n+1)).norm_map u]
  exact ((kernelAnnihilation F n).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (kernelAnnihilation_norm F n) (norm_nonneg (R (n+1) u)))

lemma sectorCreation_pairing (F : BosonKernel E) (n : ℕ) (u : G n) (v : G (n+1)) :
    ⟪sectorCreation R F n u,v⟫_ℂ = ⟪u,sectorAnnihilation R F n v⟫_ℂ := by
  have hc := (R (n+1)).inner_map_map (sectorCreation R F n u) v
  have ha := (R n).inner_map_map u (sectorAnnihilation R F n v)
  change ⟪R (n+1) ((R (n+1)).symm (kernelCreation F n (R n u))),R (n+1) v⟫_ℂ = _ at hc
  change ⟪R n u,R n ((R n).symm (kernelAnnihilation F n (R (n+1) v)))⟫_ℂ = _ at ha
  rw [LinearIsometryEquiv.apply_symm_apply] at hc ha
  exact hc.symm.trans ((kernelCreation_pairing F n (R n u) (R (n+1) v)).trans ha)

end SectorTransport

def generalizedCreationSector (F : BosonKernel ElectronL2) (n : ℕ) :
    ElectronSector n →L[ℂ] ElectronSector (n+1) := sectorCreation physicalSectorKernel F n

def generalizedAnnihilationSector (F : BosonKernel ElectronL2) (n : ℕ) :
    ElectronSector (n+1) →L[ℂ] ElectronSector n := sectorAnnihilation physicalSectorKernel F n

def generalizedCreation (F : BosonKernel ElectronL2) : Physical →ₗ.[ℂ] Physical :=
  representationTransport electronBosonUnitary.symm (maximalSectorCreation (generalizedCreationSector F))

def generalizedAnnihilation (F : BosonKernel ElectronL2) : Physical →ₗ.[ℂ] Physical :=
  representationTransport electronBosonUnitary.symm (maximalSectorAnnihilation (generalizedAnnihilationSector F))

lemma generalizedCreation_domain (F : BosonKernel ElectronL2) (u : Physical) :
    u ∈ (generalizedCreation F).domain ↔
      Summable (fun n => ‖generalizedCreationSector F n (electronBosonUnitary.symm u n)‖^2) :=
  maximalSectorCreation_domain (generalizedCreationSector F) (electronBosonUnitary.symm u)

lemma generalizedAnnihilation_domain (F : BosonKernel ElectronL2) (u : Physical) :
    u ∈ (generalizedAnnihilation F).domain ↔
      Summable (fun n => ‖generalizedAnnihilationSector F n (electronBosonUnitary.symm u (n+1))‖^2) :=
  maximalSectorAnnihilation_domain (generalizedAnnihilationSector F) (electronBosonUnitary.symm u)

lemma generalizedCreation_zero (F : BosonKernel ElectronL2) (u : (generalizedCreation F).domain) :
    electronBosonUnitary.symm (generalizedCreation F u) 0 = 0 := by
  exact (congrArg (fun z : ElectronBosonSum => z 0) (representationTransport_action _ _ u)).trans
    (maximalSectorCreation_zero _ (representationInput _ _ u))

lemma generalizedCreation_succ (F : BosonKernel ElectronL2) (u : (generalizedCreation F).domain) (n : ℕ) :
    electronBosonUnitary.symm (generalizedCreation F u) (n+1) =
      generalizedCreationSector F n (electronBosonUnitary.symm (u : Physical) n) := by
  exact (congrArg (fun z : ElectronBosonSum => z (n+1)) (representationTransport_action _ _ u)).trans
    (maximalSectorCreation_succ _ (representationInput _ _ u) n)

lemma generalizedAnnihilation_apply (F : BosonKernel ElectronL2) (u : (generalizedAnnihilation F).domain) (n : ℕ) :
    electronBosonUnitary.symm (generalizedAnnihilation F u) n =
      generalizedAnnihilationSector F n (electronBosonUnitary.symm (u : Physical) (n+1)) := by
  exact (congrArg (fun z : ElectronBosonSum => z n) (representationTransport_action _ _ u)).trans
    (maximalSectorAnnihilation_apply _ (representationInput _ _ u) n)

def ordinaryKernel (f : OneBoson) : BosonKernel ℂ := ContinuousLinearMap.toSpanSingleton ℂ f

def ordinaryCreation (f : OneBoson) : Carrier →ₗ.[ℂ] Carrier :=
  maximalSectorCreation (sectorCreation ordinarySectorKernel (ordinaryKernel f))

def ordinaryAnnihilation (f : OneBoson) : Carrier →ₗ.[ℂ] Carrier :=
  maximalSectorAnnihilation (sectorAnnihilation ordinarySectorKernel (ordinaryKernel f))

section VacuumAction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

lemma kernelVacuum_amplify {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (F : E →L[ℂ] G) (u : E) :
    amplify (sectorMeasure 0) F (kernelVacuum u) = kernelVacuum (F u) := by
  apply Lp.ext
  filter_upwards [amplify_ae (sectorMeasure 0) F (kernelVacuum u), kernelVacuum_ae u,
    kernelVacuum_ae (F u)] with k h₁ h₂ h₃
  exact h₁.trans ((congrArg F h₂).trans h₃.symm)

lemma kernelVacuum_product (v : Lp E 2 (volume : Measure GW.Space)) :
    productUnitary (sectorMeasure 0) volume (kernelVacuum v) =
      Lp.compMeasurePreserving Prod.snd (measurePreserving_snd (μ := sectorMeasure 0) (ν := volume)) v := by
  let μ : Measure GW.Space := volume
  let ν := sectorMeasure 0
  let f : Lp ℂ 2 ν := kernelVacuum (1 : ℂ)
  have hf : tensorEmbedding ν f v = kernelVacuum v := by
    apply Lp.ext
    change amplify ν (ContinuousLinearMap.toSpanSingleton ℂ v) f =ᵐ[ν] _
    filter_upwards [amplify_ae ν (ContinuousLinearMap.toSpanSingleton ℂ v) f,
      kernelVacuum_ae (1 : ℂ),kernelVacuum_ae v] with k h₁ h₂ h₃
    rw [h₁]
    change f k • v = kernelVacuum v k
    rw [show f k = 1 from h₂,one_smul]
    exact h₃.symm
  rw [← hf,productUnitary_tensor]
  apply Lp.ext
  filter_upwards [productFunction_ae ν μ f v,
    Lp.coeFn_compMeasurePreserving v (measurePreserving_snd (μ := ν) (ν := μ)),
    (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := μ)).ae (kernelVacuum_ae (1 : ℂ))]
    with p h₁ h₂ h₃
  rw [h₁]
  change f p.1 • v p.2 = _
  rw [show f p.1 = 1 from h₃,one_smul]
  exact h₂.symm

lemma kernelCreationRaw_vacuum (F : BosonKernel E) (u : E) :
    kernelCreationRaw F 0 (kernelVacuum u) = (kernelSplit (E := E) 0).symm (kernelVacuum (F u)) :=
  congrArg (kernelSplit (E := E) 0).symm (kernelVacuum_amplify F u)

lemma kernelAnnihilationRaw_vacuum (F : BosonKernel E) (v : Lp E 2 (volume : Measure GW.Space)) :
    kernelAnnihilationRaw F 0 ((kernelSplit (E := E) 0).symm (kernelVacuum v)) =
      kernelVacuum (F.adjoint v) := by
  change amplify (sectorMeasure 0) F.adjoint
    ((kernelSplit (E := E) 0) ((kernelSplit (E := E) 0).symm (kernelVacuum v))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact kernelVacuum_amplify F.adjoint v

lemma oneBosonCoordinate_preserving :
    MeasurePreserving (fun k : Coordinates 1 => k 0) (sectorMeasure 1) (volume : Measure GW.Space) :=
  (measurePreserving_fst (μ := (volume : Measure GW.Space)) (ν := sectorMeasure 0)).comp
    (splitCoordinates_preserving 0 0)

lemma kernelSplit_vacuum_one (v : Lp E 2 (volume : Measure GW.Space)) :
    (kernelSplit (E := E) 0).symm (kernelVacuum v) =
      Lp.compMeasurePreserving (fun k : Coordinates 1 => k 0) oneBosonCoordinate_preserving v := by
  let μ : Measure GW.Space := volume
  let ν := sectorMeasure 0
  let U := productUnitary (E := E) ν μ
  let S := swapProduct (E := E) μ ν
  let e := (splitCoordinates 0 0).symm
  let he := splitCoordinates_inverse_preserving 0 0
  let T := kernelSplit (E := E) 0
  let w := Lp.compMeasurePreserving (fun k : Coordinates 1 => k 0) oneBosonCoordinate_preserving v
  apply T.injective
  rw [T.apply_symm_apply]
  apply U.injective
  change U (kernelVacuum v) = U (U.symm (S (vectorPullback e he w)))
  rw [kernelVacuum_product,U.apply_symm_apply]
  have hs : MeasurePreserving (Prod.swap : Coordinates 0 × GW.Space → GW.Space × Coordinates 0)
      (ν.prod μ) (μ.prod ν) := Measure.measurePreserving_swap
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving v (measurePreserving_snd (μ := ν) (ν := μ)),
    swapProduct_ae μ ν (vectorPullback e he w),
    hs.quasiMeasurePreserving.ae (vectorPullback_ae e he w),
    (he.comp hs).quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving v oneBosonCoordinate_preserving)]
    with p h₁ h₂ h₃ h₄
  exact h₁.trans ((congrArg (fun k => v k) (insertCoordinate_same 0 0 p.2 p.1).symm).trans
    (h₄.symm.trans (h₃.symm.trans h₂.symm)))

lemma kernelFixed_one (v : KernelSector E 1) : v ∈ kernelFixed 1 := by
  apply (mem_kernelFixed 1 _).mpr
  intro τ
  apply Lp.ext
  filter_upwards [kernelPermutation_ae 1 τ v] with k hk
  exact hk.trans (congrArg (fun z : Coordinates 1 => v z) (by
    funext i
    rw [coordinatePermutation_apply]
    exact congrArg k (Subsingleton.elim _ _)))

def kernelOneBosonAmbient : Lp E 2 (volume : Measure GW.Space) ≃ₗᵢ[ℂ] KernelSector E 1 :=
  (kernelVacuum (E := Lp E 2 volume)).trans (kernelSplit (E := E) 0).symm

def kernelOneBosonIsometry : Lp E 2 (volume : Measure GW.Space) →ₗᵢ[ℂ] kernelFixed (E := E) 1 :=
  isometryIntoSubmodule (kernelOneBosonAmbient (E := E)).toLinearIsometry (kernelFixed 1).toSubmodule
    (fun v => kernelFixed_one _)

lemma kernelOneBoson_surjective : Function.Surjective (kernelOneBosonIsometry (E := E)) := by
  intro v
  let T := kernelOneBosonAmbient (E := E)
  refine ⟨T.symm (v : KernelSector E 1),Subtype.ext ?_⟩
  change T (T.symm (v : KernelSector E 1)) = _
  exact T.apply_symm_apply _

def kernelOneBoson : Lp E 2 (volume : Measure GW.Space) ≃ₗᵢ[ℂ] kernelFixed (E := E) 1 :=
  LinearIsometryEquiv.ofSurjective kernelOneBosonIsometry kernelOneBoson_surjective

lemma kernelOneBoson_coe (v : Lp E 2 (volume : Measure GW.Space)) :
    (kernelOneBoson v : KernelSector E 1) = (kernelSplit (E := E) 0).symm (kernelVacuum v) := rfl

lemma kernelFixedVacuum_coe (u : E) : (kernelFixedVacuum u : KernelSector E 0) = kernelVacuum u := rfl

lemma kernelCreation_vacuum (F : BosonKernel E) (u : E) :
    kernelCreation F 0 (kernelFixedVacuum u) = kernelOneBoson (F u) := by
  apply Subtype.ext
  rw [kernelCreation_value,kernelSymmetrizer_of_fixed _ _ (kernelFixed_one _),kernelFixedVacuum_coe,kernelOneBoson_coe]
  change (Real.sqrt (0+1 : ℕ) : ℂ) • kernelCreationRaw F 0 (kernelVacuum u) =
    (kernelSplit (E := E) 0).symm (kernelVacuum (F u))
  simpa using kernelCreationRaw_vacuum F u

lemma kernelAnnihilation_vacuum (F : BosonKernel E) (v : Lp E 2 (volume : Measure GW.Space)) :
    kernelAnnihilation F 0 (kernelOneBoson v) = kernelFixedVacuum (F.adjoint v) := by
  apply Subtype.ext
  rw [kernelAnnihilation_value,kernelOneBoson_coe,kernelFixedVacuum_coe]
  change (Real.sqrt (0+1 : ℕ) : ℂ) •
    kernelAnnihilationRaw F 0 ((kernelSplit (E := E) 0).symm (kernelVacuum v)) =
    kernelVacuum (F.adjoint v)
  simpa using kernelAnnihilationRaw_vacuum F v

end VacuumAction

set_option maxHeartbeats 1400000 in
set_option backward.isDefEq.respectTransparency.types false in
lemma ordinaryKernelCreationRaw (f : OneBoson) (n : ℕ) (u : AmbientSector n) :
    kernelCreationRaw (ordinaryKernel f) n u = prependProduct n f u := by
  let μ : Measure GW.Space := volume
  let ν := sectorMeasure n
  let S := swapProduct (E := ℂ) μ ν
  let U := productUnitary (E := ℂ) ν μ
  let V := splitUnitary n 0
  apply V.injective
  apply S.injective
  have he : S (V (kernelCreationRaw (ordinaryKernel f) n u)) =
      U (tensorEmbedding ν u f) := by
    have h : U.symm (S (V (kernelCreationRaw (ordinaryKernel f) n u))) = tensorEmbedding ν u f :=
      (kernelSplit (E := ℂ) n).apply_symm_apply (tensorEmbedding ν u f)
    exact ((U.apply_symm_apply _).symm.trans (congrArg U h))
  have hp : V (prependProduct n f u) = productFunction μ ν f u := V.apply_symm_apply _
  rw [he,hp,productUnitary_tensor]
  apply Lp.ext
  have hs : MeasurePreserving (Prod.swap : Coordinates n × GW.Space → GW.Space × Coordinates n)
      (ν.prod μ) (μ.prod ν) := Measure.measurePreserving_swap
  filter_upwards [productFunction_ae ν μ u f,swapProduct_ae μ ν (productFunction μ ν f u),
    hs.quasiMeasurePreserving.ae (productFunction_ae μ ν f u)] with p h₁ h₂ h₃
  exact h₁.trans ((mul_comm _ _).trans (h₃.symm.trans h₂.symm))

lemma ordinaryKernelSymmetrizer (n : ℕ) (u : AmbientSector n) :
    kernelSymmetrizer n u = symmetrizer n u := by
  change groupAverage (kernelPermutationRepresentation n) u = symmetrizer n u
  rw [groupAverage_apply,symmetrizer_apply,Fintype.card_perm,Fintype.card_fin]
  rfl

set_option maxHeartbeats 1400000 in
set_option backward.isDefEq.respectTransparency.types false in
lemma ordinaryCreationSector_ae (f : OneBoson) (n : ℕ) (u : Sector n) :
    ((sectorInclusion n (sectorCreation ordinarySectorKernel (ordinaryKernel f) n u) :
      AmbientSector (n+1)) : Coordinates (n+1) → ℂ) =ᵐ[sectorMeasure (n+1)] fun k =>
      (((Real.sqrt (n+1 : ℕ) : ℝ) : ℂ)⁻¹) *
        ∑ j : Fin (n+1), f (k j) * (↑(ordinarySectorKernel n u) : AmbientSector n)
          (fun i => k (j.succAbove i)) := by
  let v : AmbientSector n := (ordinarySectorKernel n u : kernelFixed (E := ℂ) n)
  have hv : v ∈ symmetricSector n := (ordinaryKernelFixed_iff n v).mp (ordinarySectorKernel n u).property
  have he : (sectorInclusion n (sectorCreation ordinarySectorKernel (ordinaryKernel f) n u)) =
      (kernelCreation (ordinaryKernel f) n (ordinarySectorKernel n u) : AmbientSector (n+1)) := by
    have h := (ordinarySectorKernel (n+1)).apply_symm_apply
      (kernelCreation (ordinaryKernel f) n (ordinarySectorKernel n u))
    exact congrArg (fun w : kernelFixed (E := ℂ) (n+1) => (w : AmbientSector (n+1))) h
  rw [he,kernelCreation_value,ordinaryKernelSymmetrizer,ordinaryKernelCreationRaw]
  exact creationAverage_ae n f v hv

def ordinaryElectronKernel (f : OneBoson) : BosonKernel ElectronL2 := tensorEmbedding volume f

lemma ordinaryElectronKernel_ae (f : OneBoson) (u : ElectronL2) :
    ordinaryElectronKernel f u =ᵐ[(volume : Measure GW.Space)] fun k => f k • u :=
  tensorEmbedding_ae volume f u

def electronOneBoson : Lp ElectronL2 2 (volume : Measure GW.Space) ≃ₗᵢ[ℂ] ElectronSector (0+1) :=
  kernelOneBoson.trans (physicalSectorKernel (0+1)).symm

lemma generalizedCreationSector_vacuum (F : BosonKernel ElectronL2) (u : ElectronSector 0) :
    generalizedCreationSector F 0 u = electronOneBoson (F (vacuumElectronIdentification u)) :=
  congrArg (physicalSectorKernel (0+1)).symm
    (kernelCreation_vacuum F (vacuumElectronIdentification u))

lemma generalizedAnnihilationSector_vacuum (F : BosonKernel ElectronL2)
    (v : Lp ElectronL2 2 (volume : Measure GW.Space)) :
    vacuumElectronIdentification (generalizedAnnihilationSector F 0 (electronOneBoson v)) = F.adjoint v := by
  let R := physicalSectorKernel (0+1)
  let V := kernelOneBoson (E := ElectronL2)
  let J := kernelFixedVacuum (E := ElectronL2)
  change J.symm (kernelAnnihilation F 0 (R (R.symm (V v)))) = _
  exact (congrArg (fun w => J.symm (kernelAnnihilation F 0 w)) (R.apply_symm_apply (V v))).trans
    ((congrArg J.symm (kernelAnnihilation_vacuum F v)).trans (J.symm_apply_apply _))

lemma ordinaryCreation_domain (f : OneBoson) (u : Carrier) :
    u ∈ (ordinaryCreation f).domain ↔
      Summable (fun n => ‖sectorCreation ordinarySectorKernel (ordinaryKernel f) n (u n)‖^2) :=
  maximalSectorCreation_domain _ _

lemma ordinaryAnnihilation_domain (f : OneBoson) (u : Carrier) :
    u ∈ (ordinaryAnnihilation f).domain ↔
      Summable (fun n => ‖sectorAnnihilation ordinarySectorKernel (ordinaryKernel f) n (u (n+1))‖^2) :=
  maximalSectorAnnihilation_domain _ _

lemma ordinaryCreation_zero (f : OneBoson) (u : (ordinaryCreation f).domain) :
    ordinaryCreation f u 0 = 0 := maximalSectorCreation_zero _ u

lemma ordinaryCreation_succ (f : OneBoson) (u : (ordinaryCreation f).domain) (n : ℕ) :
    ordinaryCreation f u (n+1) = sectorCreation ordinarySectorKernel (ordinaryKernel f) n ((u : Carrier) n) :=
  maximalSectorCreation_succ _ u n

lemma ordinaryAnnihilation_apply (f : OneBoson) (u : (ordinaryAnnihilation f).domain) (n : ℕ) :
    ordinaryAnnihilation f u n = sectorAnnihilation ordinarySectorKernel (ordinaryKernel f) n ((u : Carrier) (n+1)) :=
  maximalSectorAnnihilation_apply _ u n

end GW.Fock
