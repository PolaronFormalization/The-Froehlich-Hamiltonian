module
public import GW.Fock.Bochner
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ENNReal
namespace GW.Fock
section WeightedPointwise
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
variable (E : ℕ → Type*) [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℂ (E n)]

/-- Actual weighted vector where it is square summable, zero elsewhere. -/
def weightedPointwise (a : ℕ → ℝ) (U : BochnerFock μ E) : X → lp E 2 :=
  GW.Analysis.dependentReconstruction (fun n x => (a n : ℂ) • U x n)

lemma weightedCoordinates_measurable (a : ℕ → ℝ) (U : BochnerFock μ E) (n : ℕ) :
    AEStronglyMeasurable (fun x => (a n : ℂ) • U x n) μ :=
  (((lp.evalCLM ℂ E 2 n).continuous.comp_stronglyMeasurable (Lp.stronglyMeasurable U)).const_smul _).aestronglyMeasurable

lemma weightedPointwise_apply (a : ℕ → ℝ) (U : BochnerFock μ E) (x : X)
    (hx : U x ∈ (scalarDiagonal E a).domain) (n : ℕ) :
    weightedPointwise μ E a U x n = (a n : ℂ) • U x n := by
  change Memℓp (fun n => (a n : ℂ) • U x n) 2 at hx
  exact GW.Analysis.reconstruction_apply (fun n x => (a n : ℂ) • U x n) hx n

lemma weightedPointwise_zero (a : ℕ → ℝ) (U : BochnerFock μ E) (x : X)
    (hx : U x ∉ (scalarDiagonal E a).domain) : weightedPointwise μ E a U x = 0 := by
  change ¬ Memℓp (fun n => (a n : ℂ) • U x n) 2 at hx
  change GW.Analysis.dependentReconstruction _ x = 0
  simp only [GW.Analysis.dependentReconstruction, dite_eq_right hx]

lemma weightedPointwise_norm (a : ℕ → ℝ) (U : BochnerFock μ E)
    (hU : ∀ᵐ x ∂μ, U x ∈ (scalarDiagonal E a).domain) :
    (fun x => ‖weightedPointwise μ E a U x‖^2) =ᵐ[μ]
      fun x => ∑' n, ‖(a n : ℂ) • U x n‖^2 := by
  filter_upwards [hU] with x hx
  rw [GW.Analysis.lp_norm_sq]
  exact tsum_congr (fun n => congrArg (fun v : E n => ‖v‖^2) (weightedPointwise_apply μ E a U x hx n))

lemma weightedPointwise_lintegral (a : ℕ → ℝ) (U : BochnerFock μ E)
    (hU : ∀ᵐ x ∂μ, U x ∈ (scalarDiagonal E a).domain) :
    (∫⁻ x, ENNReal.ofReal (‖weightedPointwise μ E a U x‖^2) ∂μ) =
      ∑' n, ∫⁻ x, ENNReal.ofReal (‖(a n : ℂ) • U x n‖^2) ∂μ := by
  calc
    _ = ∫⁻ x, ∑' n, ENNReal.ofReal (‖(a n : ℂ) • U x n‖^2) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hU,weightedPointwise_norm μ E a U hU] with x hx he
      rw [he]
      exact ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _)
        ((GW.Analysis.memℓp_two_iff_sq _).mp hx)
    _ = _ := lintegral_tsum (fun n => ((weightedCoordinates_measurable μ E a U n).norm.pow 2).aemeasurable.ennreal_ofReal)

lemma bochnerDiagonal_fiber_criterion (a : ℕ → ℝ) (U : BochnerFock μ E) :
    U ∈ (bochnerDiagonal μ E a).domain ↔
      (∀ᵐ x ∂μ, U x ∈ (scalarDiagonal E a).domain) ∧
        (∫⁻ x, ENNReal.ofReal (‖weightedPointwise μ E a U x‖^2) ∂μ) < ∞ := by
  constructor
  · intro hU
    obtain ⟨V,hV⟩ := (bochnerDiagonal_domain_iff_graph μ E a U).mp hU
    have hm : ∀ᵐ x ∂μ, U x ∈ (scalarDiagonal E a).domain := hV.mono (fun x hx => by
      obtain ⟨u,hu,hv⟩ := (scalarDiagonal E a).mem_graph_iff.mp hx
      change (u : lp E 2) = U x at hu
      exact hu ▸ u.property)
    refine ⟨hm,?_⟩
    have he : weightedPointwise μ E a U =ᵐ[μ] V := by
      filter_upwards [hm,hV] with x hx hv
      apply lp.ext
      funext n
      exact (weightedPointwise_apply μ E a U x hx n).trans
        (((scalarDiagonal_graph_iff E a (U x,V x)).mp hv n).symm)
    have hi : Integrable (fun x => ‖V x‖^2) μ := by
      have h := (Lp.memLp V).norm_rpow two_ne_zero ENNReal.ofNat_ne_top
      simpa only [ENNReal.toReal_ofNat,Real.rpow_two,memLp_one_iff_integrable] using h
    rw [lintegral_congr_ae (he.mono (fun _ hx => congrArg (fun v : lp E 2 => ENNReal.ofReal (‖v‖^2)) hx))]
    exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun _ => sq_nonneg _))).mp hi.2
  · rintro ⟨hm,hf⟩
    rw [weightedPointwise_lintegral μ E a U hm] at hf
    let V := GW.Analysis.reconstructionL2 (weightedCoordinates_measurable μ E a U) hf
    apply (bochnerDiagonal_domain_iff_coordinates μ E a U).mpr
    exact ⟨V,GW.Analysis.reconstructionL2_coordinates (weightedCoordinates_measurable μ E a U) hf⟩

lemma weightedPointwise_memLp (a : ℕ → ℝ) (U : BochnerFock μ E)
    (hU : ∀ᵐ x ∂μ, U x ∈ (scalarDiagonal E a).domain)
    (hf : (∫⁻ x, ENNReal.ofReal (‖weightedPointwise μ E a U x‖^2) ∂μ) < ∞) :
    MemLp (weightedPointwise μ E a U) 2 μ := by
  rw [weightedPointwise_lintegral μ E a U hU] at hf
  exact GW.Analysis.reconstruction_memLp (weightedCoordinates_measurable μ E a U) hf

lemma weightedPointwise_strong_representative (a : ℕ → ℝ) (U : BochnerFock μ E)
    (hU : ∀ᵐ x ∂μ, U x ∈ (scalarDiagonal E a).domain)
    (hf : (∫⁻ x, ENNReal.ofReal (‖weightedPointwise μ E a U x‖^2) ∂μ) < ∞) :
    ∃ g : X → lp E 2, StronglyMeasurable g ∧ weightedPointwise μ E a U =ᵐ[μ] g :=
  GW.Analysis.l2_strong_representative (weightedPointwise_memLp μ E a U hU hf).aestronglyMeasurable

def bochnerReciprocal (a : ℕ → ℝ) (ha : ∀ n, 1 ≤ a n) : BochnerFock μ E →L[ℂ] BochnerFock μ E :=
  (bochnerUnitary μ E).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((scalarReciprocal (fun n => Lp (E n) 2 μ) a ha).comp
      (bochnerUnitary μ E).symm.toContinuousLinearEquiv.toContinuousLinearMap)

lemma bochnerReciprocal_norm (a : ℕ → ℝ) (ha : ∀ n, 1 ≤ a n) :
    ‖bochnerReciprocal μ E a ha‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro U
  change ‖bochnerUnitary μ E (scalarReciprocal (fun n => Lp (E n) 2 μ) a ha
    ((bochnerUnitary μ E).symm U))‖ ≤ 1*‖U‖
  rw [LinearIsometryEquiv.norm_map,one_mul]
  calc
    _ ≤ ‖scalarReciprocal (fun n => Lp (E n) 2 μ) a ha‖ * ‖(bochnerUnitary μ E).symm U‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1*‖(bochnerUnitary μ E).symm U‖ :=
      mul_le_mul_of_nonneg_right (scalarReciprocal_norm _ a ha) (norm_nonneg _)
    _ = ‖U‖ := by rw [one_mul,LinearIsometryEquiv.norm_map]

lemma bochnerReciprocal_mem (a : ℕ → ℝ) (ha : ∀ n, 1 ≤ a n) (U : BochnerFock μ E) :
    bochnerReciprocal μ E a ha U ∈ (bochnerDiagonal μ E a).domain := by
  change (bochnerUnitary μ E).symm (bochnerUnitary μ E
    (scalarReciprocal (fun n => Lp (E n) 2 μ) a ha ((bochnerUnitary μ E).symm U))) ∈
      (scalarDiagonal (fun n => Lp (E n) 2 μ) a).domain
  rw [LinearIsometryEquiv.symm_apply_apply]
  exact scalarReciprocal_mem _ a ha _

lemma bochnerDiagonal_reciprocal (a : ℕ → ℝ) (ha : ∀ n, 1 ≤ a n) (U : BochnerFock μ E) :
    bochnerDiagonal μ E a ⟨bochnerReciprocal μ E a ha U,bochnerReciprocal_mem μ E a ha U⟩ = U := by
  have h := bochnerDiagonal_intertwines μ E a
    ⟨scalarReciprocal (fun n => Lp (E n) 2 μ) a ha ((bochnerUnitary μ E).symm U),
      scalarReciprocal_mem _ a ha _⟩
  exact h.trans (by rw [scalarDiagonal_reciprocal,LinearIsometryEquiv.apply_symm_apply])

lemma bochnerReciprocal_diagonal (a : ℕ → ℝ) (ha : ∀ n, 1 ≤ a n)
    (U : (bochnerDiagonal μ E a).domain) :
    bochnerReciprocal μ E a ha (bochnerDiagonal μ E a U) = (U : BochnerFock μ E) := by
  change bochnerUnitary μ E (scalarReciprocal (fun n => Lp (E n) 2 μ) a ha
    ((bochnerUnitary μ E).symm (bochnerUnitary μ E
      (scalarDiagonal (fun n => Lp (E n) 2 μ) a (bochnerDiagonalInput μ E a U))))) = _
  rw [LinearIsometryEquiv.symm_apply_apply,scalarReciprocal_diagonal]
  exact (bochnerUnitary μ E).apply_symm_apply (U : BochnerFock μ E)

lemma bochnerReciprocal_injective (a : ℕ → ℝ) (ha : ∀ n, 1 ≤ a n) :
    Function.Injective (bochnerReciprocal μ E a ha) := by
  intro U V he
  apply (bochnerUnitary μ E).symm.injective
  apply scalarReciprocal_injective (fun n => Lp (E n) 2 μ) a ha
  exact (bochnerUnitary μ E).injective he

lemma bochnerReciprocal_range (a : ℕ → ℝ) (ha : ∀ n, 1 ≤ a n) :
    Set.range (bochnerReciprocal μ E a ha) = ((bochnerDiagonal μ E a).domain : Set (BochnerFock μ E)) := by
  ext U
  constructor
  · rintro ⟨V,rfl⟩
    exact bochnerReciprocal_mem μ E a ha V
  · intro hU
    exact ⟨bochnerDiagonal μ E a ⟨U,hU⟩,bochnerReciprocal_diagonal μ E a ha ⟨U,hU⟩⟩

lemma bochnerDiagonal_dense (a : ℕ → ℝ) : Dense ((bochnerDiagonal μ E a).domain : Set (BochnerFock μ E)) := by
  intro U
  have ht := (bochnerUnitary μ E).continuous.tendsto ((bochnerUnitary μ E).symm U) |>.comp
    (cutoff_tendsto (fun n => Lp (E n) 2 μ) ((bochnerUnitary μ E).symm U))
  have ht' : Tendsto (fun m => bochnerUnitary μ E
      (cutoff (fun n => Lp (E n) 2 μ) m ((bochnerUnitary μ E).symm U))) atTop (𝓝 U) := by
    simpa only [LinearIsometryEquiv.apply_symm_apply,Function.comp_def] using ht
  apply mem_closure_of_tendsto ht'
  exact Eventually.of_forall (fun m => bochnerDiagonal_unitary_mem μ E a
    ⟨_,scalarDiagonal_cutoff_mem _ a m _⟩)

/-- Named copy of the original physical L² space with its original Hilbert norm. -/
def BochnerGraphCarrier (_a : ℕ → ℝ) : Type _ := BochnerFock μ E
instance bochnerGraphNorm (a : ℕ → ℝ) : NormedAddCommGroup (BochnerGraphCarrier μ E a) :=
  inferInstanceAs (NormedAddCommGroup (BochnerFock μ E))
instance bochnerGraphInner (a : ℕ → ℝ) : InnerProductSpace ℂ (BochnerGraphCarrier μ E a) :=
  inferInstanceAs (InnerProductSpace ℂ (BochnerFock μ E))
instance bochnerGraphComplete (a : ℕ → ℝ) [∀ n, CompleteSpace (E n)] :
    CompleteSpace (BochnerGraphCarrier μ E a) := inferInstanceAs (CompleteSpace (BochnerFock μ E))

def bochnerWeightedGraph (a : ℕ → ℝ) (ha : ∀ n, 1 ≤ a n) :
    GW.Spaces.WeightedGraph (BochnerFock μ E) (BochnerGraphCarrier μ E a) where
  domain := (bochnerDiagonal μ E a).domain
  embedding := bochnerReciprocal μ E a ha
  embedding_injective := bochnerReciprocal_injective μ E a ha
  embedding_norm_le := bochnerReciprocal_norm μ E a ha
  embedding_dense := by
    change Dense (Set.range (bochnerReciprocal μ E a ha))
    rw [bochnerReciprocal_range]
    exact bochnerDiagonal_dense μ E a
  product := (bochnerDiagonal μ E a).toFun
  embedding_mem := bochnerReciprocal_mem μ E a ha
  product_embedding := bochnerDiagonal_reciprocal μ E a ha
  embedding_product := bochnerReciprocal_diagonal μ E a ha

abbrev BochnerWeightedDomain (a : ℕ → ℝ) (ha : ∀ n, 1 ≤ a n) :=
  GW.Spaces.WeightedDomain (bochnerWeightedGraph μ E a ha)

lemma bochnerDiagonal_pointwise (a : ℕ → ℝ) (U : (bochnerDiagonal μ E a).domain) :
    weightedPointwise μ E a U =ᵐ[μ] bochnerDiagonal μ E a U := by
  have hm := (bochnerDiagonal_fiber_criterion μ E a U).mp U.property |>.1
  filter_upwards [hm,bochnerDiagonal_coordinates μ E a U] with x hx hc
  apply lp.ext
  funext n
  exact (weightedPointwise_apply μ E a U x hx n).trans (hc n).symm

set_option backward.isDefEq.respectTransparency.types false in
lemma bochnerWeighted_norm_integral (a : ℕ → ℝ) (ha : ∀ n, 1 ≤ a n)
    (U : BochnerWeightedDomain μ E a ha) :
    ‖U‖^2 = ∫ x, ‖weightedPointwise μ E a
      (show BochnerFock μ E from (show (bochnerWeightedGraph μ E a ha).domain from U)) x‖^2 ∂μ := by
  rw [GW.Spaces.weightedDomain_norm]
  change ‖bochnerDiagonal μ E a U‖^2 = _
  rw [GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
  apply integral_congr_ae
  exact (bochnerDiagonal_pointwise μ E a U).symm.mono (fun _ hx => congrArg (fun v : lp E 2 => ‖v‖^2) hx)

set_option backward.isDefEq.respectTransparency.types false in
lemma bochnerWeighted_norm_series (a : ℕ → ℝ) (ha : ∀ n, 1 ≤ a n)
    (U : BochnerWeightedDomain μ E a ha) :
    ‖U‖^2 = ∑' n, a n^2 * ‖bochnerCoordinate μ E n
      (show BochnerFock μ E from (show (bochnerWeightedGraph μ E a ha).domain from U))‖^2 := by
  rw [GW.Spaces.weightedDomain_norm]
  change ‖bochnerUnitary μ E
    (scalarDiagonal (fun n => Lp (E n) 2 μ) a (bochnerDiagonalInput μ E a U))‖^2 = _
  rw [LinearIsometryEquiv.norm_map,scalarDiagonal_norm_sq]
  apply tsum_congr
  intro n
  change a n^2 * ‖((bochnerUnitary μ E).symm
    (show BochnerFock μ E from (show (bochnerWeightedGraph μ E a ha).domain from U))) n‖^2 = _
  rw [bochnerUnitary_symm_coordinate]

def numberDomainInclusion (r : ℝ) (hr : 0 ≤ r) : NumberWeightedDomain E r hr →L[ℂ] lp E 2 :=
  (numberWeightedGraph E r hr).embedding.comp
    (numberDomainIsometry E r hr).toContinuousLinearEquiv.toContinuousLinearMap

lemma numberDomainInclusion_apply (r : ℝ) (hr : 0 ≤ r) (u : NumberWeightedDomain E r hr) :
    numberDomainInclusion E r hr u =
      (show lp E 2 from (show (numberWeightedGraph E r hr).domain from u)) :=
  (numberWeightedGraph E r hr).embedding_product _

lemma numberDomainInclusion_reciprocal (r : ℝ) (hr : 0 ≤ r) (v : lp E 2) :
    numberDomainInclusion E r hr (numberReciprocalIsometry E r hr v) =
      scalarReciprocal E (fun n => ((n : ℝ)+1)^r) (shiftedNumber_weight_one r hr) v := by
  rw [numberDomainInclusion_apply]
  exact numberReciprocalIsometry_ambient E r hr v

abbrev PhysicalNumberWeightedDomain (r : ℝ) (hr : 0 ≤ r) :=
  BochnerWeightedDomain μ E (fun n => ((n : ℝ)+1)^r) (shiftedNumber_weight_one r hr)

def numberGraphIncludeL2 (r : ℝ) (hr : 0 ≤ r) :
    Lp (NumberWeightedDomain E r hr) 2 μ →L[ℂ] BochnerFock μ E :=
  (numberDomainInclusion E r hr).compLpL 2 μ

def numberGraphProductL2 (r : ℝ) (hr : 0 ≤ r) :
    Lp (NumberWeightedDomain E r hr) 2 μ →L[ℂ] BochnerFock μ E :=
  (numberDomainIsometry E r hr).toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 μ

set_option backward.isDefEq.respectTransparency.types false in
lemma numberGraphInclude_mem (r : ℝ) (hr : 0 ≤ r) (G : Lp (NumberWeightedDomain E r hr) 2 μ) :
    numberGraphIncludeL2 μ E r hr G ∈ (bochnerShiftedNumberPower μ E r).domain := by
  apply (bochnerDiagonal_domain_iff_coordinates μ E (fun n => ((n : ℝ)+1)^r) _).mpr
  refine ⟨numberGraphProductL2 μ E r hr G,?_⟩
  filter_upwards [(numberDomainInclusion E r hr).coeFn_compLp G,
    (numberDomainIsometry E r hr).toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp G] with x hi hp
  change numberGraphIncludeL2 μ E r hr G x = numberDomainInclusion E r hr (G x) at hi
  change numberGraphProductL2 μ E r hr G x =
    (show lp E 2 from numberDomainIsometry E r hr (G x)) at hp
  intro n
  rw [hi,hp,numberDomainInclusion_apply]
  exact scalarDiagonal_apply E (fun n => ((n : ℝ)+1)^r) _ n

set_option backward.isDefEq.respectTransparency.types false in
lemma numberGraphInclude_product (r : ℝ) (hr : 0 ≤ r) (G : Lp (NumberWeightedDomain E r hr) 2 μ) :
    bochnerShiftedNumberPower μ E r ⟨numberGraphIncludeL2 μ E r hr G,numberGraphInclude_mem μ E r hr G⟩ =
      numberGraphProductL2 μ E r hr G := by
  apply Lp.ext
  filter_upwards [bochnerDiagonal_coordinates μ E (fun n => ((n : ℝ)+1)^r)
    ⟨numberGraphIncludeL2 μ E r hr G,numberGraphInclude_mem μ E r hr G⟩,
    (numberDomainInclusion E r hr).coeFn_compLp G,
    (numberDomainIsometry E r hr).toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp G] with x hc hi hp
  change numberGraphIncludeL2 μ E r hr G x = numberDomainInclusion E r hr (G x) at hi
  change numberGraphProductL2 μ E r hr G x =
    (show lp E 2 from numberDomainIsometry E r hr (G x)) at hp
  apply lp.ext
  funext n
  change (bochnerDiagonal μ E (fun n => ((n : ℝ)+1)^r)
    ⟨numberGraphIncludeL2 μ E r hr G,numberGraphInclude_mem μ E r hr G⟩) x n = _
  rw [hc n,hi,hp,numberDomainInclusion_apply]
  exact (scalarDiagonal_apply E (fun n => ((n : ℝ)+1)^r) _ n).symm

set_option backward.isDefEq.respectTransparency.types false in
def numberGraphBochnerLinear (r : ℝ) (hr : 0 ≤ r) :
    Lp (NumberWeightedDomain E r hr) 2 μ →ₗ[ℂ] PhysicalNumberWeightedDomain μ E r hr where
  toFun G := show (bochnerShiftedNumberPower μ E r).domain from
    ⟨numberGraphIncludeL2 μ E r hr G,numberGraphInclude_mem μ E r hr G⟩
  map_add' G H := by apply Subtype.ext;exact map_add _ _ _
  map_smul' c G := by apply Subtype.ext;exact map_smul _ _ _

set_option backward.isDefEq.respectTransparency.types false in
lemma numberGraphBochner_norm (r : ℝ) (hr : 0 ≤ r) (G : Lp (NumberWeightedDomain E r hr) 2 μ) :
    ‖numberGraphBochnerLinear μ E r hr G‖ = ‖G‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [GW.Spaces.weightedDomain_norm]
  change ‖bochnerShiftedNumberPower μ E r
    ⟨numberGraphIncludeL2 μ E r hr G,numberGraphInclude_mem μ E r hr G⟩‖^2 = _
  rw [numberGraphInclude_product,GW.Analysis.l2_norm_sq (𝕜 := ℂ),GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
  apply integral_congr_ae
  filter_upwards [(numberDomainIsometry E r hr).toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp G] with x hx
  exact (congrArg (fun v : NumberGraphCarrier E r => ‖v‖^2) hx).trans
    (congrArg (fun t : ℝ => t^2) ((numberDomainIsometry E r hr).norm_map (G x)))

set_option backward.isDefEq.respectTransparency.types false in
lemma numberGraphBochner_surjective (r : ℝ) (hr : 0 ≤ r) :
    Function.Surjective (numberGraphBochnerLinear μ E r hr) := by
  intro U
  let V : BochnerFock μ E := bochnerShiftedNumberPower μ E r
    (show (bochnerShiftedNumberPower μ E r).domain from U)
  let G : Lp (NumberWeightedDomain E r hr) 2 μ :=
    (numberReciprocalIsometry E r hr).toContinuousLinearEquiv.toContinuousLinearMap.compLp V
  refine ⟨G,?_⟩
  apply Subtype.ext
  change numberGraphIncludeL2 μ E r hr G =
    (show BochnerFock μ E from (show (bochnerShiftedNumberPower μ E r).domain from U))
  apply Lp.ext
  filter_upwards [(numberDomainInclusion E r hr).coeFn_compLp G,
    (numberReciprocalIsometry E r hr).toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp V,
    bochnerDiagonal_coordinates μ E (fun n => ((n : ℝ)+1)^r)
      (show (bochnerShiftedNumberPower μ E r).domain from U)] with x hi hg hc
  change numberGraphIncludeL2 μ E r hr G x = numberDomainInclusion E r hr (G x) at hi
  change G x = numberReciprocalIsometry E r hr (V x) at hg
  change ∀ n, V x n = (↑(((n : ℝ)+1)^r) : ℂ) •
    (show BochnerFock μ E from (show (bochnerShiftedNumberPower μ E r).domain from U)) x n at hc
  apply lp.ext
  funext n
  rw [hi,hg,numberDomainInclusion_reciprocal,scalarReciprocal_apply]
  change (↑((((n : ℝ)+1)^r)⁻¹) : ℂ) • V x n = _
  rw [hc n,smul_smul]
  have hn : ((n : ℝ)+1)^r ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)
  simp only [← Complex.ofReal_mul,inv_mul_cancel₀ hn,Complex.ofReal_one,one_smul]

def numberGraphBochnerIsometry (r : ℝ) (hr : 0 ≤ r) :
    Lp (NumberWeightedDomain E r hr) 2 μ →ₗᵢ[ℂ] PhysicalNumberWeightedDomain μ E r hr where
  toLinearMap := numberGraphBochnerLinear μ E r hr
  norm_map' := numberGraphBochner_norm μ E r hr

def numberGraphBochnerUnitary (r : ℝ) (hr : 0 ≤ r) :
    Lp (NumberWeightedDomain E r hr) 2 μ ≃ₗᵢ[ℂ] PhysicalNumberWeightedDomain μ E r hr :=
  LinearIsometryEquiv.ofSurjective (numberGraphBochnerIsometry μ E r hr)
    (numberGraphBochner_surjective μ E r hr)

lemma numberGraphBochnerUnitary_inclusion (r : ℝ) (hr : 0 ≤ r)
    (G : Lp (NumberWeightedDomain E r hr) 2 μ) :
    (show BochnerFock μ E from
      (show (bochnerShiftedNumberPower μ E r).domain from numberGraphBochnerUnitary μ E r hr G)) =
      numberGraphIncludeL2 μ E r hr G := rfl

def numberDomainCutoff (r : ℝ) (hr : 0 ≤ r) (m : ℕ) :
    NumberWeightedDomain E r hr →L[ℂ] NumberWeightedDomain E r hr :=
  (numberDomainIsometry E r hr).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((cutoff E m).comp (numberDomainIsometry E r hr).toContinuousLinearEquiv.toContinuousLinearMap)

set_option backward.isDefEq.respectTransparency.types false in
lemma numberDomainCutoff_eq (r : ℝ) (hr : 0 ≤ r) (m : ℕ) (u : NumberWeightedDomain E r hr) :
    numberDomainCutoff E r hr m u = numberWeightedCutoff E r hr m u := by
  apply (numberDomainIsometry E r hr).injective
  change numberDomainIsometry E r hr ((numberDomainIsometry E r hr).symm
    (cutoff E m (show lp E 2 from numberDomainIsometry E r hr u))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact (scalarDiagonal_cutoff_apply E (fun n => ((n : ℝ)+1)^r) m
    (show (numberWeightedGraph E r hr).domain from u)).symm

lemma numberDomainCutoff_inclusion (r : ℝ) (hr : 0 ≤ r) (m : ℕ) (u : NumberWeightedDomain E r hr) :
    numberDomainInclusion E r hr (numberDomainCutoff E r hr m u) =
      cutoff E m (numberDomainInclusion E r hr u) := by
  rw [numberDomainCutoff_eq,numberDomainInclusion_apply,numberDomainInclusion_apply]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
lemma numberGraphBochner_cutoff_inclusion (r : ℝ) (hr : 0 ≤ r) (m : ℕ)
    (G : Lp (NumberWeightedDomain E r hr) 2 μ) :
    numberGraphIncludeL2 μ E r hr ((numberDomainCutoff E r hr m).compLp G) =
      (cutoff E m).compLp (numberGraphIncludeL2 μ E r hr G) := by
  apply Lp.ext
  filter_upwards [(numberDomainInclusion E r hr).coeFn_compLp ((numberDomainCutoff E r hr m).compLp G),
    (numberDomainCutoff E r hr m).coeFn_compLp G,
    (cutoff E m).coeFn_compLp (numberGraphIncludeL2 μ E r hr G),
    (numberDomainInclusion E r hr).coeFn_compLp G] with x hi hg hp hu
  exact hi.trans ((congrArg (numberDomainInclusion E r hr) hg).trans
    ((numberDomainCutoff_inclusion E r hr m (G x)).trans
      ((congrArg (cutoff E m) hu.symm).trans hp.symm)))

def physicalNumberDomainCutoff (r : ℝ) (hr : 0 ≤ r) (m : ℕ) :
    PhysicalNumberWeightedDomain μ E r hr →L[ℂ] PhysicalNumberWeightedDomain μ E r hr :=
  (numberGraphBochnerUnitary μ E r hr).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((numberDomainCutoff E r hr m).compLpL 2 μ).comp
      (numberGraphBochnerUnitary μ E r hr).symm.toContinuousLinearEquiv.toContinuousLinearMap)

lemma numberGraphBochner_cutoff (r : ℝ) (hr : 0 ≤ r) (m : ℕ)
    (G : Lp (NumberWeightedDomain E r hr) 2 μ) :
    physicalNumberDomainCutoff μ E r hr m (numberGraphBochnerUnitary μ E r hr G) =
      numberGraphBochnerUnitary μ E r hr ((numberDomainCutoff E r hr m).compLp G) := by
  change numberGraphBochnerUnitary μ E r hr ((numberDomainCutoff E r hr m).compLp
    ((numberGraphBochnerUnitary μ E r hr).symm (numberGraphBochnerUnitary μ E r hr G))) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

lemma physicalNumberDomainCutoff_inclusion (r : ℝ) (hr : 0 ≤ r) (m : ℕ)
    (U : PhysicalNumberWeightedDomain μ E r hr) :
    (show BochnerFock μ E from (show (bochnerShiftedNumberPower μ E r).domain from
      physicalNumberDomainCutoff μ E r hr m U)) =
      (cutoff E m).compLp
        (show BochnerFock μ E from (show (bochnerShiftedNumberPower μ E r).domain from U)) := by
  obtain ⟨G,rfl⟩ := (numberGraphBochnerUnitary μ E r hr).surjective U
  rw [numberGraphBochner_cutoff,numberGraphBochnerUnitary_inclusion,numberGraphBochnerUnitary_inclusion]
  exact numberGraphBochner_cutoff_inclusion μ E r hr m G

def finiteNumberWeight (r : ℝ) (m n : ℕ) : ℝ :=
  if n ≤ m then ((n : ℝ)+1)^r else 0

lemma finiteNumberWeight_bound (r : ℝ) (hr : 0 ≤ r) (m n : ℕ) :
    0 ≤ finiteNumberWeight r m n ∧ finiteNumberWeight r m n ≤ ((m : ℝ)+1)^r := by
  unfold finiteNumberWeight
  split_ifs with hn
  · exact ⟨Real.rpow_nonneg (by positivity) _,Real.rpow_le_rpow (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hn 1) hr⟩
  · exact ⟨le_rfl,Real.rpow_nonneg (by positivity) _⟩

lemma finiteNumberWeight_fiber_bound (r : ℝ) (hr : 0 ≤ r) (m n : ℕ) :
    ‖(finiteNumberWeight r m n : ℂ) • ContinuousLinearMap.id ℂ (E n)‖ ≤ ((m : ℝ)+1)^r := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.rpow_nonneg (by positivity) _)
  intro u
  change ‖(finiteNumberWeight r m n : ℂ) • u‖ ≤ _
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (finiteNumberWeight_bound r hr m n).1]
  exact mul_le_mul_of_nonneg_right (finiteNumberWeight_bound r hr m n).2 (norm_nonneg _)

/-- Source A_{r,m}: retain the first sectors, then multiply by the finite weights. -/
def numberFiniteWeight (r : ℝ) (hr : 0 ≤ r) (m : ℕ) : lp E 2 →L[ℂ] lp E 2 :=
  GW.Spaces.diagonalMap (fun n => (finiteNumberWeight r m n : ℂ) • ContinuousLinearMap.id ℂ (E n))
    (Real.rpow_nonneg (by positivity) _) (finiteNumberWeight_fiber_bound E r hr m)

lemma numberFiniteWeight_norm (r : ℝ) (hr : 0 ≤ r) (m : ℕ) :
    ‖numberFiniteWeight E r hr m‖ ≤ ((m : ℝ)+1)^r :=
  GW.Spaces.diagonalMap_opNorm _ _ (finiteNumberWeight_fiber_bound E r hr m)

lemma numberFiniteWeight_apply (r : ℝ) (hr : 0 ≤ r) (m : ℕ) (u : lp E 2) (n : ℕ) :
    numberFiniteWeight E r hr m u n =
      if n ≤ m then (↑(((n : ℝ)+1)^r) : ℂ) • u n else 0 := by
  change (finiteNumberWeight r m n : ℂ) • u n = _
  unfold finiteNumberWeight
  split_ifs <;> simp only [Complex.ofReal_zero,zero_smul]

lemma numberFiniteWeight_product (r : ℝ) (hr : 0 ≤ r) (m : ℕ)
    (u : (shiftedNumberPower E r).domain) :
    numberFiniteWeight E r hr m u = cutoff E m (shiftedNumberPower E r u) := by
  apply lp.ext
  funext n
  rw [numberFiniteWeight_apply,cutoff_apply,shiftedNumberPower_apply]

lemma numberFiniteWeight_tendsto (r : ℝ) (hr : 0 ≤ r)
    (u : (shiftedNumberPower E r).domain) :
    Tendsto (fun m => numberFiniteWeight E r hr m u) atTop (𝓝 (shiftedNumberPower E r u)) := by
  simp only [numberFiniteWeight_product]
  exact cutoff_tendsto E (shiftedNumberPower E r u)

lemma numberFiniteWeight_stronglyMeasurable (r : ℝ) (hr : 0 ≤ r) (m : ℕ) (U : BochnerFock μ E) :
    StronglyMeasurable (fun x => numberFiniteWeight E r hr m (U x)) :=
  (numberFiniteWeight E r hr m).continuous.comp_stronglyMeasurable (Lp.stronglyMeasurable U)

lemma numberFiniteWeight_ae_tendsto (r : ℝ) (hr : 0 ≤ r) (U : BochnerFock μ E)
    (hU : ∀ᵐ x ∂μ, U x ∈ (shiftedNumberPower E r).domain) :
    ∀ᵐ x ∂μ, Tendsto (fun m => numberFiniteWeight E r hr m (U x)) atTop
      (𝓝 (weightedPointwise μ E (fun n => ((n : ℝ)+1)^r) U x)) := by
  filter_upwards [hU] with x hx
  have he : shiftedNumberPower E r ⟨U x,hx⟩ =
      weightedPointwise μ E (fun n => ((n : ℝ)+1)^r) U x := by
    apply lp.ext
    funext n
    exact (weightedPointwise_apply μ E (fun n => ((n : ℝ)+1)^r) U x hx n).symm
  rw [← he]
  exact numberFiniteWeight_tendsto E r hr ⟨U x,hx⟩

lemma physicalNumberWeighted_norm_series (r : ℝ) (hr : 0 ≤ r)
    (U : PhysicalNumberWeightedDomain μ E r hr) :
    ‖U‖^2 = ∑' n : ℕ, ((n : ℝ)+1)^(2*r) * ‖bochnerCoordinate μ E n
      (show BochnerFock μ E from (show (bochnerShiftedNumberPower μ E r).domain from U))‖^2 := by
  rw [bochnerWeighted_norm_series]
  apply tsum_congr
  intro n
  rw [rpow_square _ _ (by positivity : 0 ≤ (n : ℝ)+1)]

set_option backward.isDefEq.respectTransparency.types false in
lemma physicalNumberWeighted_graph_representative (r : ℝ) (hr : 0 ≤ r)
    (U : PhysicalNumberWeightedDomain μ E r hr) :
    ∃ g : X → NumberWeightedDomain E r hr, StronglyMeasurable g ∧ MemLp g 2 μ ∧
      (fun x => numberDomainInclusion E r hr (g x)) =ᵐ[μ]
        (show BochnerFock μ E from (show (bochnerShiftedNumberPower μ E r).domain from U)) ∧
      (∫ x, ‖g x‖^2 ∂μ) = ‖U‖^2 := by
  let G := (numberGraphBochnerUnitary μ E r hr).symm U
  refine ⟨G,Lp.stronglyMeasurable G,Lp.memLp G,?_,?_⟩
  · have he : numberGraphIncludeL2 μ E r hr G =
        (show BochnerFock μ E from (show (bochnerShiftedNumberPower μ E r).domain from U)) := by
      have h := numberGraphBochnerUnitary_inclusion μ E r hr G
      rw [LinearIsometryEquiv.apply_symm_apply] at h
      exact h.symm
    have h := (numberDomainInclusion E r hr).coeFn_compLp G
    change numberGraphIncludeL2 μ E r hr G =ᵐ[μ] (fun x => numberDomainInclusion E r hr (G x)) at h
    rw [he] at h
    exact h.symm
  · rw [← GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
    exact congrArg (fun t : ℝ => t^2) ((numberGraphBochnerUnitary μ E r hr).symm.norm_map U)

end WeightedPointwise
abbrev PhysicalNumberDomain (r : ℝ) (hr : 0 ≤ r) :=
  PhysicalNumberWeightedDomain (volume : Measure GW.Space) Sector r hr
abbrev physicalNumberGraphBochnerUnitary (r : ℝ) (hr : 0 ≤ r) :
    Lp (NumberWeightedDomain Sector r hr) 2 (volume : Measure GW.Space) ≃ₗᵢ[ℂ] PhysicalNumberDomain r hr :=
  numberGraphBochnerUnitary (volume : Measure GW.Space) Sector r hr

end GW.Fock
