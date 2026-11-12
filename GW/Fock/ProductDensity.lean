module
public import GW.Fock.BochnerGraph
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ENNReal
namespace GW.Fock
section ProductNorm
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma simpleTensor_norm (γ : Lp ℂ 2 μ) (u : H) :
    ‖(ContinuousLinearMap.toSpanSingleton ℂ u).compLp γ‖ = ‖γ‖*‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
  calc
    _ = ∫ x, ‖γ x‖^2 * ‖u‖^2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [(ContinuousLinearMap.toSpanSingleton ℂ u).coeFn_compLp γ] with x hx
      rw [hx]
      change ‖γ x • u‖^2 = _
      rw [norm_smul,mul_pow]
    _ = (∫ x, ‖γ x‖^2 ∂μ) * ‖u‖^2 := integral_mul_const _ _
    _ = (‖γ‖*‖u‖)^2 := by rw [← GW.Analysis.l2_norm_sq (𝕜 := ℂ)];ring
lemma compLp_indicatorConst {s : Set X} (hs : MeasurableSet s) (hf : μ s ≠ ∞)
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℂ K] (T : H →L[ℂ] K) (u : H) :
    T.compLp (indicatorConstLp 2 hs hf u) = indicatorConstLp 2 hs hf (T u) := by
  apply Lp.ext
  filter_upwards [T.coeFn_compLp (indicatorConstLp 2 hs hf u),
    (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hf) (c := u)),
    (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hf) (c := T u))] with x hx hu ht
  rw [hx,hu,ht]
  by_cases h : x ∈ s
  · simp only [Set.indicator_of_mem h]
  · simp only [Set.indicator_of_notMem h,map_zero]

lemma simpleTensor_indicatorConst {s : Set X} (hs : MeasurableSet s) (hf : μ s ≠ ∞) (u : H) :
    (ContinuousLinearMap.toSpanSingleton ℂ u).compLp (indicatorConstLp 2 hs hf (1 : ℂ)) =
      indicatorConstLp 2 hs hf u := by
  rw [compLp_indicatorConst]
  simp only [ContinuousLinearMap.toSpanSingleton_apply,one_smul]

end ProductNorm

section WeightedProducts
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
variable (E : ℕ → Type*) [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℂ (E n)]

/-- Source coordinates of the weighted physical vector, with their original sum norm. -/
def numberWeightSectorCoordinates (r : ℝ) (hr : 0 ≤ r) :
    PhysicalNumberWeightedDomain μ E r hr ≃ₗᵢ[ℂ] BochnerSectorSum μ E :=
  (GW.Spaces.weightedDomainIsometry
    (bochnerWeightedGraph μ E (fun n => ((n : ℝ)+1)^r) (shiftedNumber_weight_one r hr))).trans
    (bochnerUnitary μ E).symm

def weightedSimpleTensor (r : ℝ) (hr : 0 ≤ r) (γ : Lp ℂ 2 μ) (u : NumberWeightedDomain E r hr) :
    PhysicalNumberWeightedDomain μ E r hr :=
  numberGraphBochnerUnitary μ E r hr ((ContinuousLinearMap.toSpanSingleton ℂ u).compLp γ)

lemma weightedSimpleTensor_norm (r : ℝ) (hr : 0 ≤ r) (γ : Lp ℂ 2 μ) (u : NumberWeightedDomain E r hr) :
    ‖weightedSimpleTensor μ E r hr γ u‖ = ‖γ‖*‖u‖ := by
  change ‖numberGraphBochnerUnitary μ E r hr _‖ = _
  rw [LinearIsometryEquiv.norm_map,simpleTensor_norm]

lemma weightedSimpleTensor_ambient (r : ℝ) (hr : 0 ≤ r) (γ : Lp ℂ 2 μ) (u : NumberWeightedDomain E r hr) :
    (show BochnerFock μ E from (show (bochnerShiftedNumberPower μ E r).domain from
      weightedSimpleTensor μ E r hr γ u)) =
      (ContinuousLinearMap.toSpanSingleton ℂ (numberDomainInclusion E r hr u)).compLp γ := by
  rw [weightedSimpleTensor,numberGraphBochnerUnitary_inclusion]
  apply Lp.ext
  filter_upwards [(numberDomainInclusion E r hr).coeFn_compLp
    ((ContinuousLinearMap.toSpanSingleton ℂ u).compLp γ),
    (ContinuousLinearMap.toSpanSingleton ℂ u).coeFn_compLp γ,
    (ContinuousLinearMap.toSpanSingleton ℂ (numberDomainInclusion E r hr u)).coeFn_compLp γ] with x hi ht hz
  exact hi.trans ((congrArg (numberDomainInclusion E r hr) ht).trans
    ((map_smul (numberDomainInclusion E r hr) (γ x) u).trans hz.symm))

def numberWeightedSingle (r : ℝ) (hr : 0 ≤ r) (n : ℕ) (v : E n) : NumberWeightedDomain E r hr :=
  show (shiftedNumberPower E r).domain from
    ⟨lp.single 2 n v,scalarDiagonal_single_mem E (fun j => ((j : ℝ)+1)^r) n v⟩

lemma numberWeightedSingle_norm (r : ℝ) (hr : 0 ≤ r) (n : ℕ) (v : E n) :
    ‖numberWeightedSingle E r hr n v‖ = ((n : ℝ)+1)^r * ‖v‖ := by
  rw [GW.Spaces.weightedDomain_norm]
  change ‖scalarDiagonal E (fun j => ((j : ℝ)+1)^r)
    ⟨lp.single 2 n v,scalarDiagonal_single_mem E (fun j => ((j : ℝ)+1)^r) n v⟩‖ = _
  rw [scalarDiagonal_single_apply,lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2),
    norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]

lemma weightedSingleTensor_norm (r : ℝ) (hr : 0 ≤ r) (γ : Lp ℂ 2 μ) (n : ℕ) (v : E n) :
    ‖weightedSimpleTensor μ E r hr γ (numberWeightedSingle E r hr n v)‖ =
      ((n : ℝ)+1)^r * ‖γ‖ * ‖v‖ := by
  rw [weightedSimpleTensor_norm,numberWeightedSingle_norm]
  ring

set_option backward.isDefEq.respectTransparency.types false in
lemma numberWeightSectorCoordinates_product (r : ℝ) (hr : 0 ≤ r)
    (U : PhysicalNumberWeightedDomain μ E r hr) :
    bochnerUnitary μ E (numberWeightSectorCoordinates μ E r hr U) =
      bochnerShiftedNumberPower μ E r (show (bochnerShiftedNumberPower μ E r).domain from U) :=
  (bochnerUnitary μ E).apply_symm_apply _

set_option backward.isDefEq.respectTransparency.types false in
lemma numberGraphProductL2_simpleTensor (r : ℝ) (hr : 0 ≤ r) (γ : Lp ℂ 2 μ)
    (u : NumberWeightedDomain E r hr) :
    numberGraphProductL2 μ E r hr ((ContinuousLinearMap.toSpanSingleton ℂ u).compLp γ) =
      (ContinuousLinearMap.toSpanSingleton ℂ
        (show lp E 2 from numberDomainIsometry E r hr u)).compLp γ := by
  apply Lp.ext
  filter_upwards [(numberDomainIsometry E r hr).toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp
    ((ContinuousLinearMap.toSpanSingleton ℂ u).compLp γ),
    (ContinuousLinearMap.toSpanSingleton ℂ u).coeFn_compLp γ,
    (ContinuousLinearMap.toSpanSingleton ℂ (show lp E 2 from numberDomainIsometry E r hr u)).coeFn_compLp γ]
    with x hi ht hz
  exact hi.trans ((congrArg (numberDomainIsometry E r hr) ht).trans
    ((map_smul (numberDomainIsometry E r hr) (γ x) u).trans hz.symm))

/-- Actual finite-measure one-sector indicator products, specified by ambient classes. -/
def numberIndicatorProducts (r : ℝ) (hr : 0 ≤ r) : Set (PhysicalNumberWeightedDomain μ E r hr) :=
  {U | ∃ (n : ℕ) (A : Set X) (hA : MeasurableSet A) (hfinite : μ A ≠ ∞) (v : E n),
    (show BochnerFock μ E from (show (bochnerShiftedNumberPower μ E r).domain from U)) =
      indicatorConstLp 2 hA hfinite (lp.single 2 n v)}

def weightedIndicatorGenerator (r : ℝ) (hr : 0 ≤ r) (n : ℕ)
    {A : Set X} (hA : MeasurableSet A) (hfinite : μ A ≠ ∞) (v : E n) :
    PhysicalNumberWeightedDomain μ E r hr :=
  weightedSimpleTensor μ E r hr (indicatorConstLp 2 hA hfinite (1 : ℂ))
    (numberWeightedSingle E r hr n ((↑((((n : ℝ)+1)^r)⁻¹) : ℂ) • v))

lemma weightedIndicatorGenerator_mem (r : ℝ) (hr : 0 ≤ r) (n : ℕ)
    {A : Set X} (hA : MeasurableSet A) (hfinite : μ A ≠ ∞) (v : E n) :
    weightedIndicatorGenerator μ E r hr n hA hfinite v ∈ numberIndicatorProducts μ E r hr := by
  refine ⟨n,A,hA,hfinite,(↑((((n : ℝ)+1)^r)⁻¹) : ℂ) • v,?_⟩
  rw [weightedIndicatorGenerator,weightedSimpleTensor_ambient,numberDomainInclusion_apply]
  exact simpleTensor_indicatorConst μ hA hfinite _

set_option backward.isDefEq.respectTransparency.types false in
lemma numberDomainIsometry_single_inverse (r : ℝ) (hr : 0 ≤ r) (n : ℕ) (v : E n) :
    (show lp E 2 from numberDomainIsometry E r hr
      (numberWeightedSingle E r hr n ((↑((((n : ℝ)+1)^r)⁻¹) : ℂ) • v))) = lp.single 2 n v := by
  change scalarDiagonal E (fun j => ((j : ℝ)+1)^r)
    ⟨lp.single 2 n ((↑((((n : ℝ)+1)^r)⁻¹) : ℂ) • v),_⟩ = _
  rw [scalarDiagonal_single_apply,smul_smul]
  have hn : ((n : ℝ)+1)^r ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)
  simp only [← Complex.ofReal_mul,mul_inv_cancel₀ hn,Complex.ofReal_one,one_smul]

set_option backward.isDefEq.respectTransparency.types false in
lemma weightedIndicatorGenerator_coordinates (r : ℝ) (hr : 0 ≤ r) (n : ℕ)
    {A : Set X} (hA : MeasurableSet A) (hfinite : μ A ≠ ∞) (v : E n) :
    numberWeightSectorCoordinates μ E r hr (weightedIndicatorGenerator μ E r hr n hA hfinite v) =
      lp.single 2 n (indicatorConstLp 2 hA hfinite v) := by
  apply (bochnerUnitary μ E).injective
  rw [numberWeightSectorCoordinates_product]
  change bochnerShiftedNumberPower μ E r
    ⟨numberGraphIncludeL2 μ E r hr ((ContinuousLinearMap.toSpanSingleton ℂ
      (numberWeightedSingle E r hr n ((↑((((n : ℝ)+1)^r)⁻¹) : ℂ) • v))).compLp
        (indicatorConstLp 2 hA hfinite (1 : ℂ))),_⟩ = _
  rw [numberGraphInclude_product,numberGraphProductL2_simpleTensor,numberDomainIsometry_single_inverse,
    simpleTensor_indicatorConst,bochnerUnitary_single,compLp_indicatorConst]
  rfl

lemma numberIndicatorSpan_dense (r : ℝ) (hr : 0 ≤ r) :
    Dense (Submodule.span ℂ (numberIndicatorProducts μ E r hr) : Set (PhysicalNumberWeightedDomain μ E r hr)) := by
  let S := Submodule.span ℂ (numberIndicatorProducts μ E r hr)
  let C := S.topologicalClosure
  let e := numberWeightSectorCoordinates μ E r hr
  have hind : ∀ (n : ℕ) (A : Set X) (hA : MeasurableSet A) (hf : μ A ≠ ∞) (v : E n),
      e.symm (lp.single 2 n (indicatorConstLp 2 hA hf v)) ∈ C := by
    intro n A hA hf v
    have he := weightedIndicatorGenerator_coordinates μ E r hr n hA hf v
    change e (weightedIndicatorGenerator μ E r hr n hA hf v) = _ at he
    rw [← he,LinearIsometryEquiv.symm_apply_apply]
    exact S.le_topologicalClosure (Submodule.subset_span (weightedIndicatorGenerator_mem μ E r hr n hA hf v))
  have hsector : ∀ (n : ℕ) (f : Lp (E n) 2 μ), e.symm (lp.single 2 n f) ∈ C := by
    intro n f
    let L : Lp (E n) 2 μ →L[ℂ] PhysicalNumberWeightedDomain μ E r hr :=
      e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (lp.singleContinuousLinearMap ℂ (fun n => Lp (E n) 2 μ) 2 n)
    change L f ∈ C
    refine (Lp.simpleFunc.denseRange (E := E n) (μ := μ) (p := 2) (by norm_num)).induction_on f
      (S.isClosed_topologicalClosure.preimage L.continuous) ?_
    intro sf
    refine Lp.simpleFunc.induction (p := 2) (by norm_num) (by norm_num) ?_ ?_ sf
    · intro v A hA hf
      exact hind n A hA hf.ne v
    · intro f g hf hg hd hfc hgc
      change L ((SimpleFunc.toLp f hf : Lp (E n) 2 μ) + SimpleFunc.toLp g hg) ∈ C
      rw [map_add]
      exact C.add_mem hfc hgc
  intro U
  change U ∈ C
  have hfinite : ∀ m, e.symm (cutoff (fun n => Lp (E n) 2 μ) m (e U)) ∈ C := by
    intro m
    rw [cutoff_sum,map_sum]
    exact C.sum_mem (fun n _ => hsector n (e U n))
  have ht := e.symm.continuous.tendsto (e U) |>.comp
    (cutoff_tendsto (fun n => Lp (E n) 2 μ) (e U))
  have ht' : Tendsto (fun m => e.symm (cutoff (fun n => Lp (E n) 2 μ) m (e U))) atTop (𝓝 U) := by
    simpa only [LinearIsometryEquiv.symm_apply_apply,Function.comp_def] using ht
  exact S.isClosed_topologicalClosure.mem_of_tendsto ht' (Eventually.of_forall hfinite)

lemma numberIndicatorSpan_sequence (r : ℝ) (hr : 0 ≤ r) (U : PhysicalNumberWeightedDomain μ E r hr) :
    ∃ u : ℕ → PhysicalNumberWeightedDomain μ E r hr,
      (∀ k, u k ∈ Submodule.span ℂ (numberIndicatorProducts μ E r hr)) ∧
      Tendsto u atTop (𝓝 U) :=
  mem_closure_iff_seq_limit.mp (numberIndicatorSpan_dense μ E r hr U)

lemma numberWeighted_finite_dense (r : ℝ) (hr : 0 ≤ r) :
    Dense {u : NumberWeightedDomain E r hr |
      (show lp E 2 from (show (shiftedNumberPower E r).domain from u)) ∈ finiteSectorDomain E} := by
  intro u
  apply mem_closure_of_tendsto (numberWeightedCutoff_tendsto E r hr u)
  exact Eventually.of_forall (fun m => cutoff_mem_finiteSectorDomain E m
    (show lp E 2 from (show (shiftedNumberPower E r).domain from u)))

/-- Source full L²-product generators, with the exact finite-sector condition. -/
def numberFiniteProducts (r : ℝ) (hr : 0 ≤ r) : Set (PhysicalNumberWeightedDomain μ E r hr) :=
  {U | ∃ (γ : Lp ℂ 2 μ) (u : NumberWeightedDomain E r hr),
    (show lp E 2 from (show (shiftedNumberPower E r).domain from u)) ∈ finiteSectorDomain E ∧
      U = weightedSimpleTensor μ E r hr γ u}

set_option backward.isDefEq.respectTransparency.types false in
lemma numberIndicatorProducts_subset (r : ℝ) (hr : 0 ≤ r) :
    numberIndicatorProducts μ E r hr ⊆ numberFiniteProducts μ E r hr := by
  rintro U ⟨n,A,hA,hf,v,hU⟩
  refine ⟨indicatorConstLp 2 hA hf (1 : ℂ),numberWeightedSingle E r hr n v,?_,?_⟩
  · change lp.single 2 n v ∈ finiteSectorDomain E
    apply (finiteSectorDomain_iff E _).mpr
    exact ⟨n,fun j hj => lp.single_apply_ne 2 n v (ne_of_gt hj)⟩
  · apply Subtype.ext
    change (show BochnerFock μ E from (show (bochnerShiftedNumberPower μ E r).domain from U)) = _
    have he := weightedSimpleTensor_ambient μ E r hr (indicatorConstLp 2 hA hf (1 : ℂ))
      (numberWeightedSingle E r hr n v)
    rw [numberDomainInclusion_apply] at he
    exact hU.trans (he.trans (simpleTensor_indicatorConst μ hA hf (lp.single 2 n v))).symm

lemma numberFiniteSpan_dense (r : ℝ) (hr : 0 ≤ r) :
    Dense (Submodule.span ℂ (numberFiniteProducts μ E r hr) : Set (PhysicalNumberWeightedDomain μ E r hr)) :=
  (numberIndicatorSpan_dense μ E r hr).mono (Submodule.span_mono (numberIndicatorProducts_subset μ E r hr))

lemma numberFiniteSpan_sequence (r : ℝ) (hr : 0 ≤ r) (U : PhysicalNumberWeightedDomain μ E r hr) :
    ∃ u : ℕ → PhysicalNumberWeightedDomain μ E r hr,
      (∀ k, u k ∈ Submodule.span ℂ (numberFiniteProducts μ E r hr)) ∧
      Tendsto u atTop (𝓝 U) :=
  mem_closure_iff_seq_limit.mp (numberFiniteSpan_dense μ E r hr U)

def numberFiniteInput (r : ℝ) (hr : 0 ≤ r) (u : lp E 2) (hu : u ∈ finiteSectorDomain E) :
    NumberWeightedDomain E r hr :=
  show (shiftedNumberPower E r).domain from
    ⟨u,(finiteSectorDomain_le E (fun n => ((n : ℝ)+1)^r)) hu⟩

lemma numberFiniteTensor_mem (r : ℝ) (hr : 0 ≤ r) (γ : Lp ℂ 2 μ) (u : lp E 2)
    (hu : u ∈ finiteSectorDomain E) :
    weightedSimpleTensor μ E r hr γ (numberFiniteInput E r hr u hu) ∈ numberFiniteProducts μ E r hr :=
  ⟨γ,numberFiniteInput E r hr u hu,hu,rfl⟩

lemma finiteSectorDomain_eq_ranges : (finiteSectorDomain E : Set (lp E 2)) =
    ⋃ m, Set.range (cutoff E m) := by
  ext u
  constructor
  · intro hu
    obtain ⟨m,hm⟩ := (finiteSectorDomain_iff E u).mp hu
    apply Set.mem_iUnion.mpr
    refine ⟨m,u,?_⟩
    apply lp.ext
    funext n
    rw [cutoff_apply]
    split_ifs with hn
    · rfl
    · exact (hm n (lt_of_not_ge hn)).symm
  · intro hu
    obtain ⟨m,v,rfl⟩ := Set.mem_iUnion.mp hu
    exact cutoff_mem_finiteSectorDomain E m v

lemma numberWeighted_finite_sequence (r : ℝ) (hr : 0 ≤ r) (u : NumberWeightedDomain E r hr) :
    ∃ v : ℕ → NumberWeightedDomain E r hr,
      (∀ m, (show lp E 2 from (show (shiftedNumberPower E r).domain from v m)) ∈
        ⋃ k, Set.range (cutoff E k)) ∧ Tendsto v atTop (𝓝 u) := by
  refine ⟨fun m => numberWeightedCutoff E r hr m u,?_,numberWeightedCutoff_tendsto E r hr u⟩
  intro m
  exact Set.mem_iUnion.mpr ⟨m,
    (show lp E 2 from (show (shiftedNumberPower E r).domain from u)),rfl⟩

end WeightedProducts
lemma physicalNumberFiniteSpan_dense (r : ℝ) (hr : 0 ≤ r) :
    Dense (Submodule.span ℂ (numberFiniteProducts (volume : Measure GW.Space) Sector r hr) :
      Set (PhysicalNumberDomain r hr)) :=
  numberFiniteSpan_dense (volume : Measure GW.Space) Sector r hr

lemma physicalNumberIndicatorSpan_dense (r : ℝ) (hr : 0 ≤ r) :
    Dense (Submodule.span ℂ (numberIndicatorProducts (volume : Measure GW.Space) Sector r hr) :
      Set (PhysicalNumberDomain r hr)) :=
  numberIndicatorSpan_dense (volume : Measure GW.Space) Sector r hr

end GW.Fock
