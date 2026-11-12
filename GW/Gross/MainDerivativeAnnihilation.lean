module
public import GW.Gross.MainGrossForm
public import GW.Gross.MainSingularAnnihilationLimit
public import GW.Model.ModelFrohlichEstimates

/-! Source main:derivative-annihilation, manuscript6507–6562.
Actual differentiated annihilator graphs on original H0 for finite and infinite cutoffs,
sharp collective bound and uniform real-tail decay. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Gross
open GW.Model GW.Fock GW.Analysis

/- Source argument component Continuity01. -/
lemma derivative_annihilator_component (f : OneBoson) (u : FiberPhysicalRoot) (n : ℕ) :
    electronBosonUnitary.symm (commutatorPhaseAnnihilatorMap f u) n =
      generalizedAnnihilationSector (phaseMultiplicationKernel f) n
        (electronBosonUnitary.symm (fiberPhysicalRootInput u).val (n+1)) := by
  obtain ⟨a,ha,hout⟩ := (generalizedAnnihilation (phaseMultiplicationKernel f)).mem_graph_iff.mp
    (commutatorPhaseAnnihilatorMap_graph f u)
  exact (congrArg (fun z : Physical => electronBosonUnitary.symm z n) hout).symm.trans
    ((generalizedAnnihilation_apply (phaseMultiplicationKernel f) a n).trans
      (congrArg (fun z : Physical => generalizedAnnihilationSector (phaseMultiplicationKernel f) n
        (electronBosonUnitary.symm z (n+1))) ha))

lemma derivative_annihilator_sub (f g : OneBoson) (u : FiberPhysicalRoot) :
    commutatorPhaseAnnihilatorMap (f-g) u =
      commutatorPhaseAnnihilatorMap f u-commutatorPhaseAnnihilatorMap g u := by
  apply electronBosonUnitary.symm.injective
  apply lp.ext
  funext n
  have h₀ := derivative_annihilator_component (f-g) u n
  have h₁ := derivative_annihilator_component f u n
  have h₂ := derivative_annihilator_component g u n
  have hk := congrArg (fun K : BosonKernel ElectronL2 =>
      generalizedAnnihilationSector K n (electronBosonUnitary.symm (fiberPhysicalRootInput u).val (n+1)))
    (convolutionPhaseKernel_sub f g)
  have hsector := convolutionSectorAnnihilation_sub (phaseMultiplicationKernel f) (phaseMultiplicationKernel g)
    n (electronBosonUnitary.symm (fiberPhysicalRootInput u).val (n+1))
  have hout := congrArg (fun z : ElectronBosonSum => z n)
    (electronBosonUnitary.symm.map_sub (commutatorPhaseAnnihilatorMap f u) (commutatorPhaseAnnihilatorMap g u))
  exact h₀.trans (hk.trans (hsector.trans
    ((congrArg₂ (fun x y => x-y) h₁ h₂).symm.trans hout.symm)))

lemma derivative_annihilator_coefficient_bound (f g : OneBoson) (u : FiberPhysicalRoot) :
    ‖commutatorPhaseAnnihilatorMap f u-commutatorPhaseAnnihilatorMap g u‖ ≤ ‖f-g‖*‖u‖ := by
  rw [← derivative_annihilator_sub]
  exact commutatorPhaseAnnihilatorMap_bound (f-g) u

lemma derivative_annihilator_coefficient_tendsto (fs : ℝ → OneBoson) (f : OneBoson)
    (hf : Tendsto fs atTop (𝓝 f)) (u : FiberPhysicalRoot) :
    Tendsto (fun R => commutatorPhaseAnnihilatorMap (fs R) u) atTop
      (𝓝 (commutatorPhaseAnnihilatorMap f u)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun R => derivative_annihilator_coefficient_bound (fs R) f u)
  simpa only [zero_mul] using (tendsto_iff_norm_sub_tendsto_zero.mp hf).mul_const ‖u‖

/- Source argument component Closed01. -/
lemma derivative_graph_annihilator_identification (f : OneBoson) (u : FreeGraphDomain) :
    commutatorPhaseAnnihilatorMap f (commutatorGraphRootMap u) = convolutionAnnihilationMap f u := by
  have hg := commutatorPhaseAnnihilatorMap_graph f (commutatorGraphRootMap u)
  rw [commutatorGraphRootMap_value] at hg
  exact (generalizedAnnihilation (phaseMultiplicationKernel f)).mem_graph_snd_inj
    hg (convolutionAnnihilation_graph f u) rfl

lemma derivative_closed_component_limit (fs : ℝ → OneBoson) (f : OneBoson) (j : Fin 3)
    (hf : Tendsto fs atTop (𝓝 f))
    (hjs : ∀ R, MemLp (fun k => (k j : ℂ)*fs R k) 2 (volume : Measure GW.Space))
    (ss : ℝ → Physical) (s : Physical) (u : FreeGraphDomain)
    (hs : Tendsto ss atTop (𝓝 s))
    (he : ∀ᶠ R in atTop, commutatorPhaseAnnihilatorMap (weylMomentumCoefficient (fs R) j (hjs R))
      (commutatorGraphRootMap u) = ss R) :
    (commutatorPhaseAnnihilatorMap f (commutatorGraphRootMap u),
      commutatorPhaseAnnihilatorMap f (commutatorGraphMomentumRootMap j u)+s) ∈
        (electronMomentumCoordinate j).graph := by
  have hclosed : (electronMomentumCoordinate j).IsClosed :=
    GW.Operators.selfadjoint_closed _
      (physicalSectorMultiplier_selfadjoint (fun _ => electronCoordinate_measurable j))
  have hl := (derivative_annihilator_coefficient_tendsto fs f hf (commutatorGraphRootMap u)).prodMk_nhds
    ((derivative_annihilator_coefficient_tendsto fs f hf (commutatorGraphMomentumRootMap j u)).add hs)
  apply hclosed.mem_of_tendsto hl
  filter_upwards [he] with R hR
  have hg := commutatorAnnihilator_graph_all (fs R) j (hjs R) u
  change (commutatorPhaseAnnihilatorMap (fs R) (commutatorGraphRootMap u),
    commutatorPhaseAnnihilatorMap (fs R) (commutatorGraphMomentumRootMap j u)+
      commutatorPhaseAnnihilatorMap (weylMomentumCoefficient (fs R) j (hjs R))
        (commutatorGraphRootMap u)) ∈ _ at hg
  rw [hR] at hg
  exact hg

/- Source argument component Bound01. -/
lemma derivative_annihilator_momentum_bound (fs : Fin 3 → OneBoson) (u : FreeGraphDomain) :
    ‖∑ j : Fin 3, commutatorPhaseAnnihilatorMap (fs j) (commutatorGraphMomentumRootMap j u)‖ ≤
      (1/2:ℝ)*Real.sqrt (∑ j : Fin 3, ‖fs j‖^2)*‖u‖ := by
  have hb := grossMixed_collective_bound (show freeGraphOperator.domain from u)
  have hs : (∑ j : Fin 3, ‖fs j‖*‖commutatorGraphMomentumRootMap j u‖) ≤
      Real.sqrt (∑ j : Fin 3, ‖fs j‖^2)*
        Real.sqrt (∑ j : Fin 3, ‖physicalShiftedNumberPower (1/2) (freeGraphMomentumShiftedRoot u j)‖^2) := by
    simp_rw [grossGraphMomentumRoot_norm]
    exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  calc
    _ ≤ ∑ j : Fin 3, ‖commutatorPhaseAnnihilatorMap (fs j) (commutatorGraphMomentumRootMap j u)‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin 3, ‖fs j‖*‖commutatorGraphMomentumRootMap j u‖ :=
      Finset.sum_le_sum (fun j _ => commutatorPhaseAnnihilatorMap_bound (fs j) (commutatorGraphMomentumRootMap j u))
    _ ≤ _ := hs
    _ ≤ Real.sqrt (∑ j : Fin 3, ‖fs j‖^2)*((1/2:ℝ)*‖freeGraphOperator u‖) :=
      mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)
    _ = _ := by rw [freeGraphDomain_norm]; ring

/- Source argument component Sum01. -/
lemma derivative_annihilator_zero (u : FiberPhysicalRoot) : commutatorPhaseAnnihilatorMap 0 u = 0 := by
  have h := derivative_annihilator_sub (0 : OneBoson) 0 u
  simpa only [sub_self] using h
lemma derivative_annihilator_add (f g : OneBoson) (u : FiberPhysicalRoot) :
    commutatorPhaseAnnihilatorMap (f+g) u =
      commutatorPhaseAnnihilatorMap f u+commutatorPhaseAnnihilatorMap g u := by
  have h := derivative_annihilator_sub (f+g) g u
  rw [add_sub_cancel_right] at h
  exact (eq_sub_iff_add_eq.mp h).symm
lemma derivative_annihilator_sum {ι : Type*} (s : Finset ι) (fs : ι → OneBoson) (u : FiberPhysicalRoot) :
    commutatorPhaseAnnihilatorMap (∑ i ∈ s, fs i) u =
      ∑ i ∈ s, commutatorPhaseAnnihilatorMap (fs i) u := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,derivative_annihilator_zero]
  | @insert a s ha ih => rw [Finset.sum_insert ha,Finset.sum_insert ha,derivative_annihilator_add,ih]

lemma derivative_finite_graph_sum (f : OneBoson) (R : ℝ) (u : FreeGraphDomain) :
    ∑ j : Fin 3, commutatorAnnihilatorRightMap
        (weylMomentumCoefficient (grossTruncateCoefficient f R) j (grossForm_finite_first_memLp f R j)) j
        (grossForm_finite_second_memLp f R j j) u =
      (∑ j : Fin 3, commutatorPhaseAnnihilatorMap
        (weylMomentumCoefficient (grossTruncateCoefficient f R) j (grossForm_finite_first_memLp f R j))
        (commutatorGraphMomentumRootMap j u)) + convolutionAnnihilationMap (grossFormFiniteSecondRadial f R) u := by
  simp only [commutatorAnnihilatorRightMap,ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply]
  rw [Finset.sum_add_distrib,← derivative_annihilator_sum, grossFormSecondCoefficient_sum,
    derivative_graph_annihilator_identification]

lemma derivative_singular_finite_norm (α K R : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (m : GW.Space → ℂ) (hm : Measurable m)
    (hd : ∀ᵐ k ∂(volume : Measure GW.Space), ‖m k‖ ≤ (highRegion K).indicator (fun k => |v α k|) k)
    (hR : K ≤ R) :
    ‖singularFiniteMap α K hα hK m hm hd R‖ ≤ (1/2:ℝ)*Real.sqrt (coefficientTTail α K) := by
  have h := convolutionCutoffMap_ordered_sharp (singularConvolutionData α K hα hK m hm hd)
    K K R le_rfl le_rfl hR
  change ‖singularFiniteMap α K hα hK m hm hd R-singularFiniteMap α K hα hK m hm hd K‖ ≤ _ at h
  rw [singularFiniteMap_boundary,sub_zero] at h
  exact h

/- Source argument component Data02. -/
-- Source6507–6562: second moments are singular coefficients, not L2 hypotheses.
lemma derivative_raw_domination (α K : ℝ) (r : GW.Space → ℝ)
    (hr : ∀ k, |r k| ≤ ‖k‖^2) (k : GW.Space) :
    ‖(r k : ℂ)*(b α K k : ℂ)‖ ≤
      (highRegion K).indicator (fun k => |v α k|) k := by
  rw [norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs]
  by_cases hk : K < ‖k‖
  · rw [Set.indicator_of_mem hk,b,if_pos hk,abs_div,abs_neg,
      abs_of_pos (show 0 < 1+‖k‖^2 by positivity)]
    apply (mul_le_mul_of_nonneg_right (hr k) (by positivity)).trans
    have hv : 0 ≤ |v α k| := abs_nonneg _
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (show 0 < 1+‖k‖^2 by positivity)).mpr
    nlinarith
  · rw [Set.indicator_of_notMem hk,b,if_neg hk,abs_zero,mul_zero]

lemma derivative_coordinate_square_domination (α K : ℝ) (j : Fin 3) :
    ∀ k : GW.Space, ‖(((k j)^2 : ℝ) : ℂ)*(b α K k : ℂ)‖ ≤
      (highRegion K).indicator (fun k => |v α k|) k := by
  apply derivative_raw_domination α K (fun k => (k j)^2)
  intro k
  rw [abs_of_nonneg (sq_nonneg _)]
  have h := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr
    (electronCoordinate_abs_le k j)
  simpa only [sq_abs] using h

lemma derivative_radial_square_domination (α K : ℝ) :
    ∀ k : GW.Space, ‖((‖k‖^2 : ℝ) : ℂ)*(b α K k : ℂ)‖ ≤
      (highRegion K).indicator (fun k => |v α k|) k := by
  apply derivative_raw_domination α K (fun k => ‖k‖^2)
  intro k
  rw [abs_of_nonneg (sq_nonneg _)]

/- Source argument component Radial01. -/
def derivativeRadialSingularCoefficient (α K : ℝ) (k : GW.Space) : ℂ :=
  ((‖k‖^2 : ℝ) : ℂ)*(b α K k : ℂ)
lemma derivativeRadialSingularCoefficient_measurable (α K : ℝ) :
    Measurable (derivativeRadialSingularCoefficient α K) :=
  (Complex.continuous_ofReal.measurable.comp (measurable_norm.pow_const 2)).mul
    (Complex.continuous_ofReal.measurable.comp (b_measurable α K))
lemma derivativeRadialSingularCoefficient_domination (α K : ℝ) :
    ∀ᵐ k ∂(volume : Measure GW.Space), ‖derivativeRadialSingularCoefficient α K k‖ ≤
      (highRegion K).indicator (fun k => |v α k|) k :=
  Eventually.of_forall (derivative_radial_square_domination α K)

lemma derivative_finite_radial_coefficient (α K R : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (hR : K ≤ R) :
    grossFormFiniteSecondRadial (grossDressingCoefficient α K hα hK) R =
      convolutionCutoff (singularConvolutionData α K hα hK (derivativeRadialSingularCoefficient α K)
        (derivativeRadialSingularCoefficient_measurable α K) (derivativeRadialSingularCoefficient_domination α K)) R := by
  apply Lp.ext
  filter_upwards [grossFormFiniteSecondRadial_ae (grossDressingCoefficient α K hα hK) R,
    grossTruncateCoefficient_ae (grossDressingCoefficient α K hα hK) R,
    grossDressingCoefficient_ae α K hα hK,
    convolutionCutoff_ae (singularConvolutionData α K hα hK (derivativeRadialSingularCoefficient α K)
      (derivativeRadialSingularCoefficient_measurable α K) (derivativeRadialSingularCoefficient_domination α K)) R hR]
    with k hr ht hb hc
  change _ = (lowRegion R).indicator (derivativeRadialSingularCoefficient α K) k at hc
  rw [hr,ht,hc]
  by_cases hk : k ∈ lowRegion R
  · simp only [Set.indicator_of_mem hk]
    rw [hb]
    rfl
  · simp only [Set.indicator_of_notMem hk,mul_zero]

/- Source argument component Coefficients03. -/
def derivativeSingularCoefficient (α K : ℝ) (j : Fin 3) (k : GW.Space) : ℂ :=
  (((k j)^2 : ℝ) : ℂ)*(b α K k : ℂ)
lemma derivativeSingularCoefficient_measurable (α K : ℝ) (j : Fin 3) :
    Measurable (derivativeSingularCoefficient α K j) :=
  (Complex.continuous_ofReal.measurable.comp ((electronCoordinate_measurable j).pow_const 2)).mul
    (Complex.continuous_ofReal.measurable.comp (b_measurable α K))
lemma derivativeSingularCoefficient_domination (α K : ℝ) (j : Fin 3) :
    ∀ᵐ k ∂(volume : Measure GW.Space), ‖derivativeSingularCoefficient α K j k‖ ≤
      (highRegion K).indicator (fun k => |v α k|) k :=
  Eventually.of_forall (derivative_coordinate_square_domination α K j)

def derivativeCoefficient (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (j : Fin 3) : OneBoson :=
  weylMomentumCoefficient (grossDressingCoefficient α K hα hK) j (grossForm_momentum_memLp α K hα hK j)
def derivativeFiniteCoefficient (α K R : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (j : Fin 3) : OneBoson :=
  weylMomentumCoefficient (grossTruncateCoefficient (grossDressingCoefficient α K hα hK) R) j
    (grossForm_finite_first_memLp (grossDressingCoefficient α K hα hK) R j)
lemma derivativeFiniteCoefficient_tendsto (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (j : Fin 3) :
    Tendsto (fun R => derivativeFiniteCoefficient α K R hα hK j) atTop (𝓝 (derivativeCoefficient α K hα hK j)) :=
  grossFormMoment_truncate_tendsto (grossDressingCoefficient α K hα hK) j
    (grossForm_momentum_memLp α K hα hK j)
lemma derivativeFiniteCoefficient_second_memLp (α K R : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (j : Fin 3) :
    MemLp (fun k => (k j : ℂ)*derivativeFiniteCoefficient α K R hα hK j k) 2
      (volume : Measure GW.Space) :=
  grossForm_finite_second_memLp (grossDressingCoefficient α K hα hK) R j j

lemma derivativeFiniteCoefficient_second (α K R : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (hR : K ≤ R) (j : Fin 3) :
    weylMomentumCoefficient (derivativeFiniteCoefficient α K R hα hK j) j
      (derivativeFiniteCoefficient_second_memLp α K R hα hK j) =
    convolutionCutoff (singularConvolutionData α K hα hK (derivativeSingularCoefficient α K j)
      (derivativeSingularCoefficient_measurable α K j) (derivativeSingularCoefficient_domination α K j)) R := by
  apply Lp.ext
  filter_upwards [weylMomentumCoefficient_ae (derivativeFiniteCoefficient α K R hα hK j) j
    (derivativeFiniteCoefficient_second_memLp α K R hα hK j),
    weylMomentumCoefficient_ae (grossTruncateCoefficient (grossDressingCoefficient α K hα hK) R) j
      (grossForm_finite_first_memLp (grossDressingCoefficient α K hα hK) R j),
    grossTruncateCoefficient_ae (grossDressingCoefficient α K hα hK) R,
    grossDressingCoefficient_ae α K hα hK,
    convolutionCutoff_ae (singularConvolutionData α K hα hK (derivativeSingularCoefficient α K j)
      (derivativeSingularCoefficient_measurable α K j) (derivativeSingularCoefficient_domination α K j)) R hR]
    with k h₂ h₁ ht hb hc
  change derivativeFiniteCoefficient α K R hα hK j k = _ at h₁
  change _ = (lowRegion R).indicator (derivativeSingularCoefficient α K j) k at hc
  rw [h₂,h₁,ht,hc]
  by_cases hk : k ∈ lowRegion R
  · simp only [Set.indicator_of_mem hk]
    rw [hb]
    dsimp only [singularConvolutionData,derivativeSingularCoefficient]
    push_cast
    ring
  · simp only [Set.indicator_of_notMem hk,mul_zero]

/- Source argument component Finite02. -/
def derivativeFiniteDot (α K R : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (u : FreeGraphDomain) : Physical :=
  ∑ j : Fin 3, commutatorAnnihilatorRightMap (derivativeFiniteCoefficient α K R hα hK j) j
    (derivativeFiniteCoefficient_second_memLp α K R hα hK j) u

lemma derivative_finite_first_bound (α K R : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (u : FreeGraphDomain) :
    ‖∑ j : Fin 3, commutatorPhaseAnnihilatorMap (derivativeFiniteCoefficient α K R hα hK j)
      (commutatorGraphMomentumRootMap j u)‖ ≤ (1/2:ℝ)*grossSourceA α K hα hK*‖u‖ := by
  let f := grossDressingCoefficient α K hα hK
  have hb := derivative_annihilator_momentum_bound (fun j => derivativeFiniteCoefficient α K R hα hK j) u
  have he : Real.sqrt (∑ j : Fin 3, ‖derivativeFiniteCoefficient α K R hα hK j‖^2) =
      ‖grossFormRadialCoefficient (grossTruncateCoefficient f R) (fun j => grossForm_finite_first_memLp f R j)‖ := by
    change Real.sqrt (∑ j : Fin 3, ‖weylMomentumCoefficient (grossTruncateCoefficient f R) j
      (grossForm_finite_first_memLp f R j)‖^2) = _
    rw [← grossFormRadialCoefficient_norm_sq (grossTruncateCoefficient f R)
      (fun j => grossForm_finite_first_memLp f R j),Real.sqrt_sq (norm_nonneg _)]
  rw [he] at hb
  have hr := grossFormRadial_truncate_norm_le f (grossForm_momentum_memLp α K hα hK) R
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hr (by norm_num)) (norm_nonneg u))

lemma derivative_finite_radial_bound (α K R : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (hR : K ≤ R)
    (u : FreeGraphDomain) :
    ‖convolutionAnnihilationMap (grossFormFiniteSecondRadial (grossDressingCoefficient α K hα hK) R) u‖ ≤
      (1/2:ℝ)*Real.sqrt (coefficientTTail α K)*‖u‖ := by
  rw [derivative_finite_radial_coefficient α K R hα hK hR]
  let m := derivativeRadialSingularCoefficient α K
  let hm := derivativeRadialSingularCoefficient_measurable α K
  let hd := derivativeRadialSingularCoefficient_domination α K
  have hn := derivative_singular_finite_norm α K R hα hK m hm hd hR
  exact (ContinuousLinearMap.le_opNorm (singularFiniteMap α K hα hK m hm hd R) u).trans
    (mul_le_mul_of_nonneg_right hn (norm_nonneg u))

lemma derivative_finite_dot_bound (α K R : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (hR : K ≤ R)
    (u : FreeGraphDomain) :
    ‖derivativeFiniteDot α K R hα hK u‖ ≤
      (1/2:ℝ)*(grossSourceA α K hα hK+Real.sqrt (coefficientTTail α K))*‖u‖ := by
  change ‖∑ j : Fin 3, commutatorAnnihilatorRightMap
    (weylMomentumCoefficient (grossTruncateCoefficient (grossDressingCoefficient α K hα hK) R) j
      (grossForm_finite_first_memLp (grossDressingCoefficient α K hα hK) R j)) j
    (grossForm_finite_second_memLp (grossDressingCoefficient α K hα hK) R j j) u‖ ≤ _
  rw [derivative_finite_graph_sum]
  exact (norm_add_le _ _).trans ((add_le_add
    (derivative_finite_first_bound α K R hα hK u)
    (derivative_finite_radial_bound α K R hα hK hR u)).trans_eq (by ring))

/- Source argument component Component02. -/
def derivativeSingularMap (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (j : Fin 3) : FreeGraphDomain →L[ℂ] Physical :=
  singularAnnihilationMap α K hα hK (derivativeSingularCoefficient α K j)
    (derivativeSingularCoefficient_measurable α K j) (derivativeSingularCoefficient_domination α K j)

lemma derivative_infinite_component_graph (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (j : Fin 3) (u : FreeGraphDomain) :
    (commutatorPhaseAnnihilatorMap (derivativeCoefficient α K hα hK j) (commutatorGraphRootMap u),
      commutatorPhaseAnnihilatorMap (derivativeCoefficient α K hα hK j) (commutatorGraphMomentumRootMap j u)+
        derivativeSingularMap α K hα hK j u) ∈ (electronMomentumCoordinate j).graph := by
  let m := derivativeSingularCoefficient α K j
  let hm := derivativeSingularCoefficient_measurable α K j
  let hd := derivativeSingularCoefficient_domination α K j
  let ss : ℝ → Physical := fun R => singularFiniteMap α K hα hK m hm hd R u
  have hs : Tendsto ss atTop (𝓝 (derivativeSingularMap α K hα hK j u)) := by
    let ev : (FreeGraphDomain →L[ℂ] Physical) → Physical := fun T => T u
    have hev : Continuous ev := continuous_id.clm_apply continuous_const
    exact (hev.tendsto (singularAnnihilationMap α K hα hK m hm hd)).comp
      (singularAnnihilation_tendsto α K hα hK m hm hd)
  apply derivative_closed_component_limit
    (fun R => derivativeFiniteCoefficient α K R hα hK j) (derivativeCoefficient α K hα hK j) j
    (derivativeFiniteCoefficient_tendsto α K hα hK j)
    (fun R => derivativeFiniteCoefficient_second_memLp α K R hα hK j)
    ss (derivativeSingularMap α K hα hK j u) u hs
  filter_upwards [eventually_ge_atTop K] with R hR
  rw [derivative_graph_annihilator_identification,
    derivativeFiniteCoefficient_second α K R hα hK hR j]
  rfl

lemma derivative_finite_component_graph (α K R : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (j : Fin 3) (u : FreeGraphDomain) :
    (commutatorPhaseAnnihilatorMap (derivativeFiniteCoefficient α K R hα hK j) (commutatorGraphRootMap u),
      commutatorPhaseAnnihilatorMap (derivativeFiniteCoefficient α K R hα hK j) (commutatorGraphMomentumRootMap j u)+
        commutatorPhaseAnnihilatorMap (weylMomentumCoefficient (derivativeFiniteCoefficient α K R hα hK j) j
          (derivativeFiniteCoefficient_second_memLp α K R hα hK j)) (commutatorGraphRootMap u)) ∈
          (electronMomentumCoordinate j).graph :=
  commutatorAnnihilator_graph_all (derivativeFiniteCoefficient α K R hα hK j) j
    (derivativeFiniteCoefficient_second_memLp α K R hα hK j) u

/- Source argument component Limit03. -/
def derivativeInfiniteDot (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (u : FreeGraphDomain) : Physical :=
  ∑ j : Fin 3, (commutatorPhaseAnnihilatorMap (derivativeCoefficient α K hα hK j)
    (commutatorGraphMomentumRootMap j u)+derivativeSingularMap α K hα hK j u)

lemma derivative_finite_component_tendsto (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (j : Fin 3) (u : FreeGraphDomain) :
    Tendsto (fun R => commutatorAnnihilatorRightMap (derivativeFiniteCoefficient α K R hα hK j) j
      (derivativeFiniteCoefficient_second_memLp α K R hα hK j) u) atTop
      (𝓝 (commutatorPhaseAnnihilatorMap (derivativeCoefficient α K hα hK j)
        (commutatorGraphMomentumRootMap j u)+derivativeSingularMap α K hα hK j u)) := by
  let m := derivativeSingularCoefficient α K j
  let hm := derivativeSingularCoefficient_measurable α K j
  let hd := derivativeSingularCoefficient_domination α K j
  have ht : Tendsto (fun R => singularFiniteMap α K hα hK m hm hd R u) atTop
      (𝓝 (derivativeSingularMap α K hα hK j u)) := by
    let ev : (FreeGraphDomain →L[ℂ] Physical) → Physical := fun T => T u
    have hev : Continuous ev := continuous_id.clm_apply continuous_const
    exact (hev.tendsto (singularAnnihilationMap α K hα hK m hm hd)).comp
      (singularAnnihilation_tendsto α K hα hK m hm hd)
  have ha := derivative_annihilator_coefficient_tendsto
    (fun R => derivativeFiniteCoefficient α K R hα hK j) (derivativeCoefficient α K hα hK j)
    (derivativeFiniteCoefficient_tendsto α K hα hK j) (commutatorGraphMomentumRootMap j u)
  apply (ha.add ht).congr'
  filter_upwards [eventually_ge_atTop K] with R hR
  change _ = commutatorPhaseAnnihilatorMap (derivativeFiniteCoefficient α K R hα hK j)
      (commutatorGraphMomentumRootMap j u)+
    commutatorPhaseAnnihilatorMap (weylMomentumCoefficient (derivativeFiniteCoefficient α K R hα hK j) j
      (derivativeFiniteCoefficient_second_memLp α K R hα hK j)) (commutatorGraphRootMap u)
  rw [derivative_graph_annihilator_identification,derivativeFiniteCoefficient_second α K R hα hK hR j]
  rfl

lemma derivative_finite_dot_tendsto (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (u : FreeGraphDomain) :
    Tendsto (fun R => derivativeFiniteDot α K R hα hK u) atTop
      (𝓝 (derivativeInfiniteDot α K hα hK u)) := by
  exact tendsto_finsetSum _ (fun j _ => derivative_finite_component_tendsto α K hα hK j u)

lemma derivative_infinite_dot_bound (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (u : FreeGraphDomain) :
    ‖derivativeInfiniteDot α K hα hK u‖ ≤
      (1/2:ℝ)*(grossSourceA α K hα hK+Real.sqrt (coefficientTTail α K))*‖u‖ := by
  apply le_of_tendsto (derivative_finite_dot_tendsto α K hα hK u).norm
  filter_upwards [eventually_ge_atTop K] with R hR
  exact derivative_finite_dot_bound α K R hα hK hR u

/- Source argument component Decay02. -/
lemma derivative_source_a_bound (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    grossSourceA α K hα hK ≤ Real.sqrt (coefficientDTail α K) := by
  have h := Real.sqrt_le_sqrt (grossForm_radial_original_bound α K hα hK)
  rw [Real.sqrt_sq (norm_nonneg _)] at h
  exact h

def derivativeUniformBound (α : ℝ) (hα : 0 ≤ α) (K : ℝ) : ℝ :=
  if hK : 0 < K then (1/2:ℝ)*(grossSourceA α K hα hK+Real.sqrt (coefficientTTail α K)) else 0
lemma derivativeUniformBound_nonneg (α : ℝ) (hα : 0 ≤ α) (K : ℝ) :
    0 ≤ derivativeUniformBound α hα K := by
  unfold derivativeUniformBound
  split_ifs
  · exact mul_nonneg (by norm_num) (add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
  · exact le_rfl
lemma derivativeUniformBound_value (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    derivativeUniformBound α hα K = (1/2:ℝ)*(grossSourceA α K hα hK+Real.sqrt (coefficientTTail α K)) :=
  dif_pos hK
lemma derivativeUniformBound_tendsto (α : ℝ) (hα : 0 ≤ α) :
    Tendsto (derivativeUniformBound α hα) atTop (𝓝 0) := by
  have hd := (Real.continuous_sqrt.tendsto 0).comp (coefficientDTail_tendsto α hα)
  have ht := (Real.continuous_sqrt.tendsto 0).comp (coefficientTTail_tendsto α hα)
  have hh : Tendsto (fun K => (1/2:ℝ)*(Real.sqrt (coefficientDTail α K)+Real.sqrt (coefficientTTail α K)))
      atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero,Function.comp_def,zero_add,mul_zero] using (hd.add ht).const_mul (1/2:ℝ)
  apply squeeze_zero' (Eventually.of_forall (derivativeUniformBound_nonneg α hα)) _ hh
  filter_upwards [eventually_gt_atTop (0:ℝ)] with K hK
  rw [derivativeUniformBound_value α K hα hK]
  exact mul_le_mul_of_nonneg_left (add_le_add (derivative_source_a_bound α K hα hK) le_rfl) (by norm_num)

/- Source argument component Public01. -/
lemma derivative_source_input_norm (u : freeHamiltonian.domain) :
    ‖commutatorSourceGraphInput u‖ = ‖freeHamiltonian u+u.val‖ := by
  have he : freeGraphH0Input (commutatorSourceGraphInput u) = u := Subtype.ext rfl
  rw [freeGraph_norm_identity,he,commutatorSourceGraphInput_value]

lemma derivative_source_annihilator_graph (f : OneBoson) (u : freeHamiltonian.domain) :
    (u.val,commutatorPhaseAnnihilatorMap f (commutatorGraphRootMap (commutatorSourceGraphInput u))) ∈
      (generalizedAnnihilation (phaseMultiplicationKernel f)).graph := by
  have hg := commutatorPhaseAnnihilatorMap_graph f (commutatorGraphRootMap (commutatorSourceGraphInput u))
  rw [commutatorGraphRootMap_value,commutatorSourceGraphInput_value] at hg
  exact hg

lemma main_derivative_annihilation (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (u : freeHamiltonian.domain) :
    let U := commutatorSourceGraphInput u
    (∀ R : ℝ, K ≤ R →
      (∀ j : Fin 3,
        (u.val,commutatorPhaseAnnihilatorMap (derivativeFiniteCoefficient α K R hα hK j)
          (commutatorGraphRootMap U)) ∈
            (generalizedAnnihilation (phaseMultiplicationKernel (derivativeFiniteCoefficient α K R hα hK j))).graph ∧
        (commutatorPhaseAnnihilatorMap (derivativeFiniteCoefficient α K R hα hK j) (commutatorGraphRootMap U),
          commutatorAnnihilatorRightMap (derivativeFiniteCoefficient α K R hα hK j) j
            (derivativeFiniteCoefficient_second_memLp α K R hα hK j) U) ∈
              (electronMomentumCoordinate j).graph) ∧
      ‖derivativeFiniteDot α K R hα hK U‖ ≤
        (1/2:ℝ)*(grossSourceA α K hα hK+Real.sqrt (coefficientTTail α K))*‖freeHamiltonian u+u.val‖) ∧
    (∀ j : Fin 3,
      (u.val,commutatorPhaseAnnihilatorMap (derivativeCoefficient α K hα hK j) (commutatorGraphRootMap U)) ∈
        (generalizedAnnihilation (phaseMultiplicationKernel (derivativeCoefficient α K hα hK j))).graph ∧
      (commutatorPhaseAnnihilatorMap (derivativeCoefficient α K hα hK j) (commutatorGraphRootMap U),
        commutatorPhaseAnnihilatorMap (derivativeCoefficient α K hα hK j) (commutatorGraphMomentumRootMap j U)+
          derivativeSingularMap α K hα hK j U) ∈ (electronMomentumCoordinate j).graph) ∧
    ‖derivativeInfiniteDot α K hα hK U‖ ≤
      (1/2:ℝ)*(grossSourceA α K hα hK+Real.sqrt (coefficientTTail α K))*‖freeHamiltonian u+u.val‖ ∧
    Tendsto (derivativeUniformBound α hα) atTop (𝓝 0) := by
  dsimp only
  refine ⟨?_,?_,?_,derivativeUniformBound_tendsto α hα⟩
  · intro R hR
    refine ⟨?_,?_⟩
    · intro j
      exact ⟨derivative_source_annihilator_graph _ u,
        derivative_finite_component_graph α K R hα hK j (commutatorSourceGraphInput u)⟩
    · simpa only [derivative_source_input_norm] using
        derivative_finite_dot_bound α K R hα hK hR (commutatorSourceGraphInput u)
  · intro j
    exact ⟨derivative_source_annihilator_graph _ u,
      derivative_infinite_component_graph α K hα hK j (commutatorSourceGraphInput u)⟩
  · simpa only [derivative_source_input_norm] using
      derivative_infinite_dot_bound α K hα hK (commutatorSourceGraphInput u)

end GW.Gross
