module
public import GW.Gross.MainConjugation
public import GW.Gross.MainDerivativeAnnihilation
public import GW.Gross.MainFormH
public import GW.Model.ModelCutoffWitness

/-! Source main:dressed-small, manuscript6565–6661.
Actual finite and infinite dressed perturbations on the original H0 domain,
sharp relative bounds, symmetry, self-adjointness and uniform graph norms. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Gross
open GW.Model GW.Fock GW.Analysis

/- Source argument component Numeric02. -/
def dressedRelativeCoefficient (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) : ℝ :=
  2*grossSourceA α K hα hK+Real.sqrt (coefficientTTail α K)+4*Real.sqrt 2*(grossSourceA α K hα hK)^2
lemma dressed_T_sqrt_bound (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    Real.sqrt (coefficientTTail α K) ≤ Real.sqrt (convolutionConstant*α)*K^(-(1/4):ℝ) := by
  have hc : 0 ≤ convolutionConstant*α := mul_nonneg convolutionConstant_nonneg hα
  have hs : (Real.sqrt (convolutionConstant*α)*K^(-(1/4):ℝ))^2 =
      convolutionConstant*α*K^(-(1/2):ℝ) := by
    rw [mul_pow,Real.sq_sqrt hc,← Real.rpow_natCast (K^(-(1/4):ℝ)) 2,← Real.rpow_mul hK.le]
    norm_num
  have h := coefficientTTail_bound α K hα hK
  have ht := Real.sq_sqrt (coefficientTTail_nonneg α K hα hK)
  have hn : 0 ≤ Real.sqrt (convolutionConstant*α)*K^(-(1/4):ℝ) := by positivity
  nlinarith
lemma dressedRelativeCoefficient_numeric_bound (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    dressedRelativeCoefficient α K hα hK ≤
      2*Real.sqrt (14*unitBallVolume*α/K)+Real.sqrt (convolutionConstant*α)*K^(-(1/4):ℝ)+
        56*Real.sqrt 2*unitBallVolume*α/K := by
  have ha := derivative_source_a_bound α K hα hK
  have hD := coefficientDTail_bound α K hα hK
  have hs := Real.sqrt_le_sqrt hD
  have hsq := grossForm_radial_original_bound α K hα hK
  have ht := dressed_T_sqrt_bound α K hα hK
  have hm := mul_le_mul_of_nonneg_left (hsq.trans hD) (show 0 ≤ 4*Real.sqrt 2 by positivity)
  change (grossSourceA α K hα hK)^2 ≤ coefficientDTail α K at hsq
  unfold dressedRelativeCoefficient
  have he : 4*Real.sqrt 2*(14*unitBallVolume*α/K) = 56*Real.sqrt 2*unitBallVolume*α/K := by ring
  rw [he] at hm
  change 4*Real.sqrt 2*(grossSourceA α K hα hK)^2 ≤ 56*Real.sqrt 2*unitBallVolume*α/K at hm
  linarith
lemma dressedRelativeCoefficient_witness (α ε K : ℝ) (hα : 0 ≤ α) (hε : 0 < ε)
    (hK : operatorCutoffWitness α ε ≤ K) :
    dressedRelativeCoefficient α K hα
      (zero_lt_one.trans_le ((operatorCutoffWitness_ge_one α ε hα).trans hK)) ≤ ε :=
  (dressedRelativeCoefficient_numeric_bound α K hα
    (zero_lt_one.trans_le ((operatorCutoffWitness_ge_one α ε hα).trans hK))).trans
      (operatorCutoffWitness_bound α ε K hα hε hK)

/- Source argument component Relative03. -/
lemma dressedRelativeCoefficient_nonneg (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    0 ≤ dressedRelativeCoefficient α K hα hK := by
  unfold dressedRelativeCoefficient
  have ha : 0 ≤ grossSourceA α K hα hK := norm_nonneg _
  positivity

def dressedRelativeRemainderConstant (α ε : ℝ) : ℝ :=
  ε+28*unitBallVolume*α/operatorCutoffWitness α ε

lemma dressed_relative_from_graph_bound (α ε K : ℝ) (hα : 0 ≤ α) (hε : 0 < ε)
    (hK : operatorCutoffWitness α ε ≤ K) (u : freeHamiltonian.domain) (w : Physical)
    (hw : ‖w‖ ≤ dressedRelativeCoefficient α K hα
      (zero_lt_one.trans_le ((operatorCutoffWitness_ge_one α ε hα).trans hK))*‖freeHamiltonian u+u.val‖+
        2*coefficientETail α K*‖u.val‖) :
    ‖w‖ ≤ ε*‖freeHamiltonian u‖+dressedRelativeRemainderConstant α ε*‖u.val‖ := by
  have hW : 0 < operatorCutoffWitness α ε := zero_lt_one.trans_le (operatorCutoffWitness_ge_one α ε hα)
  have hKp : 0 < K := hW.trans_le hK
  have hr := dressedRelativeCoefficient_witness α ε K hα hε hK
  have hE := coefficientETail_antitone α hα hW hK
  have hEW := (coefficientETail_le_D α (operatorCutoffWitness α ε) hα hW).trans
    (coefficientDTail_bound α (operatorCutoffWitness α ε) hα hW)
  have hg := norm_add_le (freeHamiltonian u) u.val
  have hp := mul_le_mul_of_nonneg_left hg (dressedRelativeCoefficient_nonneg α K hα hKp)
  have hp' := mul_le_mul_of_nonneg_right hr (add_nonneg (norm_nonneg (freeHamiltonian u)) (norm_nonneg u.val))
  have he := mul_le_mul_of_nonneg_right (hE.trans hEW) (norm_nonneg u.val)
  have he2 : 2*coefficientETail α K*‖u.val‖ ≤
      (28*unitBallVolume*α/operatorCutoffWitness α ε)*‖u.val‖ :=
    calc
      _ = 2*(coefficientETail α K*‖u.val‖) := by ring
      _ ≤ 2*((14*unitBallVolume*α/operatorCutoffWitness α ε)*‖u.val‖) :=
        mul_le_mul_of_nonneg_left he (by norm_num)
      _ = _ := by ring
  unfold dressedRelativeRemainderConstant
  nlinarith only [hw,hp,hp',he2]

/- Source argument component Kato03. -/
def dressedGraphConstant (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) : ℝ :=
  1/8+2*coefficientETail α K+2*‖cutoffL2 α K hα hK‖+4*‖cutoffL2 α K hα hK‖^2
lemma dressedGraphConstant_nonneg (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    0 ≤ dressedGraphConstant α K hα hK := by
  unfold dressedGraphConstant
  have hE := coefficientETail_nonneg α K
  positivity

def dressedHamiltonianFromRemainder (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (V : freeHamiltonian.domain →ₗ[ℂ] Physical) : Physical →ₗ.[ℂ] Physical :=
  GW.Operators.perturbedOperator freeHamiltonian (constructionFieldRestriction (cutoffL2 α K hα hK)+V)

lemma dressed_uniform_perturbation_bound (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (hKS : standardGrossCutoff α ≤ K) (V : freeHamiltonian.domain →ₗ[ℂ] Physical)
    (hV : ∀ u, ‖V u‖ ≤ dressedRelativeCoefficient α K hα hK*‖freeHamiltonian u+u.val‖+
      2*coefficientETail α K*‖u.val‖) (u : freeHamiltonian.domain) :
    ‖(constructionFieldRestriction (cutoffL2 α K hα hK)+V) u‖ ≤
      (3/8:ℝ)*‖freeHamiltonian u‖+dressedGraphConstant α K hα hK*‖u.val‖ := by
  have hr := dressedRelativeCoefficient_witness α (1/8) K hα (by norm_num) hKS
  have hm := mul_le_mul_of_nonneg_right hr (norm_nonneg (freeHamiltonian u+u.val))
  have hg := norm_add_le (freeHamiltonian u) u.val
  have hl := constructionField_relative (cutoffL2 α K hα hK) (1/4) (by norm_num) u
  have ht := norm_add_le (constructionFieldRestriction (cutoffL2 α K hα hK) u) (V u)
  have hv := hV u
  change ‖constructionFieldRestriction (cutoffL2 α K hα hK) u+V u‖ ≤ _
  unfold dressedGraphConstant
  norm_num only [div_div] at hl
  nlinarith

lemma dressed_uniform_kato (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (hKS : standardGrossCutoff α ≤ K)
    (V : freeHamiltonian.domain →ₗ[ℂ] Physical)
    (hV : ∀ u, ‖V u‖ ≤ dressedRelativeCoefficient α K hα hK*‖freeHamiltonian u+u.val‖+
      2*coefficientETail α K*‖u.val‖)
    (hSym : ∀ u v : freeHamiltonian.domain, ⟪V u,v.val⟫_ℂ = ⟪u.val,V v⟫_ℂ) :
    GW.IsSelfAdjointOperator (dressedHamiltonianFromRemainder α K hα hK V) ∧
      ∀ u : freeHamiltonian.domain,
        ‖u.val‖+‖dressedHamiltonianFromRemainder α K hα hK V u‖ ≤
          (2+(3/8:ℝ)+dressedGraphConstant α K hα hK)*(‖u.val‖+‖freeHamiltonian u‖) ∧
        ‖u.val‖+‖freeHamiltonian u‖ ≤
          (1+(1+dressedGraphConstant α K hα hK)/(1-(3/8:ℝ)))*
            (‖u.val‖+‖dressedHamiltonianFromRemainder α K hα hK V u‖) := by
  have hs : ∀ u v : freeHamiltonian.domain,
      ⟪(constructionFieldRestriction (cutoffL2 α K hα hK)+V) u,v.val⟫_ℂ =
        ⟪u.val,(constructionFieldRestriction (cutoffL2 α K hα hK)+V) v⟫_ℂ := by
    intro u v
    simp only [LinearMap.add_apply,inner_add_left,inner_add_right,
      constructionFieldRestriction_symmetric,hSym]
  have h := GW.Operators.kato_rellich freeHamiltonian freeHamiltonian_selfadjoint
    (constructionFieldRestriction (cutoffL2 α K hα hK)+V) hs
    (a := 3/8) (b := dressedGraphConstant α K hα hK) (by norm_num) (by norm_num)
    (dressedGraphConstant_nonneg α K hα hK) (dressed_uniform_perturbation_bound α K hα hK hKS V hV)
  exact ⟨h.1,h.2.1⟩

/- Source argument component Counterterm02. -/
lemma dressed_counterterm_scalar_bound (a d : ℝ) (hd : 1 ≤ d) :
    ‖a^2*(1/d^2-2/d)‖ ≤ 2*(a^2/d) := by
  have hd0 : 0 < d := zero_lt_one.trans_le hd
  have hx : 0 ≤ 1/d^2 := by positivity
  have hy : 1/d^2 ≤ 2/d := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hd0) hd0).mpr
    nlinarith
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg _),abs_of_nonpos (sub_nonpos.mpr hy)]
  have hp := mul_nonneg (sq_nonneg a) hx
  simp only [div_eq_mul_inv] at *
  nlinarith

def dressedCountertermDensity (α : ℝ) (S : Set GW.Space) (k : GW.Space) : ℝ :=
  S.indicator (fun k => (v α k)^2*(1/(1+‖k‖^2)^2-2/(1+‖k‖^2))) k
lemma dressedCountertermDensity_bound (α K : ℝ) (S : Set GW.Space) (hS : S ⊆ highRegion K) (k : GW.Space) :
    ‖dressedCountertermDensity α S k‖ ≤ 2*grossCoefficientMajorant α K k := by
  by_cases hk : k ∈ S
  · rw [dressedCountertermDensity,Set.indicator_of_mem hk,grossCoefficientMajorant,Set.indicator_of_mem (hS hk)]
    exact dressed_counterterm_scalar_bound (v α k) (1+‖k‖^2) (by nlinarith [sq_nonneg ‖k‖])
  · rw [dressedCountertermDensity,Set.indicator_of_notMem hk,norm_zero]
    apply mul_nonneg (by norm_num)
    exact Set.indicator_nonneg (fun k _ => div_nonneg (sq_nonneg _) (by positivity)) k
lemma dressedCountertermDensity_measurable (α : ℝ) (S : Set GW.Space) (hS : MeasurableSet S) :
    Measurable (dressedCountertermDensity α S) := by
  apply Measurable.indicator _ hS
  have hm := v_measurable α
  fun_prop
lemma dressedCountertermDensity_integrable (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (S : Set GW.Space) (hS : MeasurableSet S) (hSK : S ⊆ highRegion K) :
    Integrable (dressedCountertermDensity α S) volume :=
  ((grossCoefficientMajorant_integrable α K hα hK).const_mul 2).mono'
    (dressedCountertermDensity_measurable α S hS).aestronglyMeasurable
    (Eventually.of_forall (dressedCountertermDensity_bound α K S hSK))
lemma dressedCounterterm_integral_bound (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (S : Set GW.Space) (hS : MeasurableSet S) (hSK : S ⊆ highRegion K) :
    ‖∫ k, dressedCountertermDensity α S k ∂volume‖ ≤ 2*coefficientETail α K := by
  calc
    _ ≤ ∫ k, ‖dressedCountertermDensity α S k‖ ∂volume := norm_integral_le_integral_norm _
    _ ≤ ∫ k, 2*grossCoefficientMajorant α K k ∂volume :=
      integral_mono (dressedCountertermDensity_integrable α K hα hK S hS hSK).norm
        ((grossCoefficientMajorant_integrable α K hα hK).const_mul 2)
        (dressedCountertermDensity_bound α K S hSK)
    _ = _ := by rw [integral_const_mul,grossCoefficientMajorant_integral α K hα hK]

def dressedInfiniteCounterterm (α K : ℝ) : ℝ :=
  ∫ k, dressedCountertermDensity α (highRegion K) k ∂volume
lemma dressedInfiniteCounterterm_bound (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    |dressedInfiniteCounterterm α K| ≤ 2*coefficientETail α K := by
  exact dressedCounterterm_integral_bound α K hα hK (highRegion K) (highRegion_measurable K) (fun _ h => h)
lemma dressedFiniteCounterterm_bound (α K R : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    |conjugationCounterterm α K R| ≤ 2*coefficientETail α K := by
  have h := dressedCounterterm_integral_bound α K hα hK (highRegion K ∩ lowRegion R)
    ((highRegion_measurable K).inter (lowRegion_measurable R)) (fun _ h => h.1)
  change ‖∫ k, (highRegion K ∩ lowRegion R).indicator _ k ∂volume‖ ≤ _ at h
  rw [integral_indicator ((highRegion_measurable K).inter (lowRegion_measurable R))] at h
  exact h

/- Source argument component BasicBounds02. -/
lemma dressed_creator_momentum_bound (fs : Fin 3 → OneBoson) (u : FreeGraphDomain) :
    ‖∑ j : Fin 3, commutatorPhaseCreatorMap (fs j) (commutatorGraphMomentumRootMap j u)‖ ≤
      (1/2:ℝ)*Real.sqrt (∑ j : Fin 3, ‖fs j‖^2)*‖u‖ := by
  have hb := grossMixed_collective_bound (show freeGraphOperator.domain from u)
  have hs : (∑ j : Fin 3, ‖fs j‖*‖commutatorGraphMomentumRootMap j u‖) ≤
      Real.sqrt (∑ j : Fin 3, ‖fs j‖^2)*
        Real.sqrt (∑ j : Fin 3, ‖physicalShiftedNumberPower (1/2) (freeGraphMomentumShiftedRoot u j)‖^2) := by
    simp_rw [grossGraphMomentumRoot_norm]
    exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  calc
    _ ≤ ∑ j : Fin 3, ‖commutatorPhaseCreatorMap (fs j) (commutatorGraphMomentumRootMap j u)‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin 3, ‖fs j‖*‖commutatorGraphMomentumRootMap j u‖ :=
      Finset.sum_le_sum (fun j _ => commutatorPhaseCreatorMap_bound (fs j) (commutatorGraphMomentumRootMap j u))
    _ ≤ _ := hs
    _ ≤ Real.sqrt (∑ j : Fin 3, ‖fs j‖^2)*((1/2:ℝ)*‖freeGraphOperator u‖) :=
      mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)
    _ = _ := by rw [freeGraphDomain_norm]; ring

lemma dressed_field_square_bound (fs : Fin 3 → OneBoson) (u : freeHamiltonian.domain) :
    ‖∑ j : Fin 3, conjugationSquareMap (fs j) u‖ ≤
      4*Real.sqrt 2*(∑ j : Fin 3, ‖fs j‖^2)*‖conjugationSourceGraph u‖ := by
  simp_rw [conjugationSquareMap_value]
  have hn := grossGraphNumberOne_norm (conjugationSourceGraph u)
  rw [grossNumberOne_norm] at hn
  exact (phaseFieldSquare_vector_bound fs (grossGraphNumberOne (conjugationSourceGraph u))).trans
    (mul_le_mul_of_nonneg_left hn (by positivity))

/- Source argument component Maps03. -/
def dressedInfiniteDerivative (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) : FreeGraphDomain →L[ℂ] Physical :=
  ∑ j : Fin 3, ((commutatorPhaseAnnihilatorMap (derivativeCoefficient α K hα hK j)).comp
    (commutatorGraphMomentumRootMap j)+derivativeSingularMap α K hα hK j)
lemma dressedInfiniteDerivative_value (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (u : FreeGraphDomain) :
    dressedInfiniteDerivative α K hα hK u = derivativeInfiniteDot α K hα hK u := by
  simp only [dressedInfiniteDerivative,derivativeInfiniteDot,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply]

def dressedInfiniteRemainder (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) : freeHamiltonian.domain →ₗ[ℂ] Physical :=
  -(2 • conjugationCreatorMomentumMap (grossDressingCoefficient α K hα hK) (grossForm_momentum_memLp α K hα hK))-
    2 • (dressedInfiniteDerivative α K hα hK).toLinearMap.comp conjugationSourceGraph+
    (∑ j : Fin 3,conjugationSquareMap (derivativeCoefficient α K hα hK j))+
    (dressedInfiniteCounterterm α K : ℂ) • freeHamiltonian.domain.subtype
lemma dressedInfiniteRemainder_value (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (u : freeHamiltonian.domain) :
    dressedInfiniteRemainder α K hα hK u =
      -(2 • (∑ j : Fin 3,commutatorPhaseCreatorMap (derivativeCoefficient α K hα hK j)
        (commutatorGraphMomentumRootMap j (conjugationSourceGraph u))))-
      2 • derivativeInfiniteDot α K hα hK (conjugationSourceGraph u)+
      (∑ j : Fin 3,conjugationSquareMap (derivativeCoefficient α K hα hK j) u)+
      (dressedInfiniteCounterterm α K : ℂ) • u.val := by
  simp only [dressedInfiniteRemainder,conjugationCreatorMomentumMap,
    LinearMap.add_apply,LinearMap.sub_apply,LinearMap.neg_apply,LinearMap.smul_apply,
    LinearMap.sum_apply,LinearMap.comp_apply,ContinuousLinearMap.coe_coe,Submodule.subtype_apply,
    dressedInfiniteDerivative_value,derivativeCoefficient]

lemma dressed_infinite_coefficient_mass (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    (∑ j : Fin 3, ‖derivativeCoefficient α K hα hK j‖^2) = (grossSourceA α K hα hK)^2 :=
  (grossFormRadialCoefficient_norm_sq (grossDressingCoefficient α K hα hK)
    (grossForm_momentum_memLp α K hα hK)).symm
lemma dressed_finite_coefficient_mass (α K R : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    (∑ j : Fin 3, ‖derivativeFiniteCoefficient α K R hα hK j‖^2) ≤ (grossSourceA α K hα hK)^2 := by
  let f := grossDressingCoefficient α K hα hK
  change (∑ j : Fin 3, ‖weylMomentumCoefficient (grossTruncateCoefficient f R) j
    (grossForm_finite_first_memLp f R j)‖^2) ≤ _
  rw [← grossFormRadialCoefficient_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) (grossFormRadial_truncate_norm_le f (grossForm_momentum_memLp α K hα hK) R) 2

/- Source argument component Triangle02. -/
open GW.Fock

lemma dressed_remainder_triangle (c a s u : Physical) (C : ℝ) :
    ‖-((2:ℂ) • c)-(2:ℂ) • a+s+(C:ℂ) • u‖ ≤
      2*‖c‖+2*‖a‖+‖s‖+|C| *‖u‖ := by
  have h₁ := norm_add_le (-((2:ℂ) • c)-(2:ℂ) • a+s) ((C:ℂ) • u)
  have h₂ := norm_add_le (-((2:ℂ) • c)-(2:ℂ) • a) s
  have h₃ := norm_sub_le (-((2:ℂ) • c)) ((2:ℂ) • a)
  simp only [norm_neg,norm_smul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs] at h₁ h₂ h₃
  linarith

/- Source argument component VCore01. -/
lemma dressed_first_bound_from_mass (fs : Fin 3 → OneBoson) (u : FreeGraphDomain) (a : ℝ)
    (ha : 0 ≤ a) (hm : (∑ j : Fin 3, ‖fs j‖^2) ≤ a^2) :
    ‖∑ j : Fin 3,commutatorPhaseCreatorMap (fs j) (commutatorGraphMomentumRootMap j u)‖ ≤ (1/2:ℝ)*a*‖u‖ := by
  have hs := Real.sqrt_le_sqrt hm
  rw [Real.sqrt_sq ha] at hs
  exact (dressed_creator_momentum_bound fs u).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hs (by norm_num)) (norm_nonneg u))

lemma dressed_square_bound_from_mass (fs : Fin 3 → OneBoson) (u : freeHamiltonian.domain) (a : ℝ)
    (hm : (∑ j : Fin 3, ‖fs j‖^2) ≤ a^2) :
    ‖∑ j : Fin 3,conjugationSquareMap (fs j) u‖ ≤ 4*Real.sqrt 2*a^2*‖conjugationSourceGraph u‖ := by
  exact (dressed_field_square_bound fs u).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hm (by positivity)) (norm_nonneg _))

lemma dressed_remainder_parts_bound (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (c a s u : Physical) (C g : ℝ)
    (hc : ‖c‖ ≤ (1/2:ℝ)*grossSourceA α K hα hK*g)
    (ha : ‖a‖ ≤ (1/2:ℝ)*(grossSourceA α K hα hK+Real.sqrt (coefficientTTail α K))*g)
    (hs : ‖s‖ ≤ 4*Real.sqrt 2*(grossSourceA α K hα hK)^2*g)
    (hC : |C| ≤ 2*coefficientETail α K) :
    ‖-((2:ℂ) • c)-(2:ℂ) • a+s+(C:ℂ) • u‖ ≤
      dressedRelativeCoefficient α K hα hK*g+2*coefficientETail α K*‖u‖ := by
  have h := dressed_remainder_triangle c a s u C
  have hCs := mul_le_mul_of_nonneg_right hC (norm_nonneg u)
  unfold dressedRelativeCoefficient
  nlinarith

/- Source argument component InfiniteBound03. -/
lemma dressedInfiniteCreator_bound (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (u : freeHamiltonian.domain) :
    ‖∑ j : Fin 3,commutatorPhaseCreatorMap (derivativeCoefficient α K hα hK j)
      (commutatorGraphMomentumRootMap j (conjugationSourceGraph u))‖ ≤
        (1/2:ℝ)*grossSourceA α K hα hK*‖conjugationSourceGraph u‖ :=
  dressed_first_bound_from_mass (derivativeCoefficient α K hα hK) (conjugationSourceGraph u)
    (grossSourceA α K hα hK) (norm_nonneg _) (dressed_infinite_coefficient_mass α K hα hK).le
lemma dressedInfiniteSquare_bound (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (u : freeHamiltonian.domain) :
    ‖∑ j : Fin 3,conjugationSquareMap (derivativeCoefficient α K hα hK j) u‖ ≤
      4*Real.sqrt 2*(grossSourceA α K hα hK)^2*‖conjugationSourceGraph u‖ :=
  dressed_square_bound_from_mass (derivativeCoefficient α K hα hK) u (grossSourceA α K hα hK)
    (dressed_infinite_coefficient_mass α K hα hK).le

lemma dressedInfiniteRemainder_bound (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (u : freeHamiltonian.domain) :
    ‖dressedInfiniteRemainder α K hα hK u‖ ≤
      dressedRelativeCoefficient α K hα hK*‖freeHamiltonian u+u.val‖+2*coefficientETail α K*‖u.val‖ := by
  let c : Physical := ∑ j : Fin 3,commutatorPhaseCreatorMap (derivativeCoefficient α K hα hK j)
    (commutatorGraphMomentumRootMap j (conjugationSourceGraph u))
  let a : Physical := derivativeInfiniteDot α K hα hK (conjugationSourceGraph u)
  let s : Physical := ∑ j : Fin 3,conjugationSquareMap (derivativeCoefficient α K hα hK j) u
  have h := dressed_remainder_parts_bound α K hα hK c a s u.val (dressedInfiniteCounterterm α K)
    ‖conjugationSourceGraph u‖ (dressedInfiniteCreator_bound α K hα hK u)
    (derivative_infinite_dot_bound α K hα hK (conjugationSourceGraph u))
    (dressedInfiniteSquare_bound α K hα hK u) (dressedInfiniteCounterterm_bound α K hα hK)
  have hn : ‖conjugationSourceGraph u‖ = ‖freeHamiltonian u+u.val‖ := derivative_source_input_norm u
  rw [hn] at h
  have he := congrArg norm (dressedInfiniteRemainder_value α K hα hK u)
  have hcc : (2:ℂ) • c = (2:ℕ) • c := Nat.cast_smul_eq_nsmul ℂ 2 c
  have hca : (2:ℂ) • a = (2:ℕ) • a := Nat.cast_smul_eq_nsmul ℂ 2 a
  rw [hcc,hca] at h
  exact he.trans_le h

/- Source argument component FiniteBound04. -/
lemma dressedFiniteRemainder_bound (α K R : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (hR : K ≤ R)
    (u : freeHamiltonian.domain) :
    ‖conjugationFiniteRemainder α K R hα hK u‖ ≤
      dressedRelativeCoefficient α K hα hK*‖freeHamiltonian u+u.val‖+2*coefficientETail α K*‖u.val‖ := by
  change ‖conjugationRemainder (grossTruncateCoefficient (grossDressingCoefficient α K hα hK) R)
    (grossForm_finite_first_memLp (grossDressingCoefficient α K hα hK) R)
    (fun i j => grossForm_finite_second_memLp (grossDressingCoefficient α K hα hK) R j i)
    (conjugationCounterterm α K R) u‖ ≤ _
  rw [conjugationRemainder_value]
  have hc := dressed_first_bound_from_mass (derivativeFiniteCoefficient α K R hα hK) (conjugationSourceGraph u)
    (grossSourceA α K hα hK) (norm_nonneg _) (dressed_finite_coefficient_mass α K R hα hK)
  have hs := dressed_square_bound_from_mass (derivativeFiniteCoefficient α K R hα hK) u (grossSourceA α K hα hK)
    (dressed_finite_coefficient_mass α K R hα hK)
  have ha := derivative_finite_dot_bound α K R hα hK hR (conjugationSourceGraph u)
  have hn : ‖conjugationSourceGraph u‖ = ‖freeHamiltonian u+u.val‖ := derivative_source_input_norm u
  let c : Physical := ∑ j : Fin 3,commutatorPhaseCreatorMap (derivativeFiniteCoefficient α K R hα hK j)
    (commutatorGraphMomentumRootMap j (conjugationSourceGraph u))
  let a : Physical := derivativeFiniteDot α K R hα hK (conjugationSourceGraph u)
  let s : Physical := ∑ j : Fin 3,conjugationSquareMap (derivativeFiniteCoefficient α K R hα hK j) u
  have hb := dressed_remainder_parts_bound α K hα hK c a s u.val (conjugationCounterterm α K R)
    ‖conjugationSourceGraph u‖ hc ha hs (dressedFiniteCounterterm_bound α K R hα hK)
  rw [hn] at hb
  have hcc : (2:ℂ) • c = (2:ℕ) • c := Nat.cast_smul_eq_nsmul ℂ 2 c
  have hca : (2:ℂ) • a = (2:ℕ) • a := Nat.cast_smul_eq_nsmul ℂ 2 a
  rw [hcc,hca] at hb
  exact hb

/- Source argument component Pairings01. -/
lemma dressed_momentum_symmetric (j : Fin 3) :
    (electronMomentumCoordinate j).IsFormalAdjoint (electronMomentumCoordinate j) := by
  have hA := physicalSectorMultiplier_selfadjoint (fun _ => electronCoordinate_measurable j)
  exact (congrArg (fun A : Physical →ₗ.[ℂ] Physical => A.IsFormalAdjoint (electronMomentumCoordinate j)) hA.2).mp
    (LinearPMap.adjoint_isFormalAdjoint hA.1)

lemma dressed_creator_derivative_pairing (f : OneBoson) (j : Fin 3)
    (u v : freeHamiltonian.domain) (pv : Physical)
    (hpv : (commutatorPhaseAnnihilatorMap f (commutatorGraphRootMap (conjugationSourceGraph v)),pv) ∈
      (electronMomentumCoordinate j).graph) :
    ⟪commutatorPhaseCreatorMap f (commutatorGraphMomentumRootMap j (conjugationSourceGraph u)),v.val⟫_ℂ =
      ⟪u.val,pv⟫_ℂ := by
  have h := uvPhase_pairing f (commutatorGraphMomentumRootMap j (conjugationSourceGraph u))
    (commutatorGraphRootMap (conjugationSourceGraph v))
  rw [commutatorGraphMomentumRootMap_value,conjugationSourceRoot_value] at h
  have hg : (u.val,electronMomentumCoordinate j (commutatorMomentumInput (conjugationSourceGraph u) j)) ∈
      (electronMomentumCoordinate j).graph :=
    (electronMomentumCoordinate j).mem_graph (commutatorMomentumInput (conjugationSourceGraph u) j)
  exact h.trans (uvFormalAdjoint_graph_pairing _ _ (dressed_momentum_symmetric j) _ _ _ _ hg hpv)

lemma dressed_square_pairing (f : OneBoson) (u v : freeHamiltonian.domain) :
    ⟪conjugationSquareMap f u,v.val⟫_ℂ = ⟪u.val,conjugationSquareMap f v⟫_ℂ := by
  have h₁ := uvFormalAdjoint_graph_pairing _ _ (generalizedField_symmetric (phaseMultiplicationKernel f))
    _ _ _ _ (conjugationSquareMap_graph f u) (constructionFieldRestriction_graph f v)
  have h₂ := uvFormalAdjoint_graph_pairing _ _ (generalizedField_symmetric (phaseMultiplicationKernel f))
    _ _ _ _ (constructionFieldRestriction_graph f u) (conjugationSquareMap_graph f v)
  exact h₁.trans h₂

/- Source argument component Symmetry03. -/
lemma dressed_sum_cross_pairing (fs : Fin 3 → OneBoson)
    (pa : Fin 3 → freeHamiltonian.domain → Physical)
    (hg : ∀ j u, (commutatorPhaseAnnihilatorMap (fs j)
      (commutatorGraphRootMap (conjugationSourceGraph u)),pa j u) ∈ (electronMomentumCoordinate j).graph)
    (u v : freeHamiltonian.domain) :
    ⟪∑ j : Fin 3,commutatorPhaseCreatorMap (fs j) (commutatorGraphMomentumRootMap j (conjugationSourceGraph u)),v.val⟫_ℂ =
      ⟪u.val,∑ j : Fin 3,pa j v⟫_ℂ := by
  simp only [sum_inner,inner_sum]
  exact Finset.sum_congr rfl (fun j _ => dressed_creator_derivative_pairing (fs j) j u v (pa j v) (hg j v))

lemma dressed_sum_square_symmetric (fs : Fin 3 → OneBoson) (u v : freeHamiltonian.domain) :
    ⟪∑ j : Fin 3,conjugationSquareMap (fs j) u,v.val⟫_ℂ =
      ⟪u.val,∑ j : Fin 3,conjugationSquareMap (fs j) v⟫_ℂ := by
  simp only [sum_inner,inner_sum]
  exact Finset.sum_congr rfl (fun j _ => dressed_square_pairing (fs j) u v)

lemma dressed_combination_symmetric (c a s : freeHamiltonian.domain → Physical) (C : ℝ)
    (hca : ∀ u v, ⟪c u,v.val⟫_ℂ = ⟪u.val,a v⟫_ℂ)
    (hs : ∀ u v, ⟪s u,v.val⟫_ℂ = ⟪u.val,s v⟫_ℂ)
    (u v : freeHamiltonian.domain) :
    ⟪-((2:ℂ) • c u)-(2:ℂ) • a u+s u+(C:ℂ) • u.val,v.val⟫_ℂ =
      ⟪u.val,-((2:ℂ) • c v)-(2:ℂ) • a v+s v+(C:ℂ) • v.val⟫_ℂ := by
  have hac : ⟪a u,v.val⟫_ℂ = ⟪u.val,c v⟫_ℂ := by
    have h := congrArg (starRingEnd ℂ) (hca v u)
    simpa only [inner_conj_symm] using h.symm
  simp only [inner_add_left,inner_add_right,inner_sub_left,inner_sub_right,inner_neg_left,inner_neg_right,
    inner_smul_left,inner_smul_right,map_ofNat,Complex.conj_ofReal]
  rw [hca u v,hac,hs u v]
  ring

/- Source argument component NatSymmetry01. -/
open GW.Fock
lemma dressed_combination_nsmul_symmetric (c a s : freeHamiltonian.domain → Physical) (C : ℝ)
    (hca : ∀ u v, ⟪c u,v.val⟫_ℂ = ⟪u.val,a v⟫_ℂ)
    (hs : ∀ u v, ⟪s u,v.val⟫_ℂ = ⟪u.val,s v⟫_ℂ)
    (u v : freeHamiltonian.domain) :
    ⟪-((2:ℕ) • c u)-(2:ℕ) • a u+s u+(C:ℂ) • u.val,v.val⟫_ℂ =
      ⟪u.val,-((2:ℕ) • c v)-(2:ℕ) • a v+s v+(C:ℂ) • v.val⟫_ℂ := by
  have h := dressed_combination_symmetric c a s C hca hs u v
  have hc (w : freeHamiltonian.domain) : (2:ℂ) • c w = (2:ℕ) • c w := Nat.cast_smul_eq_nsmul ℂ 2 (c w)
  have ha (w : freeHamiltonian.domain) : (2:ℂ) • a w = (2:ℕ) • a w := Nat.cast_smul_eq_nsmul ℂ 2 (a w)
  rw [hc u,ha u,hc v,ha v] at h
  exact h

/- Source argument component InfiniteSymmetry02. -/
lemma dressedInfiniteRemainder_symmetric (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (u v : freeHamiltonian.domain) :
    ⟪dressedInfiniteRemainder α K hα hK u,v.val⟫_ℂ =
      ⟪u.val,dressedInfiniteRemainder α K hα hK v⟫_ℂ := by
  let fs := derivativeCoefficient α K hα hK
  let pa : Fin 3 → freeHamiltonian.domain → Physical := fun j w =>
    commutatorPhaseAnnihilatorMap (fs j) (commutatorGraphMomentumRootMap j (conjugationSourceGraph w))+
      derivativeSingularMap α K hα hK j (conjugationSourceGraph w)
  have hg (j : Fin 3) (w : freeHamiltonian.domain) :
      (commutatorPhaseAnnihilatorMap (fs j) (commutatorGraphRootMap (conjugationSourceGraph w)),pa j w) ∈
        (electronMomentumCoordinate j).graph :=
    derivative_infinite_component_graph α K hα hK j (conjugationSourceGraph w)
  let c : freeHamiltonian.domain → Physical := fun w => ∑ j : Fin 3,
    commutatorPhaseCreatorMap (fs j) (commutatorGraphMomentumRootMap j (conjugationSourceGraph w))
  let a : freeHamiltonian.domain → Physical := fun w => derivativeInfiniteDot α K hα hK (conjugationSourceGraph w)
  let s : freeHamiltonian.domain → Physical := fun w => ∑ j : Fin 3,conjugationSquareMap (fs j) w
  have hca : ∀ w z : freeHamiltonian.domain, ⟪c w,z.val⟫_ℂ = ⟪w.val,a z⟫_ℂ :=
    dressed_sum_cross_pairing fs pa hg
  have hs : ∀ w z : freeHamiltonian.domain, ⟪s w,z.val⟫_ℂ = ⟪w.val,s z⟫_ℂ :=
    dressed_sum_square_symmetric fs
  have h := dressed_combination_nsmul_symmetric c a s (dressedInfiniteCounterterm α K) hca hs u v
  rw [dressedInfiniteRemainder_value,dressedInfiniteRemainder_value]
  exact h

/- Source argument component FiniteSymmetry02. -/
lemma dressedFiniteRemainder_symmetric (α K R : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (u v : freeHamiltonian.domain) :
    ⟪conjugationFiniteRemainder α K R hα hK u,v.val⟫_ℂ =
      ⟪u.val,conjugationFiniteRemainder α K R hα hK v⟫_ℂ := by
  let fs := derivativeFiniteCoefficient α K R hα hK
  let pa : Fin 3 → freeHamiltonian.domain → Physical := fun j w =>
    commutatorAnnihilatorRightMap (fs j) j (derivativeFiniteCoefficient_second_memLp α K R hα hK j)
      (conjugationSourceGraph w)
  have hg (j : Fin 3) (w : freeHamiltonian.domain) :
      (commutatorPhaseAnnihilatorMap (fs j) (commutatorGraphRootMap (conjugationSourceGraph w)),pa j w) ∈
        (electronMomentumCoordinate j).graph :=
    commutatorAnnihilator_graph_all (fs j) j (derivativeFiniteCoefficient_second_memLp α K R hα hK j)
      (conjugationSourceGraph w)
  let c : freeHamiltonian.domain → Physical := fun w => ∑ j : Fin 3,
    commutatorPhaseCreatorMap (fs j) (commutatorGraphMomentumRootMap j (conjugationSourceGraph w))
  let a : freeHamiltonian.domain → Physical := fun w => derivativeFiniteDot α K R hα hK (conjugationSourceGraph w)
  let s : freeHamiltonian.domain → Physical := fun w => ∑ j : Fin 3,conjugationSquareMap (fs j) w
  have hca : ∀ w z : freeHamiltonian.domain, ⟪c w,z.val⟫_ℂ = ⟪w.val,a z⟫_ℂ :=
    dressed_sum_cross_pairing fs pa hg
  have hs : ∀ w z : freeHamiltonian.domain, ⟪s w,z.val⟫_ℂ = ⟪w.val,s z⟫_ℂ :=
    dressed_sum_square_symmetric fs
  have h := dressed_combination_nsmul_symmetric c a s (conjugationCounterterm α K R) hca hs u v
  let f := grossTruncateCoefficient (grossDressingCoefficient α K hα hK) R
  let hj := grossForm_finite_first_memLp (grossDressingCoefficient α K hα hK) R
  let hjj := fun i j => grossForm_finite_second_memLp (grossDressingCoefficient α K hα hK) R j i
  change ⟪conjugationRemainder f hj hjj (conjugationCounterterm α K R) u,v.val⟫_ℂ =
    ⟪u.val,conjugationRemainder f hj hjj (conjugationCounterterm α K R) v⟫_ℂ
  rw [conjugationRemainder_value,conjugationRemainder_value]
  exact h

/- Source argument component Hamiltonians01. -/
def dressedInfiniteHamiltonian (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) : Physical →ₗ.[ℂ] Physical :=
  dressedHamiltonianFromRemainder α K hα hK (dressedInfiniteRemainder α K hα hK)
lemma dressedInfiniteHamiltonian_domain (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    (dressedInfiniteHamiltonian α K hα hK).domain = freeHamiltonian.domain := rfl
lemma dressedFiniteHamiltonian_eq (α K R : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    dressedHamiltonianFromRemainder α K hα hK (conjugationFiniteRemainder α K R hα hK) =
      conjugationDressedHamiltonian α K R hα hK := rfl

lemma dressedInfiniteHamiltonian_selfadjoint (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (hKS : standardGrossCutoff α ≤ K) :
    GW.IsSelfAdjointOperator (dressedInfiniteHamiltonian α K hα hK) :=
  (dressed_uniform_kato α K hα hK hKS (dressedInfiniteRemainder α K hα hK)
    (dressedInfiniteRemainder_bound α K hα hK) (dressedInfiniteRemainder_symmetric α K hα hK)).1
lemma dressedFiniteHamiltonian_selfadjoint (α K R : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (hKS : standardGrossCutoff α ≤ K) (hR : K ≤ R) :
    GW.IsSelfAdjointOperator (conjugationDressedHamiltonian α K R hα hK) :=
  (dressed_uniform_kato α K hα hK hKS (conjugationFiniteRemainder α K R hα hK)
    (dressedFiniteRemainder_bound α K R hα hK hR) (dressedFiniteRemainder_symmetric α K R hα hK)).1

lemma dressedInfiniteHamiltonian_graph_bounds (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (hKS : standardGrossCutoff α ≤ K) (u : freeHamiltonian.domain) :
    ‖u.val‖+‖dressedInfiniteHamiltonian α K hα hK u‖ ≤
        (2+(3/8:ℝ)+dressedGraphConstant α K hα hK)*(‖u.val‖+‖freeHamiltonian u‖) ∧
    ‖u.val‖+‖freeHamiltonian u‖ ≤
      (1+(1+dressedGraphConstant α K hα hK)/(1-(3/8:ℝ)))*
        (‖u.val‖+‖dressedInfiniteHamiltonian α K hα hK u‖) :=
  (dressed_uniform_kato α K hα hK hKS (dressedInfiniteRemainder α K hα hK)
    (dressedInfiniteRemainder_bound α K hα hK) (dressedInfiniteRemainder_symmetric α K hα hK)).2 u
lemma dressedFiniteHamiltonian_graph_bounds (α K R : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (hKS : standardGrossCutoff α ≤ K) (hR : K ≤ R) (u : freeHamiltonian.domain) :
    ‖u.val‖+‖conjugationDressedHamiltonian α K R hα hK u‖ ≤
        (2+(3/8:ℝ)+dressedGraphConstant α K hα hK)*(‖u.val‖+‖freeHamiltonian u‖) ∧
    ‖u.val‖+‖freeHamiltonian u‖ ≤
      (1+(1+dressedGraphConstant α K hα hK)/(1-(3/8:ℝ)))*
        (‖u.val‖+‖conjugationDressedHamiltonian α K R hα hK u‖) :=
  (dressed_uniform_kato α K hα hK hKS (conjugationFiniteRemainder α K R hα hK)
    (dressedFiniteRemainder_bound α K R hα hK hR) (dressedFiniteRemainder_symmetric α K R hα hK)).2 u

/- Source argument component Endpoints01. -/
lemma dressedRelativeRemainderConstant_nonneg (α ε : ℝ) (hα : 0 ≤ α) (hε : 0 < ε) :
    0 ≤ dressedRelativeRemainderConstant α ε := by
  unfold dressedRelativeRemainderConstant
  exact add_nonneg hε.le (div_nonneg
    (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 28) unitBallVolume_pos.le) hα)
    (zero_le_one.trans (operatorCutoffWitness_ge_one α ε hα)))
lemma dressedRelativeCoefficient_zero (K : ℝ) (hK : 0 < K) :
    dressedRelativeCoefficient 0 K (by norm_num) hK = 0 := by
  have h := dressedRelativeCoefficient_numeric_bound 0 K (by norm_num) hK
  have hn := dressedRelativeCoefficient_nonneg 0 K (by norm_num) hK
  simp only [mul_zero,zero_div,Real.sqrt_zero,zero_mul,add_zero] at h
  exact le_antisymm h hn

/- Source argument component Public02. -/
lemma dressed_standard_cutoff_pos (α K : ℝ) (hα : 0 ≤ α) (hKS : standardGrossCutoff α ≤ K) : 0 < K :=
  zero_lt_one.trans_le ((operatorCutoffWitness_ge_one α (1/8) hα).trans hKS)

lemma main_dressed_small_relative (α : ℝ) (hα : 0 ≤ α) (ε : ℝ) (hε : 0 < ε) :
    let Kε := operatorCutoffWitness α ε
    let C := dressedRelativeRemainderConstant α ε
    0 < Kε ∧ 0 ≤ C ∧
    ∀ (K : ℝ) (hKε : Kε ≤ K),
      let hK : 0 < K := zero_lt_one.trans_le ((operatorCutoffWitness_ge_one α ε hα).trans hKε)
      (∀ (R : ℝ), K ≤ R → ∀ u : freeHamiltonian.domain,
        ‖conjugationFiniteRemainder α K R hα hK u‖ ≤ ε*‖freeHamiltonian u‖+C*‖u.val‖) ∧
      (∀ u : freeHamiltonian.domain,
        ‖dressedInfiniteRemainder α K hα hK u‖ ≤ ε*‖freeHamiltonian u‖+C*‖u.val‖) := by
  dsimp only
  refine ⟨zero_lt_one.trans_le (operatorCutoffWitness_ge_one α ε hα),
    dressedRelativeRemainderConstant_nonneg α ε hα hε,?_⟩
  intro K hKε
  constructor
  · intro R hR u
    exact dressed_relative_from_graph_bound α ε K hα hε hKε u _
      (dressedFiniteRemainder_bound α K R hα _ hR u)
  · intro u
    exact dressed_relative_from_graph_bound α ε K hα hε hKε u _
      (dressedInfiniteRemainder_bound α K hα _ u)

lemma main_dressed_small (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (hKS : standardGrossCutoff α ≤ K) :
    (∀ R : ℝ, K ≤ R →
      GW.IsSelfAdjointOperator (conjugationDressedHamiltonian α K R hα hK) ∧
      (conjugationDressedHamiltonian α K R hα hK).domain = freeHamiltonian.domain ∧
      ∀ u : freeHamiltonian.domain,
        ‖u.val‖+‖conjugationDressedHamiltonian α K R hα hK u‖ ≤
          (2+(3/8:ℝ)+dressedGraphConstant α K hα hK)*(‖u.val‖+‖freeHamiltonian u‖) ∧
        ‖u.val‖+‖freeHamiltonian u‖ ≤
          (1+(1+dressedGraphConstant α K hα hK)/(1-(3/8:ℝ)))*
            (‖u.val‖+‖conjugationDressedHamiltonian α K R hα hK u‖)) ∧
    GW.IsSelfAdjointOperator (dressedInfiniteHamiltonian α K hα hK) ∧
    (dressedInfiniteHamiltonian α K hα hK).domain = freeHamiltonian.domain ∧
    (∀ u : freeHamiltonian.domain,
      ‖u.val‖+‖dressedInfiniteHamiltonian α K hα hK u‖ ≤
        (2+(3/8:ℝ)+dressedGraphConstant α K hα hK)*(‖u.val‖+‖freeHamiltonian u‖) ∧
      ‖u.val‖+‖freeHamiltonian u‖ ≤
        (1+(1+dressedGraphConstant α K hα hK)/(1-(3/8:ℝ)))*
          (‖u.val‖+‖dressedInfiniteHamiltonian α K hα hK u‖)) := by
  refine ⟨?_,dressedInfiniteHamiltonian_selfadjoint α K hα hK hKS,rfl,?_⟩
  · intro R hR
    exact ⟨dressedFiniteHamiltonian_selfadjoint α K R hα hK hKS hR,rfl,
      dressedFiniteHamiltonian_graph_bounds α K R hα hK hKS hR⟩
  · exact dressedInfiniteHamiltonian_graph_bounds α K hα hK hKS

end GW.Gross
