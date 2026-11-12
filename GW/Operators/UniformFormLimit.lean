module
public import GW.Operators.FormRepresentation
public import GW.Operators.Polarization
@[expose] public section
noncomputable section
open Filter
open scoped Topology InnerProductSpace
namespace GW.Operators
section OperatorForms
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q]

/-- Forget only continuity; both sesquilinear slots and values are unchanged. -/
def boundedFormAlgebraic (b : GW.Analysis.BoundedForm Q) : AlgebraicForm Q where
  toFun u := (b u).toLinearMap
  map_add' u v := by
    ext w
    exact congrArg (fun L : Q →L[ℂ] ℂ => L w) (b.map_add u v)
  map_smul' c u := by
    ext v
    exact congrArg (fun L : Q →L[ℂ] ℂ => L v) (b.map_smulₛₗ c u)

lemma boundedFormAlgebraic_apply (b : GW.Analysis.BoundedForm Q) (u v : Q) :
    boundedFormAlgebraic b u v = b u v := rfl

def operatorAlgebraicForm (B : Q →L[ℂ] Q) : AlgebraicForm Q :=
  (innerₛₗ ℂ).compl₂ B.toLinearMap
lemma operatorAlgebraicForm_apply (B : Q →L[ℂ] Q) (u v : Q) :
    operatorAlgebraicForm B u v = ⟪u,B v⟫_ℂ := rfl

lemma operatorForm_mixed_bound (B : Q →L[ℂ] Q) (u v : Q) :
    ‖operatorAlgebraicForm B u v‖ ≤ ‖B‖*‖u‖*‖v‖ := by
  exact (norm_inner_le_norm u (B v)).trans
    (by nlinarith [mul_le_mul_of_nonneg_left (B.le_opNorm v) (norm_nonneg u)])

def operatorBoundedForm (B : Q →L[ℂ] Q) : GW.Analysis.BoundedForm Q :=
  boundedAlgebraicForm (operatorAlgebraicForm B) (norm_nonneg _) (operatorForm_mixed_bound B)
lemma operatorBoundedForm_apply (B : Q →L[ℂ] Q) (u v : Q) :
    operatorBoundedForm B u v = ⟪u,B v⟫_ℂ := rfl

lemma operatorBoundedForm_norm (B : Q →L[ℂ] Q) : ‖operatorBoundedForm B‖ = ‖B‖ := by
  apply le_antisymm
  · exact (GW.Analysis.form_norm_le_iff _ (norm_nonneg B)).mpr (operatorForm_mixed_bound B)
  · apply B.opNorm_le_bound (norm_nonneg (operatorBoundedForm B))
    intro v
    have h := GW.Analysis.form_bound (operatorBoundedForm B) (B v) v
    rw [operatorBoundedForm_apply,inner_self_eq_norm_sq_to_K] at h
    change ‖((‖B v‖ : ℂ)^2)‖ ≤ ‖operatorBoundedForm B‖*‖B v‖*‖v‖ at h
    rw [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_norm] at h
    by_cases hz : B v = 0
    · rw [hz,norm_zero]
      exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
    · have hn : 0 < ‖B v‖ := norm_pos_iff.mpr hz
      nlinarith

def operatorFormIsometry : (Q →L[ℂ] Q) →ₗᵢ[ℂ] GW.Analysis.BoundedForm Q where
  toLinearMap :=
    {toFun := operatorBoundedForm
     map_add' := by intro B C;ext u v;simp only [operatorBoundedForm_apply,add_apply,inner_add_right]
     map_smul' := by intro c B;ext u v;simp only [operatorBoundedForm_apply,smul_apply,inner_smul_right,RingHom.id_apply,smul_eq_mul]}
  norm_map' := operatorBoundedForm_norm
end OperatorForms

abbrev PositiveCutoff := {ℓ : ℝ // 0 < ℓ}

section UniformData
variable (Q H : Type*) [NormedAddCommGroup Q] [InnerProductSpace ℂ Q]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

structure UniformFormData where
  embedding : Q →L[ℂ] H
  embedding_injective : Function.Injective embedding
  embedding_dense : DenseRange embedding
  base : AlgebraicForm Q
  base_hermitian : ∀ u v, base u v = star (base v u)
  base_continuous : Continuous (fun p : Q × Q => base p.1 p.2)
  base_nonnegative : ∀ u, 0 ≤ (base u u).re
  energy_identity : ∀ u, ‖u‖^2 = (base u u).re + ‖embedding u‖^2
  perturbation : PositiveCutoff → AlgebraicForm Q
  perturbation_hermitian : ∀ ℓ u v, perturbation ℓ u v = star (perturbation ℓ v u)
  relative : ℝ
  relative_nonnegative : 0 ≤ relative
  relative_small : relative < 1
  remainder : ℝ
  remainder_nonnegative : 0 ≤ remainder
  diagonal_bound : ∀ ℓ u, ‖perturbation ℓ u u‖ ≤ relative*(base u u).re+remainder*‖embedding u‖^2
  error : ℝ → ℝ
  error_nonnegative : ∀ R, 0 < R → 0 ≤ error R
  error_tendsto : Tendsto error atTop (𝓝 0)
  difference_bound : ∀ R, 0 < R → ∀ ℓ μ : PositiveCutoff, R ≤ ℓ.val → R ≤ μ.val →
    ∀ u, ‖(perturbation ℓ-perturbation μ) u u‖ ≤ error R*‖u‖^2
end UniformData
section UniformLimit
variable {Q H : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (d : UniformFormData Q H)

omit [CompleteSpace Q] in
lemma uniform_base_le (u : Q) : (d.base u u).re ≤ ‖u‖^2 := by
  have h := d.energy_identity u
  nlinarith [sq_nonneg ‖d.embedding u‖]
omit [CompleteSpace Q] in
lemma uniform_embedding_sq_le (u : Q) : ‖d.embedding u‖^2 ≤ ‖u‖^2 := by
  have h := d.energy_identity u
  linarith [d.base_nonnegative u]

omit [CompleteSpace Q] in
lemma uniform_diagonal_bound (ℓ : PositiveCutoff) (u : Q) :
    ‖d.perturbation ℓ u u‖ ≤ (d.relative+d.remainder)*‖u‖^2 := by
  calc
    _ ≤ d.relative*(d.base u u).re+d.remainder*‖d.embedding u‖^2 := d.diagonal_bound ℓ u
    _ ≤ d.relative*‖u‖^2+d.remainder*‖u‖^2 :=
      add_le_add (mul_le_mul_of_nonneg_left (uniform_base_le d u) d.relative_nonnegative)
        (mul_le_mul_of_nonneg_left (uniform_embedding_sq_le d u) d.remainder_nonnegative)
    _ = _ := by ring

def uniformFormOperator (ℓ : PositiveCutoff) : Q →L[ℂ] Q :=
  (hermitian_form_representation (d.perturbation ℓ) (d.perturbation_hermitian ℓ)
    (add_nonneg d.relative_nonnegative d.remainder_nonnegative) (uniform_diagonal_bound d ℓ)).choose

lemma uniformFormOperator_spec (ℓ : PositiveCutoff) :
    (∀ u v, d.perturbation ℓ u v = ⟪u,uniformFormOperator d ℓ v⟫_ℂ) ∧
      (uniformFormOperator d ℓ).adjoint = uniformFormOperator d ℓ ∧
        ‖uniformFormOperator d ℓ‖ ≤ d.relative+d.remainder :=
  (hermitian_form_representation (d.perturbation ℓ) (d.perturbation_hermitian ℓ)
    (add_nonneg d.relative_nonnegative d.remainder_nonnegative) (uniform_diagonal_bound d ℓ)).choose_spec.1

lemma uniformFormOperator_pairing (ℓ : PositiveCutoff) (u v : Q) :
    d.perturbation ℓ u v = ⟪u,uniformFormOperator d ℓ v⟫_ℂ := (uniformFormOperator_spec d ℓ).1 u v

lemma uniformFormOperator_difference (R : ℝ) (hR : 0 < R) (ℓ k : PositiveCutoff)
    (hℓ : R ≤ ℓ.val) (hk : R ≤ k.val) :
    ‖uniformFormOperator d ℓ-uniformFormOperator d k‖ ≤ d.error R := by
  have hs : ∀ u v, (d.perturbation ℓ-d.perturbation k) u v =
      star ((d.perturbation ℓ-d.perturbation k) v u) := by
    intro u v
    change d.perturbation ℓ u v-d.perturbation k u v =
      star (d.perturbation ℓ v u-d.perturbation k v u)
    rw [star_sub,← d.perturbation_hermitian ℓ u v,← d.perturbation_hermitian k u v]
  obtain ⟨B,hB,_⟩ := hermitian_form_representation (d.perturbation ℓ-d.perturbation k) hs
    (d.error_nonnegative R hR) (d.difference_bound R hR ℓ k hℓ hk)
  have he : B = uniformFormOperator d ℓ-uniformFormOperator d k := by
    ext v
    apply ext_inner_left ℂ
    intro u
    rw [← hB.1 u v]
    change d.perturbation ℓ u v-d.perturbation k u v =
      ⟪u,uniformFormOperator d ℓ v-uniformFormOperator d k v⟫_ℂ
    rw [inner_sub_right,← uniformFormOperator_pairing,← uniformFormOperator_pairing]
  rw [← he]
  exact hB.2.2

def positiveNatCutoff (n : ℕ) : PositiveCutoff := ⟨(n : ℝ)+1,by positivity⟩

lemma positiveNatCutoff_tendsto : Tendsto positiveNatCutoff atTop atTop := by
  apply tendsto_atTop.2
  intro ℓ
  obtain ⟨N,hN⟩ := exists_nat_ge ℓ.val
  refine eventually_atTop.mpr ⟨N,fun n hn => ?_⟩
  change ℓ.val ≤ (n : ℝ)+1
  have hh : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

lemma uniformFormOperator_cauchy : CauchySeq (fun n => uniformFormOperator d (positiveNatCutoff n)) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨R₀,hR₀⟩ := eventually_atTop.mp ((tendsto_order.mp d.error_tendsto).2 ε hε)
  let R := max R₀ 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨N,hN⟩ := exists_nat_ge R
  refine ⟨N,fun n hn k hk => ?_⟩
  have hℓ : R ≤ (positiveNatCutoff n).val := by
    change R ≤ (n : ℝ)+1
    have hh : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hk' : R ≤ (positiveNatCutoff k).val := by
    change R ≤ (k : ℝ)+1
    have hh : (N : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  rw [dist_eq_norm]
  exact (uniformFormOperator_difference d R hR _ _ hℓ hk').trans_lt (hR₀ R (le_max_left _ _))

def uniformFormLimitOperator : Q →L[ℂ] Q :=
  (cauchySeq_tendsto_of_complete (uniformFormOperator_cauchy d)).choose

lemma uniformFormLimitOperator_tendsto :
    Tendsto (fun n => uniformFormOperator d (positiveNatCutoff n)) atTop (𝓝 (uniformFormLimitOperator d)) :=
  (cauchySeq_tendsto_of_complete (uniformFormOperator_cauchy d)).choose_spec

lemma uniformFormLimitOperator_error (R : ℝ) (hR : 0 < R) (ℓ : PositiveCutoff) (hℓ : R ≤ ℓ.val) :
    ‖uniformFormOperator d ℓ-uniformFormLimitOperator d‖ ≤ d.error R := by
  have hc : Continuous (fun B : Q →L[ℂ] Q => ‖uniformFormOperator d ℓ-B‖) :=
    (continuous_const.sub continuous_id).norm
  have ht := (hc.tendsto (uniformFormLimitOperator d)).comp (uniformFormLimitOperator_tendsto d)
  apply le_of_tendsto ht
  obtain ⟨N,hN⟩ := exists_nat_ge R
  refine (eventually_atTop.mpr ⟨N,fun n hn => ?_⟩)
  apply uniformFormOperator_difference d R hR ℓ (positiveNatCutoff n) hℓ
  change R ≤ (n : ℝ)+1
  have hh : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

lemma uniformFormOperator_tendsto :
    Tendsto (uniformFormOperator d) atTop (𝓝 (uniformFormLimitOperator d)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨R₀,hR₀⟩ := eventually_atTop.mp ((tendsto_order.mp d.error_tendsto).2 ε hε)
  let R := max R₀ 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨(⟨R,hR⟩ : PositiveCutoff),fun ℓ hℓ => ?_⟩
  rw [dist_eq_norm]
  exact (uniformFormLimitOperator_error d R hR ℓ hℓ).trans_lt (hR₀ R (le_max_left _ _))

lemma uniformFormLimit_pairing_tendsto (u v : Q) :
    Tendsto (fun n => ⟪u,uniformFormOperator d (positiveNatCutoff n) v⟫_ℂ) atTop
      (𝓝 ⟪u,uniformFormLimitOperator d v⟫_ℂ) :=
  tendsto_const_nhds.inner (((ContinuousLinearMap.apply ℂ Q v).continuous.tendsto _).comp
    (uniformFormLimitOperator_tendsto d))

lemma uniformFormLimit_hermitian (u v : Q) :
    ⟪u,uniformFormLimitOperator d v⟫_ℂ = star ⟪v,uniformFormLimitOperator d u⟫_ℂ := by
  apply tendsto_nhds_unique (uniformFormLimit_pairing_tendsto d u v)
  apply (uniformFormLimit_pairing_tendsto d v u).star.congr'
  exact Eventually.of_forall (fun n => by
    change star ⟪v,uniformFormOperator d (positiveNatCutoff n) u⟫_ℂ =
      ⟪u,uniformFormOperator d (positiveNatCutoff n) v⟫_ℂ
    rw [← uniformFormOperator_pairing,← uniformFormOperator_pairing]
    exact (d.perturbation_hermitian (positiveNatCutoff n) u v).symm)

lemma uniformFormLimit_diagonal (u : Q) :
    ‖⟪u,uniformFormLimitOperator d u⟫_ℂ‖ ≤ d.relative*(d.base u u).re+d.remainder*‖d.embedding u‖^2 := by
  apply le_of_tendsto (uniformFormLimit_pairing_tendsto d u u).norm
  exact Eventually.of_forall (fun n => by
    rw [← uniformFormOperator_pairing]
    exact d.diagonal_bound (positiveNatCutoff n) u)

def uniformBoundedForm (ℓ : PositiveCutoff) : GW.Analysis.BoundedForm Q := operatorBoundedForm (uniformFormOperator d ℓ)
def uniformLimitForm : GW.Analysis.BoundedForm Q := operatorBoundedForm (uniformFormLimitOperator d)

lemma uniformBoundedForm_source (ℓ : PositiveCutoff) (u v : Q) :
    uniformBoundedForm d ℓ u v = d.perturbation ℓ u v := (uniformFormOperator_pairing d ℓ u v).symm

lemma uniformLimitForm_hermitian (u v : Q) : uniformLimitForm d u v = star (uniformLimitForm d v u) :=
  uniformFormLimit_hermitian d u v

lemma uniformLimitForm_diagonal (u : Q) :
    ‖uniformLimitForm d u u‖ ≤ d.relative*(d.base u u).re+d.remainder*‖d.embedding u‖^2 :=
  uniformFormLimit_diagonal d u

lemma uniformLimitForm_error (R : ℝ) (hR : 0 < R) (ℓ : PositiveCutoff) (hℓ : R ≤ ℓ.val) :
    ‖uniformBoundedForm d ℓ-uniformLimitForm d‖ ≤ d.error R := by
  change ‖operatorFormIsometry (uniformFormOperator d ℓ)-operatorFormIsometry (uniformFormLimitOperator d)‖ ≤ _
  have he := (operatorFormIsometry (Q := Q)).map_sub (uniformFormOperator d ℓ) (uniformFormLimitOperator d)
  calc
    _ = ‖uniformFormOperator d ℓ-uniformFormLimitOperator d‖ :=
      (congrArg norm he.symm).trans ((operatorFormIsometry (Q := Q)).norm_map _)
    _ ≤ _ := uniformFormLimitOperator_error d R hR ℓ hℓ

lemma uniformLimitForm_tendsto : Tendsto (uniformBoundedForm d) atTop (𝓝 (uniformLimitForm d)) :=
  (operatorFormIsometry.continuous.tendsto (uniformFormLimitOperator d)).comp (uniformFormOperator_tendsto d)

lemma uniformLimitForm_unique (b : GW.Analysis.BoundedForm Q)
    (hb : Tendsto (uniformBoundedForm d) atTop (𝓝 b)) : b = uniformLimitForm d :=
  tendsto_nhds_unique hb (uniformLimitForm_tendsto d)

lemma uniform_form_limit_exists_unique : ∃! b : GW.Analysis.BoundedForm Q,
    (∀ u v, b u v = star (b v u)) ∧
    (∀ u, ‖b u u‖ ≤ d.relative*(d.base u u).re+d.remainder*‖d.embedding u‖^2) ∧
    Tendsto (uniformBoundedForm d) atTop (𝓝 b) ∧
    ∀ R, 0 < R → ∀ ℓ : PositiveCutoff, R ≤ ℓ.val → ‖uniformBoundedForm d ℓ-b‖ ≤ d.error R := by
  refine ⟨uniformLimitForm d,⟨uniformLimitForm_hermitian d,uniformLimitForm_diagonal d,
    uniformLimitForm_tendsto d,uniformLimitForm_error d⟩,?_⟩
  intro b hb
  exact uniformLimitForm_unique d b hb.2.2.1

def uniformIndexOperator (i : Option PositiveCutoff) : Q →L[ℂ] Q :=
  i.elim (uniformFormLimitOperator d) (uniformFormOperator d)
def uniformIndexPerturbation (i : Option PositiveCutoff) : AlgebraicForm Q :=
  operatorAlgebraicForm (uniformIndexOperator d i)
def uniformTotalForm (i : Option PositiveCutoff) : AlgebraicForm Q := d.base+uniformIndexPerturbation d i

lemma uniformIndexPerturbation_some (ℓ : PositiveCutoff) :
    uniformIndexPerturbation d (some ℓ) = d.perturbation ℓ := by
  ext u v
  exact (uniformFormOperator_pairing d ℓ u v).symm

lemma uniformIndexPerturbation_none (u v : Q) :
    uniformIndexPerturbation d none u v = uniformLimitForm d u v := rfl

lemma uniformIndexPerturbation_hermitian (i : Option PositiveCutoff) (u v : Q) :
    uniformIndexPerturbation d i u v = star (uniformIndexPerturbation d i v u) := by
  cases i with
  | none => exact uniformFormLimit_hermitian d u v
  | some ℓ => rw [uniformIndexPerturbation_some];exact d.perturbation_hermitian ℓ u v

lemma uniformIndexPerturbation_continuous (i : Option PositiveCutoff) :
    Continuous (fun p : Q × Q => uniformIndexPerturbation d i p.1 p.2) :=
  continuous_fst.inner ((uniformIndexOperator d i).continuous.comp continuous_snd)

lemma uniformIndexPerturbation_bound (i : Option PositiveCutoff) (u : Q) :
    ‖uniformIndexPerturbation d i u u‖ ≤ d.relative*(d.base u u).re+d.remainder*‖d.embedding u‖^2 := by
  cases i with
  | none => exact uniformFormLimit_diagonal d u
  | some ℓ => rw [uniformIndexPerturbation_some];exact d.diagonal_bound ℓ u

lemma uniformTotalForm_hermitian (i : Option PositiveCutoff) (u v : Q) :
    uniformTotalForm d i u v = star (uniformTotalForm d i v u) := by
  change d.base u v+uniformIndexPerturbation d i u v = star (d.base v u+uniformIndexPerturbation d i v u)
  rw [star_add,← d.base_hermitian u v,← uniformIndexPerturbation_hermitian d i u v]

lemma uniform_shift_bounds (i : Option PositiveCutoff) (u : Q) :
    (1-d.relative)*‖u‖^2 ≤ (uniformTotalForm d i u u).re+(d.remainder+1)*‖d.embedding u‖^2 ∧
    (uniformTotalForm d i u u).re+(d.remainder+1)*‖d.embedding u‖^2 ≤ (2+d.relative+2*d.remainder)*‖u‖^2 := by
  have hw := (Complex.abs_re_le_norm (uniformIndexPerturbation d i u u)).trans
    (uniformIndexPerturbation_bound d i u)
  have hlo := neg_le_of_abs_le hw
  have hup := le_of_abs_le hw
  have hs : (uniformTotalForm d i u u).re = (d.base u u).re+(uniformIndexPerturbation d i u u).re := rfl
  rw [hs]
  constructor
  · have he := congrArg (fun t : ℝ => (1-d.relative)*t) (d.energy_identity u)
    have hp := mul_nonneg d.relative_nonnegative (sq_nonneg ‖d.embedding u‖)
    nlinarith
  · have he := congrArg (fun t : ℝ => (2+d.relative+2*d.remainder)*t) (d.energy_identity u)
    have hp := mul_nonneg (show 0 ≤ 1+2*d.remainder by linarith [d.remainder_nonnegative]) (d.base_nonnegative u)
    have hq := mul_nonneg (show 0 ≤ 1+d.relative by linarith [d.relative_nonnegative]) (sq_nonneg ‖d.embedding u‖)
    nlinarith

def uniformClosedData (i : Option PositiveCutoff) : CoerciveFormData Q H where
  embedding := d.embedding
  embedding_injective := d.embedding_injective
  embedding_dense := d.embedding_dense
  form := uniformTotalForm d i
  hermitian := uniformTotalForm_hermitian d i
  continuous_form := d.base_continuous.add (uniformIndexPerturbation_continuous d i)
  shift := d.remainder+1
  lower := 1-d.relative
  upper := 2+d.relative+2*d.remainder
  lower_pos := sub_pos.mpr d.relative_small
  lower_le_upper := by linarith [d.relative_nonnegative,d.remainder_nonnegative]
  lower_bound := fun u => (uniform_shift_bounds d i u).1
  upper_bound := fun u => (uniform_shift_bounds d i u).2

variable [CompleteSpace H]

lemma uniform_closed_representation (i : Option PositiveCutoff) : ∃! L : H →ₗ.[ℂ] H,
    IsSelfAdjointOperator L ∧ ∀ x : L.domain, ∃ u : Q, d.embedding u = (x : H) ∧
      ∀ v, uniformTotalForm d i v u = ⟪d.embedding v,L x⟫_ℂ :=
  coercive_form_representation (uniformClosedData d i)

lemma uniform_embedded_form_space (i : Option PositiveCutoff) :
    Set.range (completedEnergyEmbedding (uniformClosedData d i)) = Set.range d.embedding :=
  completedEnergyEmbedding_range _

lemma uniform_representing_bounded_below (i : Option PositiveCutoff)
    (x : (formOperator (uniformClosedData d i)).domain) :
    -(d.remainder+1)*‖(x : H)‖^2 ≤ (⟪(x : H),formOperator (uniformClosedData d i) x⟫_ℂ).re :=
  formOperator_bounded_below _ x

omit [CompleteSpace H] in
lemma uniformBoundedForm_algebraic (ℓ : PositiveCutoff) :
    boundedFormAlgebraic (uniformBoundedForm d ℓ) = d.perturbation ℓ := by
  ext u v
  exact uniformBoundedForm_source d ℓ u v

omit [CompleteSpace H] in
lemma uniformTotalForm_some (ℓ : PositiveCutoff) :
    uniformTotalForm d (some ℓ) = d.base+d.perturbation ℓ := by
  rw [uniformTotalForm,uniformIndexPerturbation_some]

omit [CompleteSpace H] in
lemma uniformTotalForm_none : uniformTotalForm d none = d.base+boundedFormAlgebraic (uniformLimitForm d) := by
  ext u v
  rfl

omit [CompleteSpace H] in
lemma uniform_closed_complete (i : Option PositiveCutoff) :
    CompleteSpace (EnergySpace (uniformClosedData d i)) := inferInstance

end UniformLimit
end GW.Operators
