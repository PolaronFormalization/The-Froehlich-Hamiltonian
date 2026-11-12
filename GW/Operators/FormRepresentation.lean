module
public import GW.Operators.Polarization
public import GW.Operators.CoerciveBounded
public import GW.Operators.SelfadjointCriterion
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.SpecificLimits.Basic
@[expose] public section
noncomputable section
open scoped Topology InnerProductSpace
namespace GW.Operators
section Completion
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

def completionTransport (i : E →ₗᵢ[ℂ] F) : UniformSpace.Completion E →L[ℂ] F :=
  i.toContinuousLinearMap.fromCompletion

lemma completionTransport_coe (i : E →ₗᵢ[ℂ] F) (u : E) : completionTransport i u = i u :=
  ContinuousLinearMap.fromCompletion_apply_coe _ u

lemma completionTransport_norm (i : E →ₗᵢ[ℂ] F) (u : UniformSpace.Completion E) :
    ‖completionTransport i u‖ = ‖u‖ := by
  refine UniformSpace.Completion.induction_on (p := fun x => ‖completionTransport i x‖ = ‖x‖) u ?_ ?_
  · exact isClosed_eq ((completionTransport i).continuous.norm) continuous_norm
  · intro x
    rw [completionTransport_coe,UniformSpace.Completion.norm_coe,i.norm_map]

def completionTransportIsometry (i : E →ₗᵢ[ℂ] F) : UniformSpace.Completion E →ₗᵢ[ℂ] F where
  toLinearMap := (completionTransport i).toLinearMap
  norm_map' := completionTransport_norm i

lemma completionTransport_surjective (i : E →ₗᵢ[ℂ] F) (hi : DenseRange i) :
    Function.Surjective (completionTransportIsometry i) := by
  have hc : IsClosed (Set.range (completionTransportIsometry i)) :=
    (completionTransportIsometry i).isometry.isClosedEmbedding.isClosed_range
  intro y
  apply closure_minimal (s := Set.range i) (t := Set.range (completionTransportIsometry i)) ?_ hc (hi y)
  rintro _ ⟨x,rfl⟩
  exact ⟨(x : UniformSpace.Completion E),completionTransport_coe i x⟩

/-- Source completion identification: the norm identity and surjectivity are proved first. -/
def completionTransportEquiv (i : E →ₗᵢ[ℂ] F) (hi : DenseRange i) : UniformSpace.Completion E ≃ₗᵢ[ℂ] F :=
  LinearIsometryEquiv.ofSurjective (completionTransportIsometry i) (completionTransport_surjective i hi)

lemma completionTransportEquiv_coe (i : E →ₗᵢ[ℂ] F) (hi : DenseRange i) (x : E) :
    completionTransportEquiv i hi x = i x := completionTransport_coe i x
end Completion

variable {Q H : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Pull back the ambient inner product along the actual embedding. -/
def embeddingForm (J : Q →L[ℂ] H) : AlgebraicForm Q :=
  ((innerₛₗ ℂ).comp J.toLinearMap).compl₂ J.toLinearMap

lemma embeddingForm_apply (J : Q →L[ℂ] H) (u v : Q) :
    embeddingForm J u v = ⟪J u,J v⟫_ℂ := rfl

def shiftedForm (q : AlgebraicForm Q) (J : Q →L[ℂ] H) (c : ℝ) : AlgebraicForm Q :=
  q+(c : ℂ) • embeddingForm J

lemma shiftedForm_apply (q : AlgebraicForm Q) (J : Q →L[ℂ] H) (c : ℝ) (u v : Q) :
    shiftedForm q J c u v = q u v+(c : ℂ)*⟪J u,J v⟫_ℂ := by
  simp only [shiftedForm,LinearMap.add_apply,LinearMap.smul_apply,embeddingForm_apply,smul_eq_mul]

lemma shiftedForm_hermitian (q : AlgebraicForm Q) (J : Q →L[ℂ] H) (c : ℝ)
    (hs : ∀ u v, q u v = star (q v u)) :
    ∀ u v, shiftedForm q J c u v = star (shiftedForm q J c v u) := by
  intro u v
  simp only [shiftedForm_apply,star_add,star_mul,Complex.star_def,Complex.conj_ofReal,
    inner_conj_symm,← hs u v,mul_comm]

/-- Exact input data of the manuscript's coercive representation theorem. -/
structure CoerciveFormData (Q H : Type*) [NormedAddCommGroup Q] [InnerProductSpace ℂ Q]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  embedding : Q →L[ℂ] H
  embedding_injective : Function.Injective embedding
  embedding_dense : DenseRange embedding
  form : AlgebraicForm Q
  hermitian : ∀ u v, form u v = star (form v u)
  continuous_form : Continuous (fun p : Q × Q => form p.1 p.2)
  shift : ℝ
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  lower_le_upper : lower ≤ upper
  lower_bound : ∀ u, lower * ‖u‖ ^ 2 ≤ (form u u).re+shift*‖embedding u‖ ^ 2
  upper_bound : ∀ u, (form u u).re+shift*‖embedding u‖ ^ 2 ≤ upper * ‖u‖ ^ 2

variable (d : CoerciveFormData Q H)

def energyForm : AlgebraicForm Q := shiftedForm d.form d.embedding d.shift

lemma energyForm_apply (u v : Q) : energyForm d u v = d.form u v+(d.shift : ℂ)*⟪d.embedding u,d.embedding v⟫_ℂ :=
  shiftedForm_apply _ _ _ _ _

lemma energyForm_hermitian : ∀ u v, energyForm d u v = star (energyForm d v u) :=
  shiftedForm_hermitian d.form d.embedding d.shift d.hermitian

lemma energyForm_diagonal_re (u : Q) : (energyForm d u u).re =
    (d.form u u).re+d.shift*‖d.embedding u‖ ^ 2 := by
  have hi : (⟪d.embedding u,d.embedding u⟫_ℂ).re = ‖d.embedding u‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) (d.embedding u)).symm
  simp only [energyForm_apply,Complex.add_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero,hi]

lemma energyForm_lower (u : Q) : d.lower*‖u‖ ^ 2 ≤ (energyForm d u u).re := by
  rw [energyForm_diagonal_re]
  exact d.lower_bound u

lemma energyForm_upper (u : Q) : (energyForm d u u).re ≤ d.upper*‖u‖ ^ 2 := by
  rw [energyForm_diagonal_re]
  exact d.upper_bound u

lemma energyForm_diagonal_im (u : Q) : (energyForm d u u).im = 0 := by
  have he := congrArg Complex.im (energyForm_hermitian d u u)
  change (energyForm d u u).im = -(energyForm d u u).im at he
  linarith

lemma energyForm_diagonal_bound (u : Q) : ‖energyForm d u u‖ ≤ d.upper*‖u‖ ^ 2 := by
  have he : energyForm d u u = ((energyForm d u u).re : ℂ) := by
    apply Complex.ext
    · rfl
    · exact energyForm_diagonal_im d u
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg
    ((mul_nonneg d.lower_pos.le (sq_nonneg _)).trans (energyForm_lower d u))]
  exact energyForm_upper d u

variable [CompleteSpace Q]

lemma formRiesz_exists : ∃! A : Q →L[ℂ] Q,
    (∀ u v, energyForm d u v = ⟪u,A v⟫_ℂ) ∧ A.adjoint = A ∧ ‖A‖ ≤ d.upper :=
  hermitian_form_representation (energyForm d) (energyForm_hermitian d)
    (d.lower_pos.le.trans d.lower_le_upper) (energyForm_diagonal_bound d)

def formRiesz : Q →L[ℂ] Q := Classical.choose (formRiesz_exists d)

lemma formRiesz_spec : (∀ u v, energyForm d u v = ⟪u,formRiesz d v⟫_ℂ) ∧
    (formRiesz d).adjoint = formRiesz d ∧ ‖formRiesz d‖ ≤ d.upper :=
  (Classical.choose_spec (formRiesz_exists d)).1

lemma formRiesz_lower (u : Q) : d.lower*‖u‖ ^ 2 ≤ (⟪u,formRiesz d u⟫_ℂ).re := by
  rw [← (formRiesz_spec d).1]
  exact energyForm_lower d u

def formInverse : Q →L[ℂ] Q :=
  coerciveInverse (formRiesz d) (formRiesz_spec d).2.1 d.lower_pos (formRiesz_lower d)

lemma formInverse_left (u : Q) : formInverse d (formRiesz d u) = u :=
  coerciveInverse_left _ _ _ _ u

lemma formInverse_right (u : Q) : formRiesz d (formInverse d u) = u :=
  coerciveInverse_right _ _ _ _ u

lemma formInverse_norm : ‖formInverse d‖ ≤ d.lower⁻¹ := coerciveInverse_norm_le _ _ _ _

lemma formInverse_injective : Function.Injective (formInverse d) := by
  intro u v h
  have he := congrArg (formRiesz d) h
  simpa only [formInverse_right] using he

lemma formInverse_selfadjoint : (formInverse d).adjoint = formInverse d := by
  have he : (formInverse d).comp (formRiesz d) = ContinuousLinearMap.id ℂ Q := by
    apply ContinuousLinearMap.ext
    exact formInverse_left d
  have hd := congrArg (fun B : Q →L[ℂ] Q => B.adjoint) he
  rw [ContinuousLinearMap.adjoint_comp,(formRiesz_spec d).2.1,ContinuousLinearMap.adjoint_id] at hd
  apply ContinuousLinearMap.ext
  intro u
  apply (coercive_bijective (formRiesz d) (formRiesz_spec d).2.1 d.lower_pos (formRiesz_lower d)).1
  have hval := congrArg (fun B : Q →L[ℂ] Q => B u) hd
  exact hval.trans (formInverse_right d u).symm

variable [CompleteSpace H]

def formSolution : H →L[ℂ] Q := (formInverse d).comp d.embedding.adjoint

lemma formSolution_riesz (f : H) : formRiesz d (formSolution d f) = d.embedding.adjoint f :=
  formInverse_right d _

lemma formSolution_equation (f : H) (v : Q) :
    energyForm d v (formSolution d f) = ⟪d.embedding v,f⟫_ℂ := by
  rw [(formRiesz_spec d).1,formSolution_riesz]
  exact d.embedding.adjoint_inner_right v f

lemma formSolution_unique (u : Q) (f : H) :
    (∀ v, energyForm d v u = ⟪d.embedding v,f⟫_ℂ) ↔ u = formSolution d f := by
  constructor
  · intro he
    have ha : formRiesz d u = d.embedding.adjoint f := by
      apply ext_inner_left ℂ
      intro v
      rw [← (formRiesz_spec d).1,he,d.embedding.adjoint_inner_right]
    calc
      u = formInverse d (formRiesz d u) := (formInverse_left d u).symm
      _ = formInverse d (d.embedding.adjoint f) := congrArg (formInverse d) ha
      _ = formSolution d f := rfl
  · rintro rfl
    exact formSolution_equation d f

/-- The exact bounded positive operator R=J A⁻¹ J*. -/
def formResolvent : H →L[ℂ] H := d.embedding.comp (formSolution d)

lemma formResolvent_apply (f : H) : formResolvent d f = d.embedding (formSolution d f) := rfl

lemma formResolvent_selfadjoint : (formResolvent d).adjoint = formResolvent d := by
  simp only [formResolvent,formSolution,ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint,formInverse_selfadjoint,ContinuousLinearMap.comp_assoc]

lemma formResolvent_pairing (f g : H) :
    ⟪f,formResolvent d g⟫_ℂ = energyForm d (formSolution d f) (formSolution d g) := by
  have hsym := (ContinuousLinearMap.eq_adjoint_iff (formRiesz d) (formRiesz d)).mp
    (formRiesz_spec d).2.1.symm
  calc
    _ = ⟪d.embedding.adjoint f,formSolution d g⟫_ℂ :=
      (d.embedding.adjoint_inner_left (formSolution d g) f).symm
    _ = ⟪formRiesz d (formSolution d f),formSolution d g⟫_ℂ := by rw [formSolution_riesz]
    _ = ⟪formSolution d f,formRiesz d (formSolution d g)⟫_ℂ := hsym _ _
    _ = _ := ((formRiesz_spec d).1 _ _).symm

lemma formResolvent_positive (f : H) : 0 ≤ (⟪f,formResolvent d f⟫_ℂ).re := by
  rw [formResolvent_pairing]
  exact (mul_nonneg d.lower_pos.le (sq_nonneg _)).trans (energyForm_lower d _)

lemma dense_embedding_adjoint_injective (J : Q →L[ℂ] H) (hd : DenseRange J) :
    Function.Injective J.adjoint := by
  have hr : J.range.topologicalClosure = ⊤ :=
    Submodule.dense_iff_topologicalClosure_eq_top.mp hd
  have ho : J.rangeᗮ = ⊥ := J.range.topologicalClosure_eq_top_iff.mp hr
  rw [J.orthogonal_range] at ho
  exact LinearMap.ker_eq_bot.mp ho

lemma formResolvent_injective : Function.Injective (formResolvent d) := by
  intro f g h
  apply dense_embedding_adjoint_injective d.embedding d.embedding_dense
  apply formInverse_injective d
  apply d.embedding_injective
  exact h

lemma formResolvent_norm : ‖formResolvent d‖ ≤ ‖d.embedding‖ ^ 2 / d.lower := by
  calc
    _ ≤ ‖d.embedding‖ * ‖formSolution d‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖d.embedding‖ * (‖formInverse d‖ * ‖d.embedding.adjoint‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ ≤ ‖d.embedding‖ * (d.lower⁻¹ * ‖d.embedding‖) := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (formInverse_norm d) (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

/-- The unbounded operator is defined only on the actual range of R. -/
def formOperator : H →ₗ.[ℂ] H :=
  realShift (inverseOperator (formResolvent d) (formResolvent_injective d)) d.shift

lemma formOperator_domain : (formOperator d).domain = (formResolvent d).range := rfl

lemma formOperator_selfadjoint : IsSelfAdjointOperator (formOperator d) :=
  realShift_selfadjoint _
    (inverseOperator_selfadjoint _ (formResolvent_injective d) (formResolvent_selfadjoint d)) _

lemma formOperator_closed : (formOperator d).IsClosed :=
  selfadjoint_closed _ (formOperator_selfadjoint d)

lemma formOperator_apply (u : (formOperator d).domain) : formOperator d u =
    inverseOperator (formResolvent d) (formResolvent_injective d) u - (d.shift : ℂ) • (u : H) := rfl

/-- The uniquely determined original form coordinate of an operator-domain vector. -/
def operatorFormCoordinate : (formOperator d).domain →ₗ[ℂ] Q :=
  (formSolution d).toLinearMap.comp (inverseOperator (formResolvent d) (formResolvent_injective d)).toFun

lemma operatorFormCoordinate_embedding (u : (formOperator d).domain) :
    d.embedding (operatorFormCoordinate d u) = (u : H) :=
  inverseOperator_right _ _ u

lemma operatorFormCoordinate_injective : Function.Injective (operatorFormCoordinate d) := by
  intro u v he
  apply Subtype.ext
  simpa only [operatorFormCoordinate_embedding] using congrArg d.embedding he

lemma formOperator_form_identity (u : (formOperator d).domain) (v : Q) :
    d.form v (operatorFormCoordinate d u) = ⟪d.embedding v,formOperator d u⟫_ℂ := by
  have he := formSolution_equation d
    (inverseOperator (formResolvent d) (formResolvent_injective d) u) v
  change energyForm d v (operatorFormCoordinate d u) = _ at he
  rw [energyForm_apply,operatorFormCoordinate_embedding] at he
  rw [formOperator_apply,inner_sub_right,inner_smul_right]
  linear_combination he

lemma formOperator_domain_of_equation (u : Q) (f : H)
    (hq : ∀ v, d.form v u = ⟪d.embedding v,f⟫_ℂ) :
    ∃ hmem : d.embedding u ∈ (formOperator d).domain,
      formOperator d ⟨d.embedding u,hmem⟩ = f := by
  have he : u = formSolution d (f+(d.shift : ℂ) • d.embedding u) := by
    apply (formSolution_unique d u _).mp
    intro v
    rw [energyForm_apply,hq v,inner_add_right,inner_smul_right]
  have hr : formResolvent d (f+(d.shift : ℂ) • d.embedding u) = d.embedding u := by
    rw [formResolvent_apply,← he]
  have hmem : d.embedding u ∈ (formOperator d).domain :=
    ⟨f+(d.shift : ℂ) • d.embedding u,hr⟩
  refine ⟨hmem,?_⟩
  change inverseOperator (formResolvent d) (formResolvent_injective d)
    ⟨d.embedding u,⟨f+(d.shift : ℂ) • d.embedding u,hr⟩⟩ -
      (d.shift : ℂ) • d.embedding u = f
  rw [inverseOperator_apply_eq _ _ _ _ hr,add_sub_cancel_right]

lemma formOperator_domain_iff (x : H) : x ∈ (formOperator d).domain ↔
    ∃ u : Q, d.embedding u = x ∧ ∃ f : H, ∀ v, d.form v u = ⟪d.embedding v,f⟫_ℂ := by
  constructor
  · intro hx
    let u : (formOperator d).domain := ⟨x,hx⟩
    exact ⟨operatorFormCoordinate d u,operatorFormCoordinate_embedding d u,
      formOperator d u,formOperator_form_identity d u⟩
  · rintro ⟨u,hu,f,hf⟩
    obtain ⟨hmem,_⟩ := formOperator_domain_of_equation d u f hf
    exact hu ▸ hmem

lemma formOperator_bounded_below (u : (formOperator d).domain) :
    -d.shift * ‖(u : H)‖ ^ 2 ≤ (⟪(u : H),formOperator d u⟫_ℂ).re := by
  have he := formOperator_form_identity d u (operatorFormCoordinate d u)
  rw [operatorFormCoordinate_embedding] at he
  have hp := energyForm_lower d (operatorFormCoordinate d u)
  rw [energyForm_diagonal_re,operatorFormCoordinate_embedding] at hp
  rw [← he]
  nlinarith [mul_nonneg d.lower_pos.le (sq_nonneg ‖operatorFormCoordinate d u‖)]

lemma formOperator_unique (L : H →ₗ.[ℂ] H) (hL : IsSelfAdjointOperator L)
    (hform : ∀ x : L.domain, ∃ u : Q, d.embedding u = (x : H) ∧
      ∀ v, d.form v u = ⟪d.embedding v,L x⟫_ℂ) : L = formOperator d := by
  apply selfadjoint_eq_of_inclusion hL (formOperator_selfadjoint d)
  apply LinearPMap.le_of_le_graph
  intro p hp
  obtain ⟨x,hx⟩ := L.mem_graph_iff'.mp hp
  obtain ⟨u,hu,hq⟩ := hform x
  obtain ⟨hmem,hvalue⟩ := formOperator_domain_of_equation d u (L x) hq
  rw [← hx]
  exact (formOperator d).mem_graph_iff.mpr ⟨⟨d.embedding u,hmem⟩,hu,hvalue⟩

lemma formOperator_inverse_left (f : H) :
    formOperator d ⟨formResolvent d f,LinearMap.mem_range_self _ f⟩ +
      (d.shift : ℂ) • formResolvent d f = f :=
  inverseOperator_shift_left _ _ _ f

lemma formOperator_inverse_right (u : (formOperator d).domain) :
    formResolvent d (formOperator d u+(d.shift : ℂ) • (u : H)) = (u : H) :=
  inverseOperator_shift_right _ _ _ u

/-- The energy carrier has the form inner product, not the original or subtype norm. -/
def EnergySpace (_d : CoerciveFormData Q H) : Type _ := Q

instance energyAddCommGroup : AddCommGroup (EnergySpace d) := inferInstanceAs (AddCommGroup Q)
instance energyModule : Module ℂ (EnergySpace d) := inferInstanceAs (Module ℂ Q)

def energyCoordinates : EnergySpace d ≃ₗ[ℂ] Q := LinearEquiv.refl ℂ Q

@[instance_reducible]
def energyCore : InnerProductSpace.Core ℂ (EnergySpace d) where
  inner u v := energyForm d (energyCoordinates d u) (energyCoordinates d v)
  conj_inner_symm u v := (energyForm_hermitian d _ _).symm
  re_inner_nonneg u := (mul_nonneg d.lower_pos.le (sq_nonneg _)).trans (energyForm_lower d _)
  add_left u v w := by simp only [map_add,LinearMap.add_apply]
  smul_left u v r := by simp only [map_smulₛₗ,LinearMap.smul_apply,RingHom.id_apply,smul_eq_mul]
  definite u hu := by
    have hl := energyForm_lower d (energyCoordinates d u)
    change energyForm d (energyCoordinates d u) (energyCoordinates d u) = 0 at hu
    rw [hu,Complex.zero_re] at hl
    have hn : ‖energyCoordinates d u‖ = 0 := by
      have hs : ‖energyCoordinates d u‖ ^ 2 = 0 :=
        (mul_eq_zero.mp (le_antisymm hl (mul_nonneg d.lower_pos.le (sq_nonneg _)))).resolve_left d.lower_pos.ne'
      exact (sq_eq_zero_iff).mp hs
    apply (energyCoordinates d).injective
    simpa only [map_zero] using norm_eq_zero.mp hn

instance energyNormedAddCommGroup : NormedAddCommGroup (EnergySpace d) := by
  letI : InnerProductSpace.Core ℂ (EnergySpace d) := energyCore d
  exact InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

instance energyInnerProductSpace : InnerProductSpace ℂ (EnergySpace d) := by
  letI : InnerProductSpace.Core ℂ (EnergySpace d) := energyCore d
  exact InnerProductSpace.ofCore (energyCore d).toCore

omit [CompleteSpace Q] [CompleteSpace H] in
lemma energy_inner (u v : EnergySpace d) : ⟪u,v⟫_ℂ =
    energyForm d (energyCoordinates d u) (energyCoordinates d v) := rfl

omit [CompleteSpace Q] [CompleteSpace H] in
lemma energy_norm_sq (u : EnergySpace d) : ‖u‖ ^ 2 =
    (energyForm d (energyCoordinates d u) (energyCoordinates d u)).re :=
  norm_sq_eq_re_inner (𝕜 := ℂ) u

omit [CompleteSpace Q] [CompleteSpace H] in
lemma energy_norm_sq_bounds (u : EnergySpace d) :
    d.lower*‖energyCoordinates d u‖ ^ 2 ≤ ‖u‖ ^ 2 ∧
      ‖u‖ ^ 2 ≤ d.upper*‖energyCoordinates d u‖ ^ 2 := by
  rw [energy_norm_sq]
  exact ⟨energyForm_lower d _,energyForm_upper d _⟩

omit [CompleteSpace Q] [CompleteSpace H] in
lemma energy_original_bound (u : EnergySpace d) :
    ‖energyCoordinates d u‖ ≤ (Real.sqrt d.lower)⁻¹*‖u‖ := by
  have hs := Real.sq_sqrt d.lower_pos.le
  have hp := Real.sqrt_pos.mpr d.lower_pos
  have hl := (energy_norm_sq_bounds d u).1
  have he : Real.sqrt d.lower * ‖energyCoordinates d u‖ ≤ ‖u‖ := by
    apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg u)
    simpa only [← sq,mul_pow,Real.sq_sqrt d.lower_pos.le] using hl
  calc
    _ = (Real.sqrt d.lower)⁻¹*(Real.sqrt d.lower*‖energyCoordinates d u‖) := by field_simp [ne_of_gt hp]
    _ ≤ _ := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hp.le)

omit [CompleteSpace Q] [CompleteSpace H] in
lemma energy_weighted_bound (u : Q) :
    ‖(energyCoordinates d).symm u‖ ≤ Real.sqrt d.upper * ‖u‖ := by
  have hu := d.lower_pos.le.trans d.lower_le_upper
  have hs := Real.sq_sqrt hu
  have hl := (energy_norm_sq_bounds d ((energyCoordinates d).symm u)).2
  rw [(energyCoordinates d).apply_symm_apply] at hl
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  simpa only [← sq,mul_pow,Real.sq_sqrt hu] using hl

def energyEquiv : EnergySpace d ≃L[ℂ] Q :=
  (energyCoordinates d).toContinuousLinearEquivOfBounds (Real.sqrt d.lower)⁻¹ (Real.sqrt d.upper)
    (energy_original_bound d) (energy_weighted_bound d)

instance energyCompleteSpace : CompleteSpace (EnergySpace d) := by
  let e : EnergySpace d ≃ᵤ Q :=
    { toEquiv := (energyEquiv d).toLinearEquiv.toEquiv
      uniformContinuous_toFun := (energyEquiv d).toContinuousLinearMap.uniformContinuous
      uniformContinuous_invFun := (energyEquiv d).symm.toContinuousLinearMap.uniformContinuous }
  exact e.completeSpace_iff.mpr inferInstance

/-- A named copy of the actual operator domain, equipped below with its energy norm. -/
def EnergyDomain (d : CoerciveFormData Q H) : Type _ :=
  (formOperator d).domain

instance energyDomainAddCommGroup : AddCommGroup (EnergyDomain d) :=
  inferInstanceAs (AddCommGroup (formOperator d).domain)
instance energyDomainModule : Module ℂ (EnergyDomain d) :=
  inferInstanceAs (Module ℂ (formOperator d).domain)

def energyDomainCoordinates : EnergyDomain d ≃ₗ[ℂ] (formOperator d).domain :=
  LinearEquiv.refl ℂ (formOperator d).domain

def operatorEnergyCoordinate : EnergyDomain d →ₗ[ℂ] EnergySpace d :=
  (energyCoordinates d).symm.toLinearMap.comp
    ((operatorFormCoordinate d).comp (energyDomainCoordinates d).toLinearMap)

lemma operatorEnergyCoordinate_injective : Function.Injective (operatorEnergyCoordinate d) :=
  (energyCoordinates d).symm.injective.comp
    ((operatorFormCoordinate_injective d).comp (energyDomainCoordinates d).injective)

instance energyDomainNormedAddCommGroup : NormedAddCommGroup (EnergyDomain d) :=
  NormedAddCommGroup.induced _ _ (operatorEnergyCoordinate d) (operatorEnergyCoordinate_injective d)

instance energyDomainInnerProductSpace : InnerProductSpace ℂ (EnergyDomain d) :=
  InnerProductSpace.induced (operatorEnergyCoordinate d)

/-- The energy-coordinate map is an isometry by the proved induced form norm. -/
def operatorEnergyIsometry : EnergyDomain d →ₗᵢ[ℂ] EnergySpace d where
  toLinearMap := operatorEnergyCoordinate d
  norm_map' _ := rfl

lemma operatorEnergy_inner (u v : EnergyDomain d) : ⟪u,v⟫_ℂ =
    ⟪(energyDomainCoordinates d u : H),formOperator d (energyDomainCoordinates d v)+
      (d.shift : ℂ) • (energyDomainCoordinates d v : H)⟫_ℂ := by
  change ⟪operatorEnergyCoordinate d u,operatorEnergyCoordinate d v⟫_ℂ = _
  rw [energy_inner]
  change energyForm d (operatorFormCoordinate d (energyDomainCoordinates d u))
    (operatorFormCoordinate d (energyDomainCoordinates d v)) = _
  rw [energyForm_apply,formOperator_form_identity,operatorFormCoordinate_embedding,
    operatorFormCoordinate_embedding,inner_add_right,inner_smul_right]

def solutionEnergy : H →L[ℂ] EnergySpace d := (energyEquiv d).symm.toContinuousLinearMap.comp (formSolution d)

lemma solutionEnergy_equation (u : EnergySpace d) (f : H) :
    ⟪u,solutionEnergy d f⟫_ℂ = ⟪d.embedding (energyCoordinates d u),f⟫_ℂ := by
  rw [energy_inner]
  change energyForm d (energyCoordinates d u) (formSolution d f) = _
  exact formSolution_equation d f _

lemma solutionEnergy_dense : DenseRange (solutionEnergy d) := by
  have ho : (solutionEnergy d).rangeᗮ = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro u hu
    have hi (f : H) : ⟪d.embedding (energyCoordinates d u),f⟫_ℂ = 0 := by
      rw [← solutionEnergy_equation]
      exact ((solutionEnergy d).range.mem_orthogonal' u).mp hu _
        (LinearMap.mem_range_self (solutionEnergy d).toLinearMap f)
    have hz : d.embedding (energyCoordinates d u) = 0 :=
      inner_self_eq_zero.mp (hi (d.embedding (energyCoordinates d u)))
    have hc : energyCoordinates d u = 0 := d.embedding_injective (hz.trans (map_zero d.embedding).symm)
    have he : u = 0 := (energyCoordinates d).injective (hc.trans (map_zero (energyCoordinates d)).symm)
    simpa only [Submodule.mem_bot] using he
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr
    ((solutionEnergy d).range.topologicalClosure_eq_top_iff.mpr ho)

lemma operatorEnergy_range : Set.range (operatorEnergyIsometry d) = Set.range (solutionEnergy d) := by
  ext u
  constructor
  · rintro ⟨v,rfl⟩
    refine ⟨inverseOperator (formResolvent d) (formResolvent_injective d) (energyDomainCoordinates d v),?_⟩
    rfl
  · rintro ⟨f,rfl⟩
    let x : (formOperator d).domain := ⟨formResolvent d f,LinearMap.mem_range_self _ f⟩
    refine ⟨(energyDomainCoordinates d).symm x,?_⟩
    change (energyCoordinates d).symm (formSolution d (inverseOperator
      (formResolvent d) (formResolvent_injective d)
      ⟨formResolvent d f,LinearMap.mem_range_self (formResolvent d).toLinearMap f⟩)) =
        (energyCoordinates d).symm (formSolution d f)
    rw [inverseOperator_left]

lemma operatorEnergy_dense : DenseRange (operatorEnergyIsometry d) := by
  change Dense (Set.range (operatorEnergyIsometry d))
  rw [operatorEnergy_range]
  exact solutionEnergy_dense d

/-- The actual energy-domain completion is canonically the full form Hilbert carrier. -/
def formCompletionEquiv : UniformSpace.Completion (EnergyDomain d) ≃ₗᵢ[ℂ] EnergySpace d :=
  completionTransportEquiv (operatorEnergyIsometry d) (operatorEnergy_dense d)

lemma formCompletionEquiv_coe (u : EnergyDomain d) :
    formCompletionEquiv d u = operatorEnergyCoordinate d u :=
  completionTransportEquiv_coe _ _ u

/-- Actual ambient inclusion, bounded for the energy norm. -/
def energyDomainEmbedding : EnergyDomain d →L[ℂ] H :=
  d.embedding.comp ((energyEquiv d).toContinuousLinearMap.comp (operatorEnergyIsometry d).toContinuousLinearMap)

lemma energyDomainEmbedding_apply (u : EnergyDomain d) :
    energyDomainEmbedding d u = (energyDomainCoordinates d u : H) :=
  operatorFormCoordinate_embedding d (energyDomainCoordinates d u)

lemma energyDomainEmbedding_bound (u : EnergyDomain d) :
    ‖energyDomainEmbedding d u‖ ≤ (‖d.embedding‖*(Real.sqrt d.lower)⁻¹)*‖u‖ := by
  calc
    _ ≤ ‖d.embedding‖ * ‖energyCoordinates d (operatorEnergyIsometry d u)‖ := d.embedding.le_opNorm _
    _ ≤ ‖d.embedding‖ * ((Real.sqrt d.lower)⁻¹*‖operatorEnergyIsometry d u‖) :=
      mul_le_mul_of_nonneg_left (energy_original_bound d _) (norm_nonneg _)
    _ = _ := by rw [(operatorEnergyIsometry d).norm_map]; ring

def completedEnergyEmbedding : UniformSpace.Completion (EnergyDomain d) →L[ℂ] H :=
  (energyDomainEmbedding d).fromCompletion

lemma completedEnergyEmbedding_intertwines : completedEnergyEmbedding d =
    d.embedding.comp ((energyEquiv d).toContinuousLinearMap.comp
      (formCompletionEquiv d).toContinuousLinearEquiv.toContinuousLinearMap) := by
  apply ContinuousLinearMap.fromCompletion_unique
  intro u
  change energyDomainEmbedding d u = d.embedding
    (energyEquiv d (formCompletionEquiv d (u : UniformSpace.Completion (EnergyDomain d))))
  rw [formCompletionEquiv_coe]
  rfl

lemma completedEnergyEmbedding_injective : Function.Injective (completedEnergyEmbedding d) := by
  rw [completedEnergyEmbedding_intertwines]
  exact d.embedding_injective.comp ((energyEquiv d).injective.comp (formCompletionEquiv d).injective)

lemma completedEnergyEmbedding_range : Set.range (completedEnergyEmbedding d) = Set.range d.embedding := by
  rw [completedEnergyEmbedding_intertwines]
  ext x
  constructor
  · rintro ⟨u,rfl⟩
    exact ⟨energyEquiv d (formCompletionEquiv d u),rfl⟩
  · rintro ⟨u,rfl⟩
    exact ⟨(formCompletionEquiv d).symm ((energyEquiv d).symm u),by simp⟩

lemma formDomain_approximation (u : Q) : ∃ f : ℕ → H,
    (∀ n, ‖solutionEnergy d (f n)-(energyCoordinates d).symm u‖ < ((n : ℝ)+1)⁻¹) ∧
    Filter.Tendsto (fun n => formSolution d (f n)) Filter.atTop (𝓝 u) ∧
    Filter.Tendsto (fun n => formResolvent d (f n)) Filter.atTop (𝓝 (d.embedding u)) ∧
    (∀ n, formResolvent d (f n) ∈ (formOperator d).domain) := by
  have hex (n : ℕ) : ∃ f : H,
      ‖solutionEnergy d f-(energyCoordinates d).symm u‖ < ((n : ℝ)+1)⁻¹ := by
    obtain ⟨f,hf⟩ := (solutionEnergy_dense d).exists_dist_lt ((energyCoordinates d).symm u)
      (show 0 < ((n : ℝ)+1)⁻¹ by positivity)
    refine ⟨f,?_⟩
    rw [dist_comm,dist_eq_norm] at hf
    exact hf
  choose f hf using hex
  have hs : Filter.Tendsto (fun n => ‖solutionEnergy d (f n)-(energyCoordinates d).symm u‖)
      Filter.atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) (fun n => (hf n).le)
      (by simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have ht : Filter.Tendsto (fun n => solutionEnergy d (f n)) Filter.atTop
      (𝓝 ((energyCoordinates d).symm u)) := tendsto_iff_norm_sub_tendsto_zero.mpr hs
  have hc1 (n : ℕ) : energyEquiv d (solutionEnergy d (f n)) = formSolution d (f n) :=
    (energyEquiv d).apply_symm_apply _
  have hc0 : energyEquiv d ((energyCoordinates d).symm u) = u :=
    (energyCoordinates d).apply_symm_apply u
  have horig : Filter.Tendsto (fun n => formSolution d (f n)) Filter.atTop (𝓝 u) := by
    simpa only [Function.comp_def,hc1,hc0] using ((energyEquiv d).continuous.tendsto _).comp ht
  have hamb : Filter.Tendsto (fun n => formResolvent d (f n)) Filter.atTop (𝓝 (d.embedding u)) := by
    exact (d.embedding.continuous.tendsto u).comp horig
  exact ⟨f,hf,horig,hamb,(fun n => LinearMap.mem_range_self _ (f n))⟩

/-- A larger admissible shift, on exactly the same q, J and original Q. -/
def largerShiftData (a : ℝ) (ha : d.shift ≤ a) : CoerciveFormData Q H where
  embedding := d.embedding
  embedding_injective := d.embedding_injective
  embedding_dense := d.embedding_dense
  form := d.form
  hermitian := d.hermitian
  continuous_form := d.continuous_form
  shift := a
  lower := d.lower
  upper := d.upper+(a-d.shift)*‖d.embedding‖ ^ 2
  lower_pos := d.lower_pos
  lower_le_upper := d.lower_le_upper.trans (le_add_of_nonneg_right
    (mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg _)))
  lower_bound u := by
    have hnon := mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg ‖d.embedding u‖)
    linarith [d.lower_bound u]
  upper_bound u := by
    have hb := pow_le_pow_left₀ (norm_nonneg _) (d.embedding.le_opNorm u) 2
    rw [mul_pow] at hb
    calc
      _ = ((d.form u u).re+d.shift*‖d.embedding u‖ ^ 2)+
          (a-d.shift)*‖d.embedding u‖ ^ 2 := by ring
      _ ≤ d.upper*‖u‖ ^ 2+(a-d.shift)*(‖d.embedding‖ ^ 2*‖u‖ ^ 2) :=
        add_le_add (d.upper_bound u) (mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr ha))
      _ = _ := by ring

omit [CompleteSpace Q] [CompleteSpace H] in
lemma energyForm_largerShift (a : ℝ) (ha : d.shift ≤ a) (u : Q) :
    (energyForm (largerShiftData d a ha) u u).re =
      (energyForm d u u).re+(a-d.shift)*‖d.embedding u‖ ^ 2 := by
  rw [energyForm_diagonal_re,energyForm_diagonal_re]
  change (d.form u u).re+a*‖d.embedding u‖ ^ 2 = _
  ring

omit [CompleteSpace Q] [CompleteSpace H] in
lemma energyForm_largerShift_bounds (a : ℝ) (ha : d.shift ≤ a) (u : Q) :
    (energyForm d u u).re ≤ (energyForm (largerShiftData d a ha) u u).re ∧
    (energyForm (largerShiftData d a ha) u u).re ≤
      (1+(a-d.shift)*‖d.embedding‖ ^ 2/d.lower)*(energyForm d u u).re := by
  rw [energyForm_largerShift]
  have hnon := mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg ‖d.embedding u‖)
  constructor
  · linarith
  · have hb := pow_le_pow_left₀ (norm_nonneg _) (d.embedding.le_opNorm u) 2
    rw [mul_pow] at hb
    have hc := energyForm_lower d u
    have hcoef : 0 ≤ (a-d.shift)*‖d.embedding‖ ^ 2/d.lower :=
      div_nonneg (mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg _)) d.lower_pos.le
    have hm := mul_le_mul_of_nonneg_left hc hcoef
    calc
      _ ≤ (energyForm d u u).re+(a-d.shift)*(‖d.embedding‖ ^ 2*‖u‖ ^ 2) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr ha))
      _ = (energyForm d u u).re+((a-d.shift)*‖d.embedding‖ ^ 2/d.lower)*(d.lower*‖u‖ ^ 2) := by
        field_simp [d.lower_pos.ne']
      _ ≤ (energyForm d u u).re+((a-d.shift)*‖d.embedding‖ ^ 2/d.lower)*(energyForm d u u).re :=
        add_le_add le_rfl hm
      _ = _ := by ring

lemma largerShift_same_operator (a : ℝ) (ha : d.shift ≤ a) :
    formOperator (largerShiftData d a ha) = formOperator d := by
  apply formOperator_unique d _ (formOperator_selfadjoint _)
  intro x
  refine ⟨operatorFormCoordinate (largerShiftData d a ha) x,
    operatorFormCoordinate_embedding (largerShiftData d a ha) x,?_⟩
  exact formOperator_form_identity (largerShiftData d a ha) x

lemma largerShift_same_embedded_domain (a : ℝ) (ha : d.shift ≤ a) :
    Set.range (completedEnergyEmbedding (largerShiftData d a ha)) =
      Set.range (completedEnergyEmbedding d) := by
  rw [completedEnergyEmbedding_range,completedEnergyEmbedding_range]
  rfl

/-- Uniqueness concerns the full self-adjoint operator and its full domain. -/
lemma coercive_form_representation : ∃! L : H →ₗ.[ℂ] H,
    IsSelfAdjointOperator L ∧ ∀ x : L.domain, ∃ u : Q,
      d.embedding u = (x : H) ∧ ∀ v, d.form v u = ⟪d.embedding v,L x⟫_ℂ := by
  refine ⟨formOperator d,⟨formOperator_selfadjoint d,?_⟩,?_⟩
  · intro x
    exact ⟨operatorFormCoordinate d x,operatorFormCoordinate_embedding d x,
      formOperator_form_identity d x⟩
  · intro L hL
    exact formOperator_unique d L hL.1 hL.2

def energyDomainToCompletion : EnergyDomain d →ₗᵢ[ℂ] UniformSpace.Completion (EnergyDomain d) :=
  UniformSpace.Completion.toComplₗᵢ

lemma formCompletion_initial_isometry (u : EnergyDomain d) :
    formCompletionEquiv d (energyDomainToCompletion d u) = operatorEnergyCoordinate d u :=
  formCompletionEquiv_coe d u

lemma formCompletion_inner (x y : UniformSpace.Completion (EnergyDomain d)) :
    ⟪formCompletionEquiv d x,formCompletionEquiv d y⟫_ℂ = ⟪x,y⟫_ℂ :=
  (formCompletionEquiv d).inner_map_map x y

lemma formOperator_energy_identity (u v : (formOperator d).domain) :
    energyForm d (operatorFormCoordinate d u) (operatorFormCoordinate d v) =
      ⟪(u : H),formOperator d v+(d.shift : ℂ) • (v : H)⟫_ℂ := by
  rw [energyForm_apply,formOperator_form_identity,operatorFormCoordinate_embedding,
    operatorFormCoordinate_embedding,inner_add_right,inner_smul_right]

lemma usualEnergy_shift_identity (u : (formOperator d).domain) :
    ‖(u : H)‖ ^ 2+(⟪(u : H),formOperator d u+(d.shift : ℂ) • (u : H)⟫_ℂ).re =
      (energyForm (largerShiftData d (d.shift+1) (by linarith))
        (operatorFormCoordinate d u) (operatorFormCoordinate d u)).re := by
  rw [energyForm_largerShift,formOperator_energy_identity,operatorFormCoordinate_embedding]
  ring

end GW.Operators
