module
public import GW.Fock.FockWeylGraphContinuity
public import GW.Operators.ClosureCore
public import GW.Analysis.BridgeUniformDerivatives
public import GW.Analysis.BridgeLaplaceMajorant
public import GW.Operators.GraphIntegration
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import GW.Operators.SelfadjointCriterion
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal
namespace GW.Fock

def ordinaryFieldClosure (f : OneBoson) : Carrier →ₗ.[ℂ] Carrier := (ordinaryField f).closure

lemma ordinaryField_isClosable (f : OneBoson) : (ordinaryField f).IsClosable :=
  GW.Operators.symmetric_isClosable (ordinaryField f) (ordinaryField_dense f) (ordinaryField_symmetric f)

lemma ordinaryFieldClosure_dense (f : OneBoson) :
    Dense ((ordinaryFieldClosure f).domain : Set Carrier) :=
  GW.Operators.symmetric_closure_dense (ordinaryField f) (ordinaryField_dense f)

lemma ordinaryFieldClosure_closed (f : OneBoson) : (ordinaryFieldClosure f).IsClosed :=
  GW.Operators.symmetric_closure_closed (ordinaryField f) (ordinaryField_dense f) (ordinaryField_symmetric f)

lemma ordinaryFieldClosure_symmetric (f : OneBoson) :
    (ordinaryFieldClosure f).IsFormalAdjoint (ordinaryFieldClosure f) :=
  GW.Operators.symmetric_closure_symmetric (ordinaryField f) (ordinaryField_dense f) (ordinaryField_symmetric f)

lemma ordinaryFieldClosure_extends (f : OneBoson) : ordinaryField f ≤ ordinaryFieldClosure f :=
  (ordinaryField f).le_closure

lemma ordinaryFieldClosure_graph (f : OneBoson) :
    (ordinaryField f).graph.topologicalClosure = (ordinaryFieldClosure f).graph :=
  (ordinaryField_isClosable f).graph_closure_eq_closure_graph


def ordinaryFieldHalfInput (f : OneBoson) (u : NumberWeightedDomain Sector (1/2) (by norm_num)) :
    (ordinaryField f).domain := numberHalfWeightedInput u

def ordinaryFieldHalfInputLinear (f : OneBoson) : NumberWeightedDomain Sector (1/2) (by norm_num) →ₗ[ℂ]
    (ordinaryField f).domain where
  toFun := ordinaryFieldHalfInput f
  map_add' u v := Subtype.ext ((numberDomainEmbedding (1/2) (by norm_num)).map_add u v)
  map_smul' c u := Subtype.ext ((numberDomainEmbedding (1/2) (by norm_num)).map_smul c u)

def ordinaryFieldHalfLinear (f : OneBoson) : NumberWeightedDomain Sector (1/2) (by norm_num) →ₗ[ℂ] Carrier :=
  (ordinaryField f).toFun.comp (ordinaryFieldHalfInputLinear f)

set_option backward.isDefEq.respectTransparency.types false in
lemma ordinaryFieldHalfLinear_norm (f : OneBoson) (u : NumberWeightedDomain Sector (1/2) (by norm_num)) :
    ‖ordinaryFieldHalfLinear f u‖ ≤ (2*‖f‖)*‖u‖ := by
  let v : (shiftedNumberPower Sector (1/2)).domain := u
  let w := numberHalfWeightedInput u
  have hC : ‖ordinaryCreation f (ordinaryCreationRootInput f w)‖ ≤ ‖f‖*‖u‖ := by
    have h := creation_root_norm ordinarySectorKernel (ordinaryKernel f) v
    rw [ordinaryKernel_opNorm] at h
    convert! h using 1
    congr 1
    congr 1
    exact Subtype.ext (numberDomainEmbedding_apply (1/2) (by norm_num) u)
  have hA : ‖ordinaryAnnihilation f (ordinaryAnnihilationRootInput f w)‖ ≤ ‖f‖*‖u‖ := by
    have h := annihilation_root_norm ordinarySectorKernel (ordinaryKernel f) w
    rw [ordinaryKernel_opNorm] at h
    exact h.trans (mul_le_mul_of_nonneg_left (numberHalfLinear_norm u) (norm_nonneg f))
  change ‖ordinaryAnnihilation f (ordinaryAnnihilationRootInput f w)+ordinaryCreation f (ordinaryCreationRootInput f w)‖ ≤ _
  calc
    _ ≤ ‖ordinaryAnnihilation f (ordinaryAnnihilationRootInput f w)‖+
      ‖ordinaryCreation f (ordinaryCreationRootInput f w)‖ := norm_add_le _ _
    _ ≤ ‖f‖*‖u‖+‖f‖*‖u‖ := add_le_add hA hC
    _ = _ := by ring

def ordinaryFieldHalfMap (f : OneBoson) : NumberWeightedDomain Sector (1/2) (by norm_num) →L[ℂ] Carrier :=
  (ordinaryFieldHalfLinear f).mkContinuous (2*‖f‖) (ordinaryFieldHalfLinear_norm f)

lemma ordinaryFieldHalfMap_graph (f : OneBoson) (u : NumberWeightedDomain Sector (1/2) (by norm_num)) :
    (numberDomainEmbedding (1/2) (by norm_num) u,ordinaryFieldHalfMap f u) ∈ (ordinaryField f).graph :=
  (ordinaryField f).mem_graph (ordinaryFieldHalfInput f u)

lemma ordinaryFieldHalfMap_range (f : OneBoson) :
    Set.range (numberDomainEmbedding (1/2) (by norm_num)) = ((ordinaryField f).domain : Set Carrier) := by
  ext u
  constructor
  · rintro ⟨v,rfl⟩
    exact (ordinaryFieldHalfInput f v).property
  · intro hu
    refine ⟨numberHalfGraphInput ⟨u,hu⟩,?_⟩
    exact numberHalfGraphInput_embedding ⟨u,hu⟩

lemma ordinaryFieldClosure_exponentialCore (f : OneBoson) :
    (ordinaryFieldClosure f).HasCore
      (numberHalfCore.map (numberDomainEmbedding (1/2) (by norm_num)).toLinearMap) := by
  apply GW.Operators.symmetric_closure_hasCore (ordinaryField f) (ordinaryField_dense f)
    (ordinaryField_symmetric f) (numberDomainEmbedding (1/2) (by norm_num)) (ordinaryFieldHalfMap f)
    (ordinaryFieldHalfMap_range f)
  · intro x
    exact ⟨ordinaryFieldHalfInput f x,rfl,rfl⟩
  · exact numberHalfCore_dense


def fieldHalfFiniteCore : Submodule ℂ (NumberWeightedDomain Sector (1/2) (by norm_num)) :=
  (finiteSectorDomain Sector).comap (numberDomainEmbedding (1/2) (by norm_num)).toLinearMap

set_option backward.isDefEq.respectTransparency.types false in
lemma fieldHalfFiniteCore_dense :
    Dense (fieldHalfFiniteCore : Set (NumberWeightedDomain Sector (1/2) (by norm_num))) := by
  intro u
  apply mem_closure_of_tendsto (numberWeightedCutoff_tendsto Sector (1/2) (by norm_num) u)
  apply Filter.Eventually.of_forall
  intro m
  change numberDomainEmbedding (1/2) (by norm_num) (numberWeightedCutoff Sector (1/2) (by norm_num) m u) ∈ finiteSectorDomain Sector
  rw [numberDomainEmbedding_apply]
  exact cutoff_mem_finiteSectorDomain Sector m _

lemma fieldHalfCore_map_eq (C : Submodule ℂ Carrier) (hC : C ≤ (numberPower Sector (1/2)).domain) :
    (C.comap (numberDomainEmbedding (1/2) (by norm_num)).toLinearMap).map
      (numberDomainEmbedding (1/2) (by norm_num)).toLinearMap = C := by
  ext u
  constructor
  · rintro ⟨v,hv,rfl⟩
    exact hv
  · intro hu
    refine ⟨numberHalfGraphInput ⟨u,hC hu⟩,?_,?_⟩
    · change numberDomainEmbedding (1/2) (by norm_num) (numberHalfGraphInput ⟨u,hC hu⟩) ∈ C
      rw [numberHalfGraphInput_embedding]
      exact hu
    · exact numberHalfGraphInput_embedding ⟨u,hC hu⟩

set_option backward.isDefEq.respectTransparency.types false in
lemma ordinaryFieldClosure_finiteCore (f : OneBoson) :
    (ordinaryFieldClosure f).HasCore (finiteSectorDomain Sector) := by
  have hc := GW.Operators.symmetric_closure_hasCore (ordinaryField f) (ordinaryField_dense f)
    (ordinaryField_symmetric f) (numberDomainEmbedding (1/2) (by norm_num)) (ordinaryFieldHalfMap f)
    (ordinaryFieldHalfMap_range f) (fun x => ⟨ordinaryFieldHalfInput f x,rfl,rfl⟩)
    fieldHalfFiniteCore fieldHalfFiniteCore_dense
  have he := fieldHalfCore_map_eq (finiteSectorDomain Sector)
    (finiteSectorDomain_le Sector (numberPowerCoefficient (1/2)))
  simp only [fieldHalfFiniteCore,he] at hc
  convert! hc using 1 <;> rfl

def fieldHalfNumberCore : Submodule ℂ (NumberWeightedDomain Sector (1/2) (by norm_num)) :=
  numberOperator.domain.comap (numberDomainEmbedding (1/2) (by norm_num)).toLinearMap

lemma fieldHalfNumberCore_dense :
    Dense (fieldHalfNumberCore : Set (NumberWeightedDomain Sector (1/2) (by norm_num))) := by
  apply fieldHalfFiniteCore_dense.mono
  intro u hu
  exact finiteSectorDomain_le Sector (fun n => (n:ℝ)) hu

set_option backward.isDefEq.respectTransparency.types false in
lemma ordinaryFieldClosure_numberCore (f : OneBoson) :
    (ordinaryFieldClosure f).HasCore numberOperator.domain := by
  have hc := GW.Operators.symmetric_closure_hasCore (ordinaryField f) (ordinaryField_dense f)
    (ordinaryField_symmetric f) (numberDomainEmbedding (1/2) (by norm_num)) (ordinaryFieldHalfMap f)
    (ordinaryFieldHalfMap_range f) (fun x => ⟨ordinaryFieldHalfInput f x,rfl,rfl⟩)
    fieldHalfNumberCore fieldHalfNumberCore_dense
  have hle : numberOperator.domain ≤ (numberPower Sector (1/2)).domain := by
    intro u hu
    exact (numberConjugationHalfInput ⟨u,hu⟩).property
  have he := fieldHalfCore_map_eq numberOperator.domain hle
  simp only [fieldHalfNumberCore,he] at hc
  convert! hc using 1 <;> rfl


lemma fieldHalfExponential_image :
    numberHalfCore.map (numberDomainEmbedding (1/2) (by norm_num)).toLinearMap = exponentialSpan ⊤ := by
  have hE (g : OneBoson) : numberDomainEmbedding (1/2) (by norm_num)
      (coherentExponentialWeighted (1/2) (by norm_num) g) = exponentialVector g := by
    rw [numberDomainEmbedding_apply,coherentExponentialWeighted_ambient]
  unfold numberHalfCore exponentialSpan
  rw [Submodule.map_span]
  congr 1
  ext u
  constructor
  · rintro ⟨v,⟨g,rfl⟩,rfl⟩
    exact ⟨g,Submodule.mem_top,hE g⟩
  · rintro ⟨g,_,rfl⟩
    exact ⟨coherentExponentialWeighted (1/2) (by norm_num) g,⟨⟨g,Submodule.mem_top⟩,rfl⟩,hE g⟩

lemma ordinaryFieldClosure_literalExponentialCore (f : OneBoson) :
    (ordinaryFieldClosure f).HasCore (exponentialSpan ⊤) := by
  have h := ordinaryFieldClosure_exponentialCore f
  rw [fieldHalfExponential_image] at h
  exact h


lemma ordinaryField_restriction_closure (f : OneBoson) (C : Submodule ℂ Carrier)
    (hC : C ≤ (ordinaryField f).domain) (hc : (ordinaryFieldClosure f).HasCore C) :
    ((ordinaryField f).domRestrict C).closure = ordinaryFieldClosure f := by
  rw [← GW.Operators.restriction_of_extension (ordinaryFieldClosure_extends f) C hC]
  exact hc.closure_eq

lemma ordinaryField_finite_restriction_closure (f : OneBoson) :
    ((ordinaryField f).domRestrict (finiteSectorDomain Sector)).closure = ordinaryFieldClosure f :=
  ordinaryField_restriction_closure f (finiteSectorDomain Sector)
    (finiteSectorDomain_le Sector (numberPowerCoefficient (1/2))) (ordinaryFieldClosure_finiteCore f)

lemma ordinaryField_number_restriction_closure (f : OneBoson) :
    ((ordinaryField f).domRestrict numberOperator.domain).closure = ordinaryFieldClosure f := by
  apply ordinaryField_restriction_closure f numberOperator.domain
    (fun u hu => (numberConjugationHalfInput ⟨u,hu⟩).property)
  exact ordinaryFieldClosure_numberCore f

lemma ordinaryField_exponential_restriction_closure (f : OneBoson) :
    ((ordinaryField f).domRestrict (exponentialSpan ⊤)).closure = ordinaryFieldClosure f := by
  apply ordinaryField_restriction_closure f (exponentialSpan ⊤)
  · apply Submodule.span_le.mpr
    rintro u ⟨g,_,rfl⟩
    exact (coherentFieldInput f g).property
  · exact ordinaryFieldClosure_literalExponentialCore f



def weylLineCoefficient (h g : OneBoson) (t : ℝ) : ℂ :=
  Complex.exp (((-(t^2*‖h‖^2)/2:ℝ):ℂ)-(t:ℂ)*⟪h,g⟫_ℂ)

lemma weylCoefficient_line (h g : OneBoson) (t : ℝ) :
    weylCoefficient (t • h) g = weylLineCoefficient h g t := by
  have hn : ‖t • h‖^2 = t^2*‖h‖^2 := by
    rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  have hi : ⟪t • h,g⟫_ℂ = (t:ℂ)*⟪h,g⟫_ℂ := by
    calc
      _ = ⟪(t:ℂ) • h,g⟫_ℂ := congrArg (fun z : OneBoson => ⟪z,g⟫_ℂ)
        (RCLike.real_smul_eq_coe_smul (K := ℂ) t h)
      _ = t • ⟪h,g⟫_ℂ := inner_smul_real_left h g t
      _ = _ := RCLike.real_smul_eq_coe_mul t ⟪h,g⟫_ℂ
  unfold weylCoefficient weylLineCoefficient
  rw [hn,hi]
  congr 1
  push_cast
  ring

lemma weylLineCoefficient_hasDerivAt (h g : OneBoson) (t : ℝ) :
    HasDerivAt (weylLineCoefficient h g)
      (weylLineCoefficient h g t * (-((t*‖h‖^2:ℝ):ℂ)-⟪h,g⟫_ℂ)) t := by
  have hr : HasDerivAt (fun s : ℝ => -(s^2*‖h‖^2)/2) (-(2*t*‖h‖^2)/2) t := by
    convert! (((hasDerivAt_id t).pow 2).mul_const (‖h‖^2)).neg.div_const 2 using 1 <;> simp only [id_eq] <;> ring
  have hc := (hr.ofReal_comp.sub ((hasDerivAt_id t).ofReal_comp.mul_const ⟪h,g⟫_ℂ)).cexp
  dsimp only [Pi.sub_apply,id_eq] at hc
  convert! hc using 1
  simp only [weylLineCoefficient]
  push_cast
  ring

set_option backward.isDefEq.respectTransparency.types false in
lemma exponentialVector_line_hasDerivAt (g h : OneBoson) (t : ℝ) :
    HasDerivAt (fun s : ℝ => exponentialVector (g+s • h)) (coherentCreatorOne (g+t • h) h) t := by
  have hc : HasDerivAt (fun s : ℝ => g+s • h) h t := by
    simpa only [id_eq,one_smul] using ((hasDerivAt_id t).smul_const h).const_add g
  have hp := (exponentialVector_hasFDerivAt_creator (g+t • h)).restrictScalars ℝ
  have hh := hp.comp_hasDerivAt t hc
  convert! hh using 1
  exact (coherentCreatorOneLinear_apply (g+t • h) h).symm

set_option backward.isDefEq.respectTransparency.types false in
lemma weyl_coherent_line_hasDerivAt (h g : OneBoson) (t : ℝ) :
    HasDerivAt (fun s : ℝ => weylUnitary (s • h) (exponentialVector g))
      (weylLineCoefficient h g t • coherentCreatorOne (g+t • h) h+
       (weylLineCoefficient h g t * (-((t*‖h‖^2:ℝ):ℂ)-⟪h,g⟫_ℂ)) • exponentialVector (g+t • h)) t := by
  have hd := (weylLineCoefficient_hasDerivAt h g t).smul (exponentialVector_line_hasDerivAt g h t)
  simp only [weylUnitary_exponential,weylCoherent,weylCoefficient_line]
  convert! hd using 1 <;> rfl


lemma weylCoherentAnnihilation_action (f h g : OneBoson) :
    ordinaryAnnihilation h (weylCoherentAnnihilationInput f h g) =
      weylCoefficient f g • (⟪h,g+f⟫_ℂ • exponentialVector (g+f)) := by
  calc
    _ = ordinaryAnnihilation h (weylCoefficient f g •
        ordinaryAnnihilationAllInput h (coherentExponentialAll (g+f))) :=
      congrArg (ordinaryAnnihilation h) (weylCoherentAnnihilationInput_eq f h g)
    _ = weylCoefficient f g • ordinaryAnnihilation h
        (ordinaryAnnihilationAllInput h (coherentExponentialAll (g+f))) :=
      (ordinaryAnnihilation h).toFun.map_smul _ _
    _ = _ := by rw [exponentialVector_annihilation]

lemma coherentLine_inner (h g : OneBoson) (t : ℝ) :
    ⟪h,g+t • h⟫_ℂ = ⟪h,g⟫_ℂ+(t:ℂ)*((‖h‖^2:ℝ):ℂ) := by
  rw [inner_add_right,RCLike.real_smul_eq_coe_smul (K := ℂ) t h,
    inner_smul_right,inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

set_option backward.isDefEq.respectTransparency.types false in
lemma weyl_coherent_generator_hasDerivAt (h g : OneBoson) (t : ℝ) :
    HasDerivAt (fun s : ℝ => weylUnitary (s • h) (exponentialVector g))
      (ordinaryCreation h (weylCoherentCreationInput (t • h) h g)-
       ordinaryAnnihilation h (weylCoherentAnnihilationInput (t • h) h g)) t := by
  have hd := weyl_coherent_line_hasDerivAt h g t
  convert! hd using 1
  rw [weylCoherentCreation_action,weylCoherentAnnihilation_action,weylCoefficient_line,coherentLine_inner]
  push_cast
  module


def fieldWeylCoherentInput (f h g : OneBoson) : (ordinaryField f).domain :=
  weylCoefficient h g • coherentFieldInput f (g+h)

lemma fieldWeylCoherentInput_value (f h g : OneBoson) :
    (fieldWeylCoherentInput f h g).val = weylUnitary h (exponentialVector g) := by
  change weylCoefficient h g • exponentialVector (g+h) = _
  rw [weylUnitary_exponential]

lemma fieldWeylCoherent_action (f h g : OneBoson) :
    ordinaryField f (fieldWeylCoherentInput f h g) =
      weylCoefficient h g • (⟪f,g+h⟫_ℂ • exponentialVector (g+h)+coherentCreatorOne (g+h) f) := by
  calc
    _ = weylCoefficient h g • ordinaryField f (coherentFieldInput f (g+h)) :=
      (ordinaryField f).toFun.map_smul _ _
    _ = _ := by rw [coherentField_action]

lemma coherentCreatorOne_smul (g h : OneBoson) (c : ℂ) :
    coherentCreatorOne g (c • h) = c • coherentCreatorOne g h := by
  rw [← coherentCreatorOneLinear_apply,map_smul,coherentCreatorOneLinear_apply]

set_option backward.isDefEq.respectTransparency.types false in
lemma weyl_coherent_field_hasDerivAt (f g : OneBoson) (t : ℝ) :
    HasDerivAt (fun s : ℝ => weylUnitary (s • (Complex.I • f)) (exponentialVector g))
      (Complex.I • ordinaryField f (fieldWeylCoherentInput f (t • (Complex.I • f)) g)) t := by
  have hd := weyl_coherent_line_hasDerivAt (Complex.I • f) g t
  have hn : ‖Complex.I • f‖^2 = ‖f‖^2 := by rw [norm_smul,Complex.norm_I,one_mul]
  have hi : ⟪Complex.I • f,g⟫_ℂ = -Complex.I*⟪f,g⟫_ℂ := by simp [inner_smul_left]
  have hz : ⟪f,g+t • (Complex.I • f)⟫_ℂ =
      ⟪f,g⟫_ℂ+(t:ℂ)*Complex.I*((‖f‖^2:ℝ):ℂ) := by
    rw [inner_add_right,RCLike.real_smul_eq_coe_smul (K := ℂ) t (Complex.I • f),
      inner_smul_right,inner_smul_right,inner_self_eq_norm_sq_to_K]
    push_cast
    ring_nf
    convert! congrArg (fun z : ℂ => ⟪f,g⟫_ℂ+z*(‖f‖:ℂ)^2)
      (mul_comm (t:ℂ) Complex.I) using 1 <;> rfl
  have hs : Complex.I*(weylLineCoefficient (Complex.I • f) g t * ⟪f,g+t • (Complex.I • f)⟫_ℂ) =
      weylLineCoefficient (Complex.I • f) g t * (-((t*‖Complex.I • f‖^2:ℝ):ℂ)-⟪Complex.I • f,g⟫_ℂ) := by
    rw [hz,hi,hn]
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring
  convert! hd using 1
  rw [fieldWeylCoherent_action,weylCoefficient_line,coherentCreatorOne_smul]
  simp only [smul_add,smul_smul,mul_assoc]
  rw [hs]
  module


def fieldOrbit (f : OneBoson) (t : ℝ) : NumberWeightedDomain Sector (1/2) (by norm_num) →L[ℂ]
    NumberWeightedDomain Sector (1/2) (by norm_num) :=
  weylWeightedMap (1/2) (by norm_num) (by norm_num) (t • (Complex.I • f))

def fieldOrbitValue (f : OneBoson) (t : ℝ) : NumberWeightedDomain Sector (1/2) (by norm_num) →L[ℂ] Carrier :=
  (numberDomainEmbedding (1/2) (by norm_num)).comp (fieldOrbit f t)

def fieldOrbitDerivative (f : OneBoson) (t : ℝ) : NumberWeightedDomain Sector (1/2) (by norm_num) →L[ℂ] Carrier :=
  Complex.I • ((ordinaryFieldHalfMap f).comp (fieldOrbit f t))

lemma fieldOrbitValue_apply (f : OneBoson) (t : ℝ) (u : NumberWeightedDomain Sector (1/2) (by norm_num)) :
    fieldOrbitValue f t u = weylUnitary (t • (Complex.I • f)) (numberDomainEmbedding (1/2) (by norm_num) u) :=
  weylWeightedInput_embedding (1/2) (by norm_num) (by norm_num) _ u

set_option backward.isDefEq.respectTransparency.types false in
lemma fieldOrbit_continuous (f : OneBoson) (u : NumberWeightedDomain Sector (1/2) (by norm_num)) :
    Continuous (fun t : ℝ => fieldOrbit f t u) := by
  have hc : Continuous (fun t : ℝ => t • (Complex.I • f)) := by fun_prop
  have hh := (weylWeightedMap_joint_continuous (1/2) (by norm_num) (by norm_num)).comp
    (hc.prodMk (continuous_const : Continuous (fun _ : ℝ => u)))
  convert! hh using 1 <;> rfl

lemma fieldOrbitDerivative_continuous (f : OneBoson) (u : NumberWeightedDomain Sector (1/2) (by norm_num)) :
    Continuous (fun t : ℝ => fieldOrbitDerivative f t u) :=
  ((ordinaryFieldHalfMap f).continuous.comp (fieldOrbit_continuous f u)).const_smul Complex.I

set_option backward.isDefEq.respectTransparency.types false in
lemma fieldOrbit_norm (f : OneBoson) (t : ℝ) (u : NumberWeightedDomain Sector (1/2) (by norm_num)) :
    ‖fieldOrbit f t u‖ ≤ (1+|t| *‖f‖)*‖u‖ := by
  have h := weylWeightedInput_norm (1/2) (by norm_num) (by norm_num) (t • (Complex.I • f)) u
  norm_num only [show (2*(1/2):ℝ) = 1 by ring,Real.rpow_one,norm_smul,Complex.norm_I,
    one_mul,mul_one,Real.norm_eq_abs] at h
  exact h

lemma fieldOrbitDerivative_norm (f : OneBoson) (t : ℝ) (u : NumberWeightedDomain Sector (1/2) (by norm_num)) :
    ‖fieldOrbitDerivative f t u‖ ≤ (2*‖f‖)*(1+|t| *‖f‖)*‖u‖ := by
  change ‖Complex.I • ordinaryFieldHalfMap f (fieldOrbit f t u)‖ ≤ _
  rw [norm_smul,Complex.norm_I,one_mul]
  exact (ordinaryFieldHalfLinear_norm f (fieldOrbit f t u)).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (fieldOrbit_norm f t u) (by positivity : 0 ≤ 2*‖f‖))

set_option backward.isDefEq.respectTransparency.types false in
lemma fieldOrbit_coherent_hasDerivAt (f g : OneBoson) (t : ℝ) :
    HasDerivAt (fun s : ℝ => fieldOrbitValue f s (coherentExponentialWeighted (1/2) (by norm_num) g))
      (fieldOrbitDerivative f t (coherentExponentialWeighted (1/2) (by norm_num) g)) t := by
  have hd := weyl_coherent_field_hasDerivAt f g t
  have he : ordinaryFieldHalfInput f (fieldOrbit f t (coherentExponentialWeighted (1/2) (by norm_num) g)) =
      fieldWeylCoherentInput f (t • (Complex.I • f)) g := by
    apply Subtype.ext
    change fieldOrbitValue f t (coherentExponentialWeighted (1/2) (by norm_num) g) = _
    rw [fieldOrbitValue_apply,numberDomainEmbedding_apply,coherentExponentialWeighted_ambient,
      fieldWeylCoherentInput_value]
  simp only [fieldOrbitValue_apply,numberDomainEmbedding_apply,coherentExponentialWeighted_ambient]
  convert! hd using 1
  change Complex.I • ordinaryField f (ordinaryFieldHalfInput f
    (fieldOrbit f t (coherentExponentialWeighted (1/2) (by norm_num) g))) = _
  rw [he]


set_option backward.isDefEq.respectTransparency.types false in
lemma fieldOrbit_span_hasDerivAt (f : OneBoson) (u : NumberWeightedDomain Sector (1/2) (by norm_num))
    (hu : u ∈ numberHalfCore) (t : ℝ) :
    HasDerivAt (fun s : ℝ => fieldOrbitValue f s u) (fieldOrbitDerivative f t u) t := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g,rfl⟩ := hx
    exact fieldOrbit_coherent_hasDerivAt f g t
  | zero =>
    simpa only [map_zero] using hasDerivAt_const t (0:Carrier)
  | add x y hx hy ihx ihy =>
    simp only [map_add]
    convert! ihx.add ihy using 1 <;> rfl
  | smul a x hx ih =>
    simp only [map_smul]
    convert! ih.const_smul a using 1 <;> rfl

lemma fieldOrbitDerivative_compact_bound (f : OneBoson) (a b t : ℝ) (ht : t ∈ uIcc a b)
    (u : NumberWeightedDomain Sector (1/2) (by norm_num)) :
    ‖fieldOrbitDerivative f t u‖ ≤ (2*‖f‖)*(1+max |a| |b| *‖f‖)*‖u‖ := by
  have habs : |t| ≤ max |a| |b| := by
    rcases le_total a b with hab | hba
    · rw [uIcc_of_le hab] at ht
      exact abs_le_max_abs_abs ht.1 ht.2
    · rw [uIcc_comm,uIcc_of_le hba] at ht
      simpa only [max_comm] using abs_le_max_abs_abs ht.1 ht.2
  apply (fieldOrbitDerivative_norm f t u).trans
  gcongr

set_option backward.isDefEq.respectTransparency.types false in
lemma fieldOrbitDerivative_uniform (f : OneBoson)
    (v : ℕ → NumberWeightedDomain Sector (1/2) (by norm_num))
    (u : NumberWeightedDomain Sector (1/2) (by norm_num)) (hu : Tendsto v atTop (𝓝 u)) (a b : ℝ) :
    TendstoUniformlyOn (fun n t => fieldOrbitDerivative f t (v n))
      (fun t => fieldOrbitDerivative f t u) atTop (uIcc a b) := by
  let K := (2*‖f‖)*(1+max |a| |b| *‖f‖)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.mp hu) (ε/(K+1)) (div_pos hε (by positivity))] with n hn t ht
  rw [dist_comm,dist_eq_norm,← map_sub]
  have hb := fieldOrbitDerivative_compact_bound f a b t ht (v n-u)
  have he := (lt_div_iff₀ (by positivity : 0 < K+1)).mp hn
  rw [dist_eq_norm] at he
  change _ ≤ K*‖v n-u‖ at hb
  nlinarith [norm_nonneg (v n-u)]

set_option backward.isDefEq.respectTransparency.types false in
lemma fieldOrbit_hasDerivAt (f : OneBoson) (u : NumberWeightedDomain Sector (1/2) (by norm_num)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => fieldOrbitValue f s u) (fieldOrbitDerivative f t u) t := by
  obtain ⟨v,hv,hvu⟩ := mem_closure_iff_seq_limit.mp (numberHalfCore_dense u)
  have hr := GW.Analysis.uniformDerivativeLimit (F := Carrier) (J := Set.univ) isOpen_univ
    (t₀ := (0:ℝ)) (Set.mem_univ 0)
    (cN := fun n t => fieldOrbitValue f t (v n))
    (dN := fun n t => fieldOrbitDerivative f t (v n))
    (d := fun t => fieldOrbitDerivative f t u) (c₀ := fieldOrbitValue f 0 u)
    (fun n t _ => fieldOrbit_span_hasDerivAt f (v n) (hv n) t)
    (fun n => (fieldOrbitDerivative_continuous f (v n)).continuousOn)
    (((fieldOrbitValue f 0).continuous.tendsto u).comp hvu)
    (fun a b _ => fieldOrbitDerivative_uniform f v u hvu a b)
  have hC : connectedComponentIn (Set.univ : Set ℝ) (0:ℝ) = Set.univ := by
    rw [connectedComponentIn_univ,PreconnectedSpace.connectedComponent_eq_univ]
  have he := hr.2.2.2.2.2 (fun s => fieldOrbitValue f s u)
    (fun s _ => ((fieldOrbitValue f s).continuous.tendsto u).comp hvu)
  have hfun : (fun s => fieldOrbitValue f s u) = GW.Analysis.integratedDerivative 0
      (fieldOrbitValue f 0 u) (fun s => fieldOrbitDerivative f s u) := by
    funext s
    exact he (by simp only [hC,Set.mem_univ])
  rw [hfun]
  exact hr.2.2.1 t (by simp only [hC,Set.mem_univ])


def fieldLaplacePlus (f : OneBoson) (u : NumberWeightedDomain Sector (1/2) (by norm_num)) :
    NumberWeightedDomain Sector (1/2) (by norm_num) :=
  GW.Analysis.laplaceGraphIntegral (fun t => fieldOrbit f t u)

def fieldLaplaceMinus (f : OneBoson) (u : NumberWeightedDomain Sector (1/2) (by norm_num)) :
    NumberWeightedDomain Sector (1/2) (by norm_num) :=
  GW.Analysis.laplaceGraphIntegral (fun t => fieldOrbit f (-t) u)

set_option backward.isDefEq.respectTransparency.types false in
lemma fieldLaplace_pair (f : OneBoson) (u : NumberWeightedDomain Sector (1/2) (by norm_num)) :
    (numberDomainEmbedding (1/2) (by norm_num)-Complex.I • ordinaryFieldHalfMap f) (fieldLaplacePlus f u) =
      numberDomainEmbedding (1/2) (by norm_num) u ∧
    (numberDomainEmbedding (1/2) (by norm_num)+Complex.I • ordinaryFieldHalfMap f) (fieldLaplaceMinus f u) =
      numberDomainEmbedding (1/2) (by norm_num) u := by
  let V : ℝ → Carrier →ₗᵢ[ℂ] Carrier := fun t => weylIsometry (t • (Complex.I • f))
  apply GW.Analysis.laplaceGraph_resolvent_pair
    (numberDomainEmbedding (1/2) (by norm_num)) (ordinaryFieldHalfMap f) V
    (fun t => fieldOrbit f t u) u ‖f‖ (norm_nonneg f) (fieldOrbit_continuous f u)
  · intro t
    exact fieldOrbitValue_apply f t u
  · intro w
    change weylIsometry ((0:ℝ) • (Complex.I • f)) w = w
    rw [zero_smul]
    exact congrArg (fun L : Carrier →L[ℂ] Carrier => L w) weylIsometry_zero
  · intro t ht
    simpa only [abs_of_nonneg ht,mul_comm] using fieldOrbit_norm f t u
  · intro t ht
    simpa only [Function.comp_def,abs_neg,abs_of_nonneg ht,mul_comm] using fieldOrbit_norm f (-t) u
  · intro t
    exact fieldOrbit_hasDerivAt f u t


section AmbientNorm

variable {X H : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

lemma fieldLaplace_ambient_norm (J : X →L[ℂ] H) (v : ℝ → X)
    (hv : IntegrableOn (GW.Analysis.laplaceGraphIntegrand v) (Ici (0:ℝ)) volume)
    (a : ℝ) (hn : ∀ t, ‖J (v t)‖ = a) :
    ‖J (GW.Analysis.laplaceGraphIntegral v)‖ ≤ a := by
  unfold GW.Analysis.laplaceGraphIntegral
  rw [← J.integral_comp_comm hv]
  calc
    _ ≤ ∫ t in Ici (0:ℝ), ‖J (GW.Analysis.laplaceGraphIntegrand v t)‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ t in Ici (0:ℝ), Real.exp (-t)*a := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro t
      change ‖(J.restrictScalars ℝ) (Real.exp (-t) • v t)‖ = _
      rw [map_smul,norm_smul,Real.norm_of_nonneg (Real.exp_nonneg _)]
      change Real.exp (-t)*‖J (v t)‖ = Real.exp (-t)*a
      rw [hn]
    _ = a := by
      rw [integral_mul_const,integral_Ici_eq_integral_Ioi,integral_exp_neg_Ioi_zero,one_mul]


def fieldLaplace_integralLinear (T : ℝ → X →L[ℂ] X)
    (hi : ∀ u, IntegrableOn (GW.Analysis.laplaceGraphIntegrand (fun t => T t u)) (Ici (0:ℝ)) volume) :
    X →ₗ[ℂ] X where
  toFun u := GW.Analysis.laplaceGraphIntegral (fun t => T t u)
  map_add' u v := by
    unfold GW.Analysis.laplaceGraphIntegral
    rw [← integral_add (hi u) (hi v)]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    change Real.exp (-t) • T t (u+v) = Real.exp (-t) • T t u+Real.exp (-t) • T t v
    rw [map_add,smul_add]
  map_smul' c u := by
    unfold GW.Analysis.laplaceGraphIntegral
    rw [← integral_smul]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    change Real.exp (-t) • T t (c • u) = c • (Real.exp (-t) • T t u)
    rw [map_smul,smul_comm]


end AmbientNorm

lemma fieldLaplace_plus_integrable (f : OneBoson) (u : NumberWeightedDomain Sector (1/2) (by norm_num)) :
    IntegrableOn (GW.Analysis.laplaceGraphIntegrand (fun t => fieldOrbit f t u)) (Ici (0:ℝ)) volume := by
  apply GW.Analysis.laplaceGraphIntegrand_integrable _ (fieldOrbit_continuous f u) u ‖f‖ (norm_nonneg f)
  intro t ht
  simpa only [abs_of_nonneg ht,mul_comm] using fieldOrbit_norm f t u

lemma fieldLaplace_minus_integrable (f : OneBoson) (u : NumberWeightedDomain Sector (1/2) (by norm_num)) :
    IntegrableOn (GW.Analysis.laplaceGraphIntegrand (fun t => fieldOrbit f (-t) u)) (Ici (0:ℝ)) volume := by
  apply GW.Analysis.laplaceGraphIntegrand_integrable _ ((fieldOrbit_continuous f u).comp continuous_neg)
    u ‖f‖ (norm_nonneg f)
  intro t ht
  simpa only [Function.comp_def,abs_neg,abs_of_nonneg ht,mul_comm] using fieldOrbit_norm f (-t) u

def fieldLaplacePlusLinear (f : OneBoson) : NumberWeightedDomain Sector (1/2) (by norm_num) →ₗ[ℂ] Carrier :=
  (numberDomainEmbedding (1/2) (by norm_num)).toLinearMap.comp
    (fieldLaplace_integralLinear (fieldOrbit f) (fieldLaplace_plus_integrable f))

def fieldLaplaceMinusLinear (f : OneBoson) : NumberWeightedDomain Sector (1/2) (by norm_num) →ₗ[ℂ] Carrier :=
  (numberDomainEmbedding (1/2) (by norm_num)).toLinearMap.comp
    (fieldLaplace_integralLinear (fun t => fieldOrbit f (-t)) (fieldLaplace_minus_integrable f))

lemma fieldLaplacePlusLinear_apply (f : OneBoson) (u : NumberWeightedDomain Sector (1/2) (by norm_num)) :
    fieldLaplacePlusLinear f u = numberDomainEmbedding (1/2) (by norm_num) (fieldLaplacePlus f u) := rfl

lemma fieldLaplaceMinusLinear_apply (f : OneBoson) (u : NumberWeightedDomain Sector (1/2) (by norm_num)) :
    fieldLaplaceMinusLinear f u = numberDomainEmbedding (1/2) (by norm_num) (fieldLaplaceMinus f u) := rfl

lemma fieldLaplacePlusLinear_norm (f : OneBoson) (u : NumberWeightedDomain Sector (1/2) (by norm_num)) :
    ‖fieldLaplacePlusLinear f u‖ ≤ ‖numberDomainEmbedding (1/2) (by norm_num) u‖ := by
  apply fieldLaplace_ambient_norm (numberDomainEmbedding (1/2) (by norm_num))
    (fun t => fieldOrbit f t u) (fieldLaplace_plus_integrable f u)
  intro t
  change ‖fieldOrbitValue f t u‖ = _
  rw [fieldOrbitValue_apply,LinearIsometryEquiv.norm_map]

lemma fieldLaplaceMinusLinear_norm (f : OneBoson) (u : NumberWeightedDomain Sector (1/2) (by norm_num)) :
    ‖fieldLaplaceMinusLinear f u‖ ≤ ‖numberDomainEmbedding (1/2) (by norm_num) u‖ := by
  apply fieldLaplace_ambient_norm (numberDomainEmbedding (1/2) (by norm_num))
    (fun t => fieldOrbit f (-t) u) (fieldLaplace_minus_integrable f u)
  intro t
  change ‖fieldOrbitValue f (-t) u‖ = _
  rw [fieldOrbitValue_apply,LinearIsometryEquiv.norm_map]

lemma fieldHalfEmbedding_dense : DenseRange (numberDomainEmbedding (1/2) (by norm_num)) := by
  change Dense (Set.range (numberDomainEmbedding (1/2) (by norm_num)))
  rw [ordinaryFieldHalfMap_range (0:OneBoson)]
  exact ordinaryField_dense 0

def fieldResolventPlus (f : OneBoson) : Carrier →L[ℂ] Carrier :=
  (fieldLaplacePlusLinear f).extendOfNorm (numberDomainEmbedding (1/2) (by norm_num)).toLinearMap

def fieldResolventMinus (f : OneBoson) : Carrier →L[ℂ] Carrier :=
  (fieldLaplaceMinusLinear f).extendOfNorm (numberDomainEmbedding (1/2) (by norm_num)).toLinearMap

set_option backward.isDefEq.respectTransparency.types false in
lemma fieldResolventPlus_core (f : OneBoson) (u : NumberWeightedDomain Sector (1/2) (by norm_num)) :
    fieldResolventPlus f (numberDomainEmbedding (1/2) (by norm_num) u) = fieldLaplacePlusLinear f u :=
  LinearMap.extendOfNorm_eq fieldHalfEmbedding_dense ⟨1,fun u => by
    simp only [one_mul]
    convert! fieldLaplacePlusLinear_norm f u using 1 <;> rfl⟩ u

set_option backward.isDefEq.respectTransparency.types false in
lemma fieldResolventMinus_core (f : OneBoson) (u : NumberWeightedDomain Sector (1/2) (by norm_num)) :
    fieldResolventMinus f (numberDomainEmbedding (1/2) (by norm_num) u) = fieldLaplaceMinusLinear f u :=
  LinearMap.extendOfNorm_eq fieldHalfEmbedding_dense ⟨1,fun u => by
    simp only [one_mul]
    convert! fieldLaplaceMinusLinear_norm f u using 1 <;> rfl⟩ u

set_option backward.isDefEq.respectTransparency.types false in
lemma fieldResolventPlus_norm (f : OneBoson) (u : Carrier) : ‖fieldResolventPlus f u‖ ≤ ‖u‖ := by
  have hn := LinearMap.norm_extendOfNorm_apply_le
    (f := fieldLaplacePlusLinear f) (e := (numberDomainEmbedding (1/2) (by norm_num)).toLinearMap)
    fieldHalfEmbedding_dense 1 (fun u => by
    simp only [one_mul]
    convert! fieldLaplacePlusLinear_norm f u using 1 <;> rfl) u
  simp only [one_mul] at hn
  convert! hn using 1 <;> rfl

set_option backward.isDefEq.respectTransparency.types false in
lemma fieldResolventMinus_norm (f : OneBoson) (u : Carrier) : ‖fieldResolventMinus f u‖ ≤ ‖u‖ := by
  have hn := LinearMap.norm_extendOfNorm_apply_le
    (f := fieldLaplaceMinusLinear f) (e := (numberDomainEmbedding (1/2) (by norm_num)).toLinearMap)
    fieldHalfEmbedding_dense 1 (fun u => by
    simp only [one_mul]
    convert! fieldLaplaceMinusLinear_norm f u using 1 <;> rfl) u
  simp only [one_mul] at hn
  convert! hn using 1 <;> rfl


lemma field_i_square : Complex.I*Complex.I = -1 := by rw [← pow_two,Complex.I_sq]

lemma fieldResolvent_algebra (s : ℂ) (hs : s*s = -1) (x y z : Carrier) (he : x-s • y = z) :
    y = s • (z-x) := by
  calc
    y = s • (x-s • y)-s • x := by rw [smul_sub,smul_smul,hs,neg_one_smul]; abel
    _ = s • z-s • x := by rw [he]
    _ = s • (z-x) := by rw [smul_sub]

set_option backward.isDefEq.respectTransparency.types false in
lemma fieldLaplacePlus_graph (f : OneBoson) (u : NumberWeightedDomain Sector (1/2) (by norm_num)) :
    (fieldLaplacePlusLinear f u,Complex.I • (numberDomainEmbedding (1/2) (by norm_num) u-fieldLaplacePlusLinear f u)) ∈
      (ordinaryFieldClosure f).graph := by
  have hp := (fieldLaplace_pair f u).1
  change numberDomainEmbedding (1/2) (by norm_num) (fieldLaplacePlus f u)-
    Complex.I • ordinaryFieldHalfMap f (fieldLaplacePlus f u) = numberDomainEmbedding (1/2) (by norm_num) u at hp
  have he := fieldResolvent_algebra Complex.I field_i_square _ _ _ hp
  have hg := (LinearPMap.le_graph_of_le (ordinaryFieldClosure_extends f))
    (ordinaryFieldHalfMap_graph f (fieldLaplacePlus f u))
  rw [he] at hg
  exact hg

set_option backward.isDefEq.respectTransparency.types false in
lemma fieldLaplaceMinus_graph (f : OneBoson) (u : NumberWeightedDomain Sector (1/2) (by norm_num)) :
    (fieldLaplaceMinusLinear f u,(-Complex.I) • (numberDomainEmbedding (1/2) (by norm_num) u-fieldLaplaceMinusLinear f u)) ∈
      (ordinaryFieldClosure f).graph := by
  have hp := (fieldLaplace_pair f u).2
  change numberDomainEmbedding (1/2) (by norm_num) (fieldLaplaceMinus f u)+
    Complex.I • ordinaryFieldHalfMap f (fieldLaplaceMinus f u) = numberDomainEmbedding (1/2) (by norm_num) u at hp
  have hphase : (-Complex.I)*(-Complex.I) = -1 := by rw [neg_mul_neg,field_i_square]
  have he := fieldResolvent_algebra (-Complex.I) hphase
    (numberDomainEmbedding (1/2) (by norm_num) (fieldLaplaceMinus f u))
    (ordinaryFieldHalfMap f (fieldLaplaceMinus f u)) (numberDomainEmbedding (1/2) (by norm_num) u)
    (by simpa only [neg_smul,sub_neg_eq_add] using hp)
  have hg := (LinearPMap.le_graph_of_le (ordinaryFieldClosure_extends f))
    (ordinaryFieldHalfMap_graph f (fieldLaplaceMinus f u))
  rw [he] at hg
  exact hg

set_option backward.isDefEq.respectTransparency.types false in
lemma fieldResolvent_closed_extension (f : OneBoson) (R : Carrier →L[ℂ] Carrier) (s : ℂ)
    (hcore : ∀ v : NumberWeightedDomain Sector (1/2) (by norm_num),
      (R (numberDomainEmbedding (1/2) (by norm_num) v),
       s • (numberDomainEmbedding (1/2) (by norm_num) v-R (numberDomainEmbedding (1/2) (by norm_num) v))) ∈
        (ordinaryFieldClosure f).graph) (u : Carrier) :
    (R u,s • (u-R u)) ∈ (ordinaryFieldClosure f).graph := by
  let P := R.prod (s • (ContinuousLinearMap.id ℂ Carrier-R))
  let S : Set Carrier := {z | (R z,s • (z-R z)) ∈ (ordinaryFieldClosure f).graph}
  have hclosed : IsClosed S := (ordinaryFieldClosure_closed f).preimage P.continuous
  have hdense : Dense S := fieldHalfEmbedding_dense.mono (by
    rintro z ⟨v,rfl⟩
    exact hcore v)
  have heq : S = Set.univ := hclosed.closure_eq.symm.trans hdense.closure_eq
  exact (Set.eq_univ_iff_forall.mp heq) u

lemma fieldResolventPlus_graph (f : OneBoson) (u : Carrier) :
    (fieldResolventPlus f u,Complex.I • (u-fieldResolventPlus f u)) ∈ (ordinaryFieldClosure f).graph :=
  fieldResolvent_closed_extension f (fieldResolventPlus f) Complex.I (fun v => by
    rw [fieldResolventPlus_core]
    exact fieldLaplacePlus_graph f v) u

lemma fieldResolventMinus_graph (f : OneBoson) (u : Carrier) :
    (fieldResolventMinus f u,(-Complex.I) • (u-fieldResolventMinus f u)) ∈ (ordinaryFieldClosure f).graph :=
  fieldResolvent_closed_extension f (fieldResolventMinus f) (-Complex.I) (fun v => by
    rw [fieldResolventMinus_core]
    exact fieldLaplaceMinus_graph f v) u

lemma fieldClosure_graph_domain (f : OneBoson) {x y : Carrier} (h : (x,y) ∈ (ordinaryFieldClosure f).graph) :
    x ∈ (ordinaryFieldClosure f).domain := by
  obtain ⟨v,hv,_⟩ := (ordinaryFieldClosure f).mem_graph_iff.mp h
  exact (show v.val = x from hv) ▸ v.property

def fieldResolventPlusInput (f : OneBoson) (u : Carrier) : (ordinaryFieldClosure f).domain :=
  ⟨fieldResolventPlus f u,fieldClosure_graph_domain f (fieldResolventPlus_graph f u)⟩

def fieldResolventMinusInput (f : OneBoson) (u : Carrier) : (ordinaryFieldClosure f).domain :=
  ⟨fieldResolventMinus f u,fieldClosure_graph_domain f (fieldResolventMinus_graph f u)⟩

lemma fieldResolventPlus_action (f : OneBoson) (u : Carrier) :
    ordinaryFieldClosure f (fieldResolventPlusInput f u) = Complex.I • (u-fieldResolventPlus f u) :=
  (ordinaryFieldClosure f).mem_graph_snd_inj ((ordinaryFieldClosure f).mem_graph (fieldResolventPlusInput f u))
    (fieldResolventPlus_graph f u) rfl

lemma fieldResolventMinus_action (f : OneBoson) (u : Carrier) :
    ordinaryFieldClosure f (fieldResolventMinusInput f u) = (-Complex.I) • (u-fieldResolventMinus f u) :=
  (ordinaryFieldClosure f).mem_graph_snd_inj ((ordinaryFieldClosure f).mem_graph (fieldResolventMinusInput f u))
    (fieldResolventMinus_graph f u) rfl

lemma field_i_neg_one_i (w : Carrier) : Complex.I • ((-1:ℂ) • (Complex.I • w)) = w := by
  rw [smul_smul,smul_smul,mul_neg_one,neg_mul,field_i_square,neg_neg,one_smul]

set_option backward.isDefEq.respectTransparency.types false in
lemma ordinaryFieldClosure_selfadjoint (f : OneBoson) : IsSelfAdjointOperator (ordinaryFieldClosure f) := by
  apply GW.Operators.selfadjoint_of_imaginary_ranges (ordinaryFieldClosure f)
    (ordinaryFieldClosure_dense f) (ordinaryFieldClosure_symmetric f) (t := 1) zero_lt_one
  · intro w
    refine ⟨fieldResolventMinusInput f (Complex.I • w),?_⟩
    rw [GW.Operators.complexShift_apply,fieldResolventMinus_action]
    change (-Complex.I) • (Complex.I • w-fieldResolventMinus f (Complex.I • w))-
      ((1:ℂ)*Complex.I) • fieldResolventMinus f (Complex.I • w) = w
    simp only [one_mul,smul_sub,smul_smul,neg_mul,mul_neg,field_i_square,neg_neg,one_smul,neg_smul]
    abel
  · intro w
    refine ⟨fieldResolventPlusInput f ((-Complex.I) • w),?_⟩
    rw [GW.Operators.complexShift_apply,fieldResolventPlus_action]
    change Complex.I • ((-Complex.I) • w-fieldResolventPlus f ((-Complex.I) • w))-
      (-((1:ℂ)*Complex.I)) • fieldResolventPlus f ((-Complex.I) • w) = w
    simp only [one_mul,smul_sub,smul_smul,neg_mul,mul_neg,field_i_square,neg_neg,one_smul,neg_smul]
    abel_nf
    convert! field_i_neg_one_i w using 1 <;> simp only [neg_one_zsmul,neg_one_smul]



set_option backward.isDefEq.respectTransparency.types false in
lemma fieldPhase_inner_cancel (f : OneBoson) (t : ℝ) :
    ⟪f,t • (Complex.I • f)⟫_ℂ+⟪t • (Complex.I • f),f⟫_ℂ = 0 := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) t (Complex.I • f),smul_smul,
    inner_smul_right,inner_smul_left]
  have hconj : (starRingEnd ℂ) ((t:ℂ)*Complex.I) = -((t:ℂ)*Complex.I) := by simp
  have hz : ((t:ℂ)*Complex.I)*⟪f,f⟫_ℂ+(starRingEnd ℂ) ((t:ℂ)*Complex.I)*⟪f,f⟫_ℂ = 0 := by
    rw [hconj,neg_mul,add_neg_cancel]
  convert! hz using 1 <;> rfl

set_option backward.isDefEq.respectTransparency.types false in
lemma fieldCoherent_commutes (f g : OneBoson) (t : ℝ) :
    ordinaryField f (fieldWeylCoherentInput f (t • (Complex.I • f)) g) =
      weylUnitary (t • (Complex.I • f)) (ordinaryField f (coherentFieldInput f g)) := by
  have ha : ordinaryAnnihilationRootInput f (fieldWeylCoherentInput f (t • (Complex.I • f)) g) =
      weylCoherentAnnihilationInput (t • (Complex.I • f)) f g :=
    Subtype.ext (fieldWeylCoherentInput_value f _ g)
  have hc : ordinaryCreationRootInput f (fieldWeylCoherentInput f (t • (Complex.I • f)) g) =
      weylCoherentCreationInput (t • (Complex.I • f)) f g :=
    Subtype.ext (fieldWeylCoherentInput_value f _ g)
  rw [ordinaryField_action,ha,hc,weyl_annihilation_coherent_intertwine,weyl_creation_coherent_intertwine,
    ← map_add,coherentField_action]
  congr 1
  calc
    _ = ⟪f,g⟫_ℂ • exponentialVector g+coherentCreatorOne g f+
      (⟪f,t • (Complex.I • f)⟫_ℂ+⟪t • (Complex.I • f),f⟫_ℂ) • exponentialVector g := by module
    _ = _ := by rw [fieldPhase_inner_cancel,zero_smul,add_zero]

lemma ordinaryFieldHalfMap_coherent (f g : OneBoson) :
    ordinaryFieldHalfMap f (coherentExponentialWeighted (1/2) (by norm_num) g) =
      ordinaryField f (coherentFieldInput f g) := by
  change ordinaryField f (ordinaryFieldHalfInput f (coherentExponentialWeighted (1/2) (by norm_num) g)) = _
  congr 1
  apply Subtype.ext
  change numberDomainEmbedding (1/2) (by norm_num) (coherentExponentialWeighted (1/2) (by norm_num) g) = exponentialVector g
  rw [numberDomainEmbedding_apply,coherentExponentialWeighted_ambient]

lemma fieldOrbit_coherent_fieldInput (f g : OneBoson) (t : ℝ) :
    ordinaryFieldHalfInput f (fieldOrbit f t (coherentExponentialWeighted (1/2) (by norm_num) g)) =
      fieldWeylCoherentInput f (t • (Complex.I • f)) g := by
  apply Subtype.ext
  change fieldOrbitValue f t (coherentExponentialWeighted (1/2) (by norm_num) g) = _
  rw [fieldOrbitValue_apply,numberDomainEmbedding_apply,coherentExponentialWeighted_ambient,
    fieldWeylCoherentInput_value]

set_option backward.isDefEq.respectTransparency.types false in
lemma fieldOrbit_half_commutes (f : OneBoson) (t : ℝ) (u : NumberWeightedDomain Sector (1/2) (by norm_num)) :
    ordinaryFieldHalfMap f (fieldOrbit f t u) =
      weylUnitary (t • (Complex.I • f)) (ordinaryFieldHalfMap f u) := by
  let L := (ordinaryFieldHalfMap f).comp (fieldOrbit f t)
  let R := (weylUnitary (t • (Complex.I • f)) : Carrier →L[ℂ] Carrier).comp (ordinaryFieldHalfMap f)
  have hE (g : OneBoson) : L (coherentExponentialWeighted (1/2) (by norm_num) g) =
      R (coherentExponentialWeighted (1/2) (by norm_num) g) := by
    change ordinaryField f (ordinaryFieldHalfInput f
      (fieldOrbit f t (coherentExponentialWeighted (1/2) (by norm_num) g))) = _
    rw [fieldOrbit_coherent_fieldInput,fieldCoherent_commutes]
    change _ = weylUnitary (t • (Complex.I • f)) (ordinaryFieldHalfMap f (coherentExponentialWeighted (1/2) (by norm_num) g))
    rw [ordinaryFieldHalfMap_coherent]
  have hEq : Set.EqOn L R (numberHalfCore : Set (NumberWeightedDomain Sector (1/2) (by norm_num))) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g,rfl⟩ := hx
      exact hE g
    | zero => simp only [map_zero]
    | add x y hx hy ihx ihy => simp only [map_add,ihx,ihy]
    | smul a x hx ih => simp only [map_smul,ih]
  exact (hEq.closure L.continuous R.continuous) (numberHalfCore_dense u)


lemma fieldOrbit_half_commutation_graph (f : OneBoson) (t : ℝ)
    (u : NumberWeightedDomain Sector (1/2) (by norm_num)) :
    (weylUnitary (t • (Complex.I • f)) (numberDomainEmbedding (1/2) (by norm_num) u),
     weylUnitary (t • (Complex.I • f)) (ordinaryFieldHalfMap f u)) ∈ (ordinaryFieldClosure f).graph := by
  have hg := (LinearPMap.le_graph_of_le (ordinaryFieldClosure_extends f))
    (ordinaryFieldHalfMap_graph f (fieldOrbit f t u))
  change (fieldOrbitValue f t u,ordinaryFieldHalfMap f (fieldOrbit f t u)) ∈ (ordinaryFieldClosure f).graph at hg
  rw [fieldOrbitValue_apply,fieldOrbit_half_commutes] at hg
  exact hg

set_option backward.isDefEq.respectTransparency.types false in
lemma fieldWeylClosure_graph (f : OneBoson) (t : ℝ) (u : (ordinaryFieldClosure f).domain) :
    (weylUnitary (t • (Complex.I • f)) u.val,
     weylUnitary (t • (Complex.I • f)) (ordinaryFieldClosure f u)) ∈ (ordinaryFieldClosure f).graph := by
  let U : Carrier →L[ℂ] Carrier := weylUnitary (t • (Complex.I • f))
  let P := U.prodMap U
  let S : Set (Carrier × Carrier) := {p | (U p.1,U p.2) ∈ (ordinaryFieldClosure f).graph}
  have hclosed : IsClosed S := (ordinaryFieldClosure_closed f).preimage P.continuous
  have hsub : ((ordinaryField f).graph : Set (Carrier × Carrier)) ⊆ S := by
    intro p hp
    obtain ⟨w,hw⟩ := (ordinaryField f).mem_graph_iff'.mp hp
    rw [← hw]
    let v := numberHalfGraphInput w
    have heJ : numberDomainEmbedding (1/2) (by norm_num) v = w.val := numberHalfGraphInput_embedding w
    have heA : ordinaryFieldHalfMap f v = ordinaryField f w := by
      change ordinaryField f (ordinaryFieldHalfInput f v) = ordinaryField f w
      congr 1
      exact Subtype.ext heJ
    have hg := fieldOrbit_half_commutation_graph f t v
    rw [heJ,heA] at hg
    exact hg
  have hp : (u.val,ordinaryFieldClosure f u) ∈ closure ((ordinaryField f).graph : Set (Carrier × Carrier)) := by
    change (u.val,ordinaryFieldClosure f u) ∈ (ordinaryField f).graph.topologicalClosure
    rw [ordinaryFieldClosure_graph]
    exact (ordinaryFieldClosure f).mem_graph u
  exact closure_minimal hsub hclosed hp

def fieldWeylClosureInput (f : OneBoson) (t : ℝ) (u : (ordinaryFieldClosure f).domain) :
    (ordinaryFieldClosure f).domain :=
  ⟨weylUnitary (t • (Complex.I • f)) u.val,by
    obtain ⟨v,hv,_⟩ := (ordinaryFieldClosure f).mem_graph_iff.mp (fieldWeylClosure_graph f t u)
    exact (show v.val = weylUnitary (t • (Complex.I • f)) u.val from hv) ▸ v.property⟩

lemma fieldWeylClosure_action (f : OneBoson) (t : ℝ) (u : (ordinaryFieldClosure f).domain) :
    ordinaryFieldClosure f (fieldWeylClosureInput f t u) =
      weylUnitary (t • (Complex.I • f)) (ordinaryFieldClosure f u) :=
  (ordinaryFieldClosure f).mem_graph_snd_inj ((ordinaryFieldClosure f).mem_graph (fieldWeylClosureInput f t u))
    (fieldWeylClosure_graph f t u) rfl

lemma fieldWeylClosure_domain_iff (f : OneBoson) (t : ℝ) (u : Carrier) :
    weylUnitary (t • (Complex.I • f)) u ∈ (ordinaryFieldClosure f).domain ↔ u ∈ (ordinaryFieldClosure f).domain := by
  constructor
  · intro hu
    have hh := (fieldWeylClosureInput f (-t) ⟨weylUnitary (t • (Complex.I • f)) u,hu⟩).property
    change weylUnitary ((-t) • (Complex.I • f)) (weylUnitary (t • (Complex.I • f)) u) ∈ (ordinaryFieldClosure f).domain at hh
    rw [neg_smul,← weylUnitary_symm,LinearIsometryEquiv.symm_apply_apply] at hh
    exact hh
  · intro hu
    exact (fieldWeylClosureInput f t ⟨u,hu⟩).property

lemma fieldWeylClosure_domain_image (f : OneBoson) (t : ℝ) :
    (weylUnitary (t • (Complex.I • f))) '' ((ordinaryFieldClosure f).domain : Set Carrier) =
      ((ordinaryFieldClosure f).domain : Set Carrier) := by
  ext u
  constructor
  · rintro ⟨v,hv,rfl⟩
    exact (fieldWeylClosure_domain_iff f t v).mpr hv
  · intro hu
    refine ⟨weylUnitary ((-t) • (Complex.I • f)) u,(fieldWeylClosure_domain_iff f (-t) u).mpr hu,?_⟩
    rw [neg_smul,← weylUnitary_symm,LinearIsometryEquiv.apply_symm_apply]


set_option backward.isDefEq.respectTransparency.types false in
lemma fieldInitial_hasDerivAt (f : OneBoson) (u : (ordinaryField f).domain) (t : ℝ) :
    HasDerivAt (fun s : ℝ => weylUnitary (s • (Complex.I • f)) u.val)
      (Complex.I • weylUnitary (t • (Complex.I • f)) (ordinaryField f u)) t := by
  let v := numberHalfGraphInput u
  have heJ : numberDomainEmbedding (1/2) (by norm_num) v = u.val := numberHalfGraphInput_embedding u
  have heA : ordinaryFieldHalfMap f v = ordinaryField f u := by
    change ordinaryField f (ordinaryFieldHalfInput f v) = ordinaryField f u
    congr 1
    exact Subtype.ext heJ
  have hd := fieldOrbit_hasDerivAt f v t
  have hfun : (fun s : ℝ => fieldOrbitValue f s v) = fun s => weylUnitary (s • (Complex.I • f)) u.val := by
    funext s
    rw [fieldOrbitValue_apply,heJ]
  have heD : fieldOrbitDerivative f t v = Complex.I • weylUnitary (t • (Complex.I • f)) (ordinaryField f u) := by
    change Complex.I • ordinaryFieldHalfMap f (fieldOrbit f t v) = _
    rw [fieldOrbit_half_commutes,heA]
  rw [hfun,heD] at hd
  exact hd

lemma fieldInitial_graph_approximation (f : OneBoson) (u : (ordinaryFieldClosure f).domain) :
    ∃ v : ℕ → (ordinaryField f).domain,
      Tendsto (fun n => (v n).val) atTop (𝓝 u.val) ∧
      Tendsto (fun n => ordinaryField f (v n)) atTop (𝓝 (ordinaryFieldClosure f u)) := by
  have hm : (u.val,ordinaryFieldClosure f u) ∈ closure ((ordinaryField f).graph : Set (Carrier × Carrier)) := by
    change (u.val,ordinaryFieldClosure f u) ∈ (ordinaryField f).graph.topologicalClosure
    rw [ordinaryFieldClosure_graph]
    exact (ordinaryFieldClosure f).mem_graph u
  obtain ⟨p,hp,hlim⟩ := mem_closure_iff_seq_limit.mp hm
  choose v hvJ hvA using fun n => (ordinaryField f).mem_graph_iff.mp (hp n)
  refine ⟨v,?_,?_⟩
  · exact ((continuous_fst.tendsto (u.val,ordinaryFieldClosure f u)).comp hlim).congr'
      (Filter.Eventually.of_forall (fun n => (hvJ n).symm))
  · exact ((continuous_snd.tendsto (u.val,ordinaryFieldClosure f u)).comp hlim).congr'
      (Filter.Eventually.of_forall (fun n => (hvA n).symm))

lemma fieldWeylOrbit_continuous (f : OneBoson) (u : Carrier) :
    Continuous (fun t : ℝ => weylUnitary (t • (Complex.I • f)) u) := by
  have hc : Continuous (fun t : ℝ => t • (Complex.I • f)) := by fun_prop
  exact (weylUnitary_strong_continuous u).comp hc

lemma fieldWeylDerivative_distance (f : OneBoson) (t : ℝ) (u v : Carrier) :
    dist (Complex.I • weylUnitary (t • (Complex.I • f)) u)
      (Complex.I • weylUnitary (t • (Complex.I • f)) v) = dist u v := by
  rw [dist_eq_norm,← smul_sub,norm_smul,Complex.norm_I,one_mul,← dist_eq_norm]
  exact (weylUnitary (t • (Complex.I • f))).isometry.dist_eq u v

lemma fieldWeylDerivative_uniform (f : OneBoson) (v : ℕ → Carrier) (u : Carrier)
    (hu : Tendsto v atTop (𝓝 u)) (a b : ℝ) :
    TendstoUniformlyOn (fun n t => Complex.I • weylUnitary (t • (Complex.I • f)) (v n))
      (fun t => Complex.I • weylUnitary (t • (Complex.I • f)) u) atTop (uIcc a b) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.mp hu) ε hε] with n hn t ht
  rw [fieldWeylDerivative_distance,dist_comm]
  exact hn

set_option backward.isDefEq.respectTransparency.types false in
lemma fieldWeylClosure_hasDerivAt (f : OneBoson) (u : (ordinaryFieldClosure f).domain) (t : ℝ) :
    HasDerivAt (fun s : ℝ => weylUnitary (s • (Complex.I • f)) u.val)
      (Complex.I • ordinaryFieldClosure f (fieldWeylClosureInput f t u)) t := by
  rw [fieldWeylClosure_action]
  obtain ⟨v,hv,hAv⟩ := fieldInitial_graph_approximation f u
  have hr := GW.Analysis.uniformDerivativeLimit (F := Carrier) (J := Set.univ) isOpen_univ
    (t₀ := (0:ℝ)) (Set.mem_univ 0)
    (cN := fun n t => weylUnitary (t • (Complex.I • f)) (v n).val)
    (dN := fun n t => Complex.I • weylUnitary (t • (Complex.I • f)) (ordinaryField f (v n)))
    (d := fun t => Complex.I • weylUnitary (t • (Complex.I • f)) (ordinaryFieldClosure f u))
    (c₀ := weylUnitary ((0:ℝ) • (Complex.I • f)) u.val)
    (fun n t _ => fieldInitial_hasDerivAt f (v n) t)
    (fun n => ((fieldWeylOrbit_continuous f (ordinaryField f (v n))).fun_const_smul Complex.I).continuousOn)
    (((weylUnitary ((0:ℝ) • (Complex.I • f))).continuous.tendsto u.val).comp hv)
    (fun a b _ => fieldWeylDerivative_uniform f (fun n => ordinaryField f (v n)) (ordinaryFieldClosure f u) hAv a b)
  have hC : connectedComponentIn (Set.univ : Set ℝ) (0:ℝ) = Set.univ := by
    rw [connectedComponentIn_univ,PreconnectedSpace.connectedComponent_eq_univ]
  have he := hr.2.2.2.2.2 (fun s => weylUnitary (s • (Complex.I • f)) u.val)
    (fun s _ => ((weylUnitary (s • (Complex.I • f))).continuous.tendsto u.val).comp hv)
  have hfun : (fun s => weylUnitary (s • (Complex.I • f)) u.val) = GW.Analysis.integratedDerivative 0
      (weylUnitary ((0:ℝ) • (Complex.I • f)) u.val)
      (fun s => Complex.I • weylUnitary (s • (Complex.I • f)) (ordinaryFieldClosure f u)) := by
    funext s
    exact he (by simp only [hC,Set.mem_univ])
  rw [hfun]
  exact hr.2.2.1 t (by simp only [hC,Set.mem_univ])


def ordinaryMomentumFieldClosure (h : OneBoson) : Carrier →ₗ.[ℂ] Carrier := ordinaryFieldClosure (Complex.I • h)

lemma ordinaryMomentumFieldClosure_eq (h : OneBoson) :
    ordinaryMomentumFieldClosure h = (ordinaryMomentumField h).closure := rfl

lemma field_pi_phase (h : OneBoson) (t : ℝ) :
    (-t) • (Complex.I • (Complex.I • h)) = t • h := by
  have hi : Complex.I • (Complex.I • h) = -h := by
    rw [smul_smul,← pow_two,Complex.I_sq,neg_one_smul]
  rw [hi,smul_neg,neg_smul,neg_neg]

def momentumWeylClosureInput (h : OneBoson) (t : ℝ) (u : (ordinaryMomentumFieldClosure h).domain) :
    (ordinaryMomentumFieldClosure h).domain := fieldWeylClosureInput (Complex.I • h) (-t) u

lemma momentumWeylClosureInput_value (h : OneBoson) (t : ℝ) (u : (ordinaryMomentumFieldClosure h).domain) :
    (momentumWeylClosureInput h t u).val = weylUnitary (t • h) u.val := by
  change weylUnitary ((-t) • (Complex.I • (Complex.I • h))) u.val = _
  rw [field_pi_phase]

lemma momentumWeylClosure_domain_iff (h : OneBoson) (t : ℝ) (u : Carrier) :
    weylUnitary (t • h) u ∈ (ordinaryMomentumFieldClosure h).domain ↔ u ∈ (ordinaryMomentumFieldClosure h).domain := by
  have hh := fieldWeylClosure_domain_iff (Complex.I • h) (-t) u
  rw [field_pi_phase] at hh
  exact hh

set_option backward.isDefEq.respectTransparency.types false in
lemma momentumWeylClosure_hasDerivAt (h : OneBoson) (u : (ordinaryMomentumFieldClosure h).domain) (t : ℝ) :
    HasDerivAt (fun s : ℝ => weylUnitary (s • h) u.val)
      ((-Complex.I) • ordinaryMomentumFieldClosure h (momentumWeylClosureInput h t u)) t := by
  have hd := (fieldWeylClosure_hasDerivAt (Complex.I • h) u (-t)).scomp t (hasDerivAt_id t).neg
  simp only [Function.comp_def,id_eq,field_pi_phase,neg_one_smul] at hd
  convert! hd using 1
  rw [neg_smul]
  rfl


lemma ordinaryField_essentially_selfadjoint (f : OneBoson) : IsSelfAdjointOperator (ordinaryField f).closure :=
  ordinaryFieldClosure_selfadjoint f

lemma ordinaryMomentumFieldClosure_selfadjoint (h : OneBoson) :
    IsSelfAdjointOperator (ordinaryMomentumFieldClosure h) := ordinaryFieldClosure_selfadjoint (Complex.I • h)

lemma fieldWeylClosureInput_value (f : OneBoson) (t : ℝ) (u : (ordinaryFieldClosure f).domain) :
    (fieldWeylClosureInput f t u).val = weylUnitary (t • (Complex.I • f)) u.val := rfl

set_option backward.isDefEq.respectTransparency.types false in
lemma fieldWeyl_phase_argument (f : OneBoson) (t : ℝ) :
    t • (Complex.I • f) = (Complex.I*(t:ℂ)) • f := by
  calc
    _ = ((t:ℂ)*Complex.I) • f := by
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ),smul_smul]
      rfl
    _ = _ := congrArg (fun c : ℂ => c • f) (mul_comm (t:ℂ) Complex.I)

set_option backward.isDefEq.respectTransparency.types false in
lemma fieldWeylClosure_hasDerivAt_complex_phase (f : OneBoson) (u : (ordinaryFieldClosure f).domain) (t : ℝ) :
    HasDerivAt (fun s : ℝ => weylUnitary ((Complex.I*(s:ℂ)) • f) u.val)
      (Complex.I • ordinaryFieldClosure f (fieldWeylClosureInput f t u)) t := by
  have hd := fieldWeylClosure_hasDerivAt f u t
  simpa only [fieldWeyl_phase_argument] using hd

end GW.Fock
