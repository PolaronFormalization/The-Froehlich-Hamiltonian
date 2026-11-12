module
public import GW.Fock.FockWeyl
public import GW.Fock.FockCcr
public import GW.Operators.BasicInterpolation
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal
namespace GW.Fock

def weylCoherentAnnihilationInput (f h g : OneBoson) : (ordinaryAnnihilation h).domain :=
  ⟨weylUnitary f (exponentialVector g),by
    rw [weylUnitary_exponential]
    exact (ordinaryAnnihilation h).domain.smul_mem (weylCoefficient f g)
      (ordinaryAnnihilationAllInput h (coherentExponentialAll (g+f))).property⟩

lemma weylCoherentAnnihilationInput_eq (f h g : OneBoson) :
    weylCoherentAnnihilationInput f h g = weylCoefficient f g •
      ordinaryAnnihilationAllInput h (coherentExponentialAll (g+f)) :=
  Subtype.ext (weylUnitary_exponential f g)

lemma weyl_annihilation_coherent_intertwine (f h g : OneBoson) :
    ordinaryAnnihilation h (weylCoherentAnnihilationInput f h g) =
      weylUnitary f ((⟪h,g⟫_ℂ+⟪h,f⟫_ℂ) • exponentialVector g) := by
  calc
    _ = ordinaryAnnihilation h (weylCoefficient f g •
        ordinaryAnnihilationAllInput h (coherentExponentialAll (g+f))) :=
      congrArg (ordinaryAnnihilation h) (weylCoherentAnnihilationInput_eq f h g)
    _ = weylCoefficient f g • ordinaryAnnihilation h
        (ordinaryAnnihilationAllInput h (coherentExponentialAll (g+f))) :=
      (ordinaryAnnihilation h).toFun.map_smul _ _
    _ = weylCoefficient f g • (⟪h,g+f⟫_ℂ • exponentialVector (g+f)) := by
      rw [exponentialVector_annihilation]
    _ = _ := by
      rw [map_smul,weylUnitary_exponential,inner_add_right,smul_smul,smul_smul,mul_comm]

lemma weyl_annihilation_coherent_conjugation (f h g : OneBoson) :
    (weylUnitary f).symm (ordinaryAnnihilation h (weylCoherentAnnihilationInput f h g)) =
      ordinaryAnnihilation h (ordinaryAnnihilationAllInput h (coherentExponentialAll g)) +
        ⟪h,f⟫_ℂ • exponentialVector g := by
  rw [weyl_annihilation_coherent_intertwine,LinearIsometryEquiv.symm_apply_apply,
    exponentialVector_annihilation,add_smul]


def numberZeroGraphMap : NumberWeightedDomain Sector 0 (by norm_num) →L[ℂ] Carrier :=
  (numberDomainIsometry Sector 0 (by norm_num)).toLinearIsometry.toContinuousLinearMap

set_option backward.isDefEq.respectTransparency.types false in
lemma numberZeroGraphMap_apply (u : NumberWeightedDomain Sector 0 (by norm_num)) :
    numberZeroGraphMap u = (numberWeightedGraph Sector 0 (by norm_num)).domain.subtype u := by
  apply lp.ext
  funext n
  change scalarDiagonal Sector (fun j => ((j:ℝ)+1)^0) _ n = _
  rw [scalarDiagonal_apply,Real.rpow_zero,Complex.ofReal_one,one_smul]
  rfl

def coherentCreatorOne (g h : OneBoson) : Carrier :=
  ordinaryCreation h (ordinaryCreationAllInput h (coherentExponentialAll g))

def coherentCreatorOneLinear (g : OneBoson) : OneBoson →L[ℂ] Carrier :=
  numberZeroGraphMap.comp (continuousMultilinearCurryFin1 ℂ OneBoson
    (NumberWeightedDomain Sector 0 (by norm_num)) (coherentJet 1 0 (by norm_num) g))

lemma coherentCreatorOneLinear_apply (g h : OneBoson) :
    coherentCreatorOneLinear g h = coherentCreatorOne g h := by
  rw [coherentCreatorOneLinear,ContinuousLinearMap.comp_apply,continuousMultilinearCurryFin1_apply,
    numberZeroGraphMap_apply,coherentJet_creator_product]
  rfl

lemma exponentialVector_hasFDerivAt_creator (g : OneBoson) :
    HasFDerivAt exponentialVector (coherentCreatorOneLinear g) g := by
  have hE := (coherentExponentialWeighted_hasFTaylorSeries 0 (by norm_num)).hasFDerivAt (by simp) g
  have h := numberZeroGraphMap.hasFDerivAt.comp g hE
  change HasFDerivAt (fun z => numberZeroGraphMap (coherentExponentialWeighted 0 (by norm_num) z))
    (coherentCreatorOneLinear g) g at h
  have he : (fun z => numberZeroGraphMap (coherentExponentialWeighted 0 (by norm_num) z)) =
      exponentialVector := by
    funext z
    rw [numberZeroGraphMap_apply,coherentExponentialWeighted_ambient]
  rwa [he] at h


def weylCoefficientDerivative (f g : OneBoson) : OneBoson →L[ℂ] ℂ :=
  weylCoefficient f g • -(innerSL ℂ f)

set_option backward.isDefEq.respectTransparency.types false in
lemma weylCoefficient_hasFDerivAt (f g : OneBoson) :
    HasFDerivAt (weylCoefficient f) (weylCoefficientDerivative f g) g := by
  have hc := ((hasFDerivAt_const (-((‖f‖^2:ℝ):ℂ)/2) g).fun_sub (innerSL ℂ f).hasFDerivAt).cexp
  simp only [zero_sub] at hc
  convert! hc using 1 <;> rfl

set_option backward.isDefEq.respectTransparency.types false in
lemma weyl_creation_coherent_derivative (f g h : OneBoson) :
    weylUnitary f (coherentCreatorOne g h) =
      weylCoefficient f g • coherentCreatorOne (g+f) h +
        (weylCoefficient f g * (-⟪f,h⟫_ℂ)) • exponentialVector (g+f) := by
  have hl := (weylUnitary f : Carrier →L[ℂ] Carrier).hasFDerivAt.comp g
    (exponentialVector_hasFDerivAt_creator g)
  change HasFDerivAt (fun z => weylUnitary f (exponentialVector z))
    ((weylUnitary f : Carrier →L[ℂ] Carrier).comp (coherentCreatorOneLinear g)) g at hl
  have hE : HasFDerivAt (fun z : OneBoson => exponentialVector (z+f))
      (coherentCreatorOneLinear (g+f)) g := by
    have ht := (exponentialVector_hasFDerivAt_creator (g+f)).comp g ((hasFDerivAt_id g).add_const f)
    simp only [ContinuousLinearMap.comp_id] at ht
    convert! ht using 1 <;> rfl
  have hr := (weylCoefficient_hasFDerivAt f g).fun_smul hE
  have he : (fun z => weylUnitary f (exponentialVector z)) =
      fun z => weylCoefficient f z • exponentialVector (z+f) := funext (weylUnitary_exponential f)
  rw [he] at hl
  have hh := congrArg (fun T : OneBoson →L[ℂ] Carrier => T h) (hl.unique hr)
  simpa [weylCoefficientDerivative,coherentCreatorOneLinear_apply] using hh


def weylCoherentCreationInput (f h g : OneBoson) : (ordinaryCreation h).domain :=
  ⟨weylUnitary f (exponentialVector g),by
    rw [weylUnitary_exponential]
    exact (ordinaryCreation h).domain.smul_mem (weylCoefficient f g)
      (ordinaryCreationAllInput h (coherentExponentialAll (g+f))).property⟩

lemma weylCoherentCreationInput_eq (f h g : OneBoson) :
    weylCoherentCreationInput f h g = weylCoefficient f g •
      ordinaryCreationAllInput h (coherentExponentialAll (g+f)) :=
  Subtype.ext (weylUnitary_exponential f g)

lemma weylCoherentCreation_action (f h g : OneBoson) :
    ordinaryCreation h (weylCoherentCreationInput f h g) =
      weylCoefficient f g • coherentCreatorOne (g+f) h := by
  calc
    _ = ordinaryCreation h (weylCoefficient f g •
        ordinaryCreationAllInput h (coherentExponentialAll (g+f))) :=
      congrArg (ordinaryCreation h) (weylCoherentCreationInput_eq f h g)
    _ = _ := (ordinaryCreation h).toFun.map_smul _ _

lemma weyl_creation_coherent_intertwine (f h g : OneBoson) :
    ordinaryCreation h (weylCoherentCreationInput f h g) =
      weylUnitary f (coherentCreatorOne g h + ⟪f,h⟫_ℂ • exponentialVector g) := by
  rw [weylCoherentCreation_action,map_add,map_smul,weyl_creation_coherent_derivative,
    weylUnitary_exponential,smul_smul,add_assoc,← add_smul]
  have hs : weylCoefficient f g * (-⟪f,h⟫_ℂ) + ⟪f,h⟫_ℂ * weylCoefficient f g = 0 := by ring
  rw [hs,zero_smul,add_zero]

lemma weyl_creation_coherent_conjugation (f h g : OneBoson) :
    (weylUnitary f).symm (ordinaryCreation h (weylCoherentCreationInput f h g)) =
      coherentCreatorOne g h + ⟪f,h⟫_ℂ • exponentialVector g := by
  rw [weyl_creation_coherent_intertwine,LinearIsometryEquiv.symm_apply_apply]

lemma coherentNumber_graph (g : OneBoson) :
    (exponentialVector g,coherentCreatorOne g g) ∈ numberOperator.graph := by
  have h := (numberPower Sector 1).mem_graph (exponentialNumberInput g)
  change (exponentialVector g,numberPower Sector 1 (exponentialNumberInput g)) ∈ (numberPower Sector 1).graph at h
  rw [exponentialVector_number,numberPower_one] at h
  exact h

def coherentNumberInput (g : OneBoson) : numberOperator.domain :=
  ⟨exponentialVector g,by
    have h := (exponentialNumberInput g).property
    change exponentialVector g ∈ (numberPower Sector 1).domain at h
    rw [numberPower_one] at h
    exact h⟩

lemma coherentNumber_action (g : OneBoson) : numberOperator (coherentNumberInput g) = coherentCreatorOne g g :=
  numberOperator.mem_graph_snd_inj (numberOperator.mem_graph (coherentNumberInput g)) (coherentNumber_graph g) rfl

def weylCoherentNumberInput (f g : OneBoson) : numberOperator.domain :=
  ⟨weylUnitary f (exponentialVector g),by
    rw [weylUnitary_exponential]
    exact numberOperator.domain.smul_mem (weylCoefficient f g) (coherentNumberInput (g+f)).property⟩

lemma weylCoherentNumberInput_eq (f g : OneBoson) :
    weylCoherentNumberInput f g = weylCoefficient f g • coherentNumberInput (g+f) :=
  Subtype.ext (weylUnitary_exponential f g)

lemma weylCoherentNumber_action (f g : OneBoson) :
    numberOperator (weylCoherentNumberInput f g) = weylCoefficient f g • coherentCreatorOne (g+f) (g+f) := by
  calc
    _ = numberOperator (weylCoefficient f g • coherentNumberInput (g+f)) :=
      congrArg numberOperator (weylCoherentNumberInput_eq f g)
    _ = weylCoefficient f g • numberOperator (coherentNumberInput (g+f)) := numberOperator.toFun.map_smul _ _
    _ = _ := by rw [coherentNumber_action]

lemma coherentCreatorOne_add (g h k : OneBoson) :
    coherentCreatorOne g (h+k) = coherentCreatorOne g h + coherentCreatorOne g k := by
  rw [← coherentCreatorOneLinear_apply,← coherentCreatorOneLinear_apply,← coherentCreatorOneLinear_apply,map_add]

def coherentFieldInput (f g : OneBoson) : (ordinaryField f).domain :=
  ordinaryShiftedToField f ⟨exponentialVector g,coherentJet_exponential_weighted (1/2) (by norm_num) g⟩

lemma coherentField_action (f g : OneBoson) :
    ordinaryField f (coherentFieldInput f g) = ⟪f,g⟫_ℂ • exponentialVector g + coherentCreatorOne g f := by
  rw [ordinaryField_action]
  have ha : ordinaryAnnihilationRootInput f (coherentFieldInput f g) =
      ordinaryAnnihilationAllInput f (coherentExponentialAll g) := Subtype.ext rfl
  have hc : ordinaryCreationRootInput f (coherentFieldInput f g) =
      ordinaryCreationAllInput f (coherentExponentialAll g) := Subtype.ext rfl
  rw [ha,hc,exponentialVector_annihilation]
  rfl

lemma weyl_number_coherent_conjugation (f g : OneBoson) :
    (weylUnitary f).symm (numberOperator (weylCoherentNumberInput f g)) =
      numberOperator (coherentNumberInput g) + ordinaryField f (coherentFieldInput f g) +
        ((‖f‖^2:ℝ):ℂ) • exponentialVector g := by
  have he : numberOperator (weylCoherentNumberInput f g) =
      ordinaryCreation (g+f) (weylCoherentCreationInput f (g+f) g) := by
    rw [weylCoherentNumber_action,weylCoherentCreation_action]
  have hf : ⟪f,f⟫_ℂ = ((‖f‖^2:ℝ):ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    exact (RCLike.ofReal_pow (K := ℂ) ‖f‖ 2).symm
  rw [he,weyl_creation_coherent_conjugation,coherentCreatorOne_add,inner_add_right,hf,
    coherentNumber_action,coherentField_action,add_smul]
  abel


def numberConjugationLowerInput (a b : ℝ) (hab : a ≤ b) (u : (shiftedNumberPower Sector b).domain) :
    (shiftedNumberPower Sector a).domain :=
  ⟨u.val,shiftedNumberDomain_mono (G := Sector) hab u.property⟩

set_option backward.isDefEq.respectTransparency.types false in
lemma shiftedNumberPower_norm_mono (a b : ℝ) (hab : a ≤ b) (u : (shiftedNumberPower Sector b).domain) :
    ‖shiftedNumberPower Sector a (numberConjugationLowerInput a b hab u)‖ ≤ ‖shiftedNumberPower Sector b u‖ := by
  apply lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0)
  intro n
  rw [shiftedNumberPower_apply,shiftedNumberPower_apply,norm_smul,norm_smul,
    Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ (n:ℝ)+1) a),
    abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ (n:ℝ)+1) b)]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith) hab)
    (norm_nonneg _)

def numberConjugationFieldInput (f : OneBoson) (u : NumberWeightedDomain Sector 1 zero_le_one) :
    (ordinaryField f).domain :=
  ordinaryShiftedToField f (numberConjugationLowerInput (1/2) 1 (by norm_num) u)

lemma numberConjugation_field_norm (f : OneBoson) (u : NumberWeightedDomain Sector 1 zero_le_one) :
    ‖ordinaryField f (numberConjugationFieldInput f u)‖ ≤ (2*‖f‖)*‖u‖ := by
  let v := numberConjugationLowerInput (1/2) 1 (by norm_num) (show (shiftedNumberPower Sector 1).domain from u)
  let w : (numberPower Sector (1/2)).domain := numberConjugationFieldInput f u
  have hC : ‖ordinaryCreation f (ordinaryCreationRootInput f w)‖ ≤ ‖f‖*‖shiftedNumberPower Sector (1/2) v‖ := by
    have h := creation_root_norm ordinarySectorKernel (ordinaryKernel f) v
    rw [ordinaryKernel_opNorm] at h
    exact h
  have hA : ‖ordinaryAnnihilation f (ordinaryAnnihilationRootInput f w)‖ ≤ ‖f‖*‖numberPower Sector (1/2) w‖ := by
    have h := annihilation_root_norm ordinarySectorKernel (ordinaryKernel f) w
    rw [ordinaryKernel_opNorm] at h
    exact h
  have hN : ‖numberPower Sector (1/2) w‖ ≤ ‖shiftedNumberPower Sector (1/2) v‖ := by
    have h := numberPower_graph_lower Sector (1/2) (by norm_num) w
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    exact (add_le_add_iff_left (‖(w:Carrier)‖^2)).mp h
  have hroot : ‖shiftedNumberPower Sector (1/2) v‖ ≤ ‖u‖ :=
    shiftedNumberPower_norm_mono (1/2) 1 (by norm_num) u
  calc
    _ = ‖ordinaryAnnihilation f (ordinaryAnnihilationRootInput f w) +
      ordinaryCreation f (ordinaryCreationRootInput f w)‖ := rfl
    _ ≤ ‖ordinaryAnnihilation f (ordinaryAnnihilationRootInput f w)‖+
      ‖ordinaryCreation f (ordinaryCreationRootInput f w)‖ := norm_add_le _ _
    _ ≤ ‖f‖*‖shiftedNumberPower Sector (1/2) v‖+‖f‖*‖shiftedNumberPower Sector (1/2) v‖ :=
      add_le_add (hA.trans (mul_le_mul_of_nonneg_left hN (norm_nonneg _))) hC
    _ = (2*‖f‖)*‖shiftedNumberPower Sector (1/2) v‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hroot (mul_nonneg (by norm_num) (norm_nonneg _))


def numberDomainEmbedding (r : ℝ) (hr : 0 ≤ r) : NumberWeightedDomain Sector r hr →L[ℂ] Carrier :=
  (numberWeightedGraph Sector r hr).embedding.comp
    (numberDomainIsometry Sector r hr).toLinearIsometry.toContinuousLinearMap

lemma numberDomainEmbedding_apply (r : ℝ) (hr : 0 ≤ r) (u : NumberWeightedDomain Sector r hr) :
    numberDomainEmbedding r hr u = (numberWeightedGraph Sector r hr).domain.subtype u :=
  GW.Spaces.weightedDomain_embedding (numberWeightedGraph Sector r hr) u

lemma numberDomainEmbedding_norm (r : ℝ) (hr : 0 ≤ r) (u : NumberWeightedDomain Sector r hr) :
    ‖numberDomainEmbedding r hr u‖ ≤ ‖u‖ := by
  change ‖(numberWeightedGraph Sector r hr).embedding (numberDomainIsometry Sector r hr u)‖ ≤ _
  calc
    _ ≤ ‖(numberWeightedGraph Sector r hr).embedding‖ * ‖numberDomainIsometry Sector r hr u‖ :=
      (numberWeightedGraph Sector r hr).embedding.le_opNorm _
    _ ≤ 1 * ‖numberDomainIsometry Sector r hr u‖ := mul_le_mul_of_nonneg_right
      (numberWeightedGraph Sector r hr).embedding_norm_le (norm_nonneg _)
    _ = _ := by rw [one_mul,LinearIsometryEquiv.norm_map]

def numberDomainProduct : NumberWeightedDomain Sector 1 zero_le_one →L[ℂ] Carrier :=
  (numberDomainIsometry Sector 1 zero_le_one).toLinearIsometry.toContinuousLinearMap

lemma numberDomainProduct_apply (u : NumberWeightedDomain Sector 1 zero_le_one) :
    numberDomainProduct u = shiftedNumberPower Sector 1 (show (shiftedNumberPower Sector 1).domain from u) := rfl

def numberDomainNumberInput (u : NumberWeightedDomain Sector 1 zero_le_one) : numberOperator.domain :=
  ⟨(show (shiftedNumberPower Sector 1).domain from u).val,
    ordinaryNumber_shiftedOne_domain.symm ▸ (show (shiftedNumberPower Sector 1).domain from u).property⟩

def numberDomainNumber : NumberWeightedDomain Sector 1 zero_le_one →L[ℂ] Carrier :=
  numberDomainProduct-numberDomainEmbedding 1 zero_le_one

set_option backward.isDefEq.respectTransparency.types false in
lemma numberDomainNumber_apply (u : NumberWeightedDomain Sector 1 zero_le_one) :
    numberDomainNumber u = numberOperator (numberDomainNumberInput u) := by
  rw [numberDomainNumber,ContinuousLinearMap.sub_apply,numberDomainProduct_apply,numberDomainEmbedding_apply]
  apply lp.ext
  funext n
  change shiftedNumberPower Sector 1 (show (shiftedNumberPower Sector 1).domain from u) n -
    (show (shiftedNumberPower Sector 1).domain from u).val n = numberOperator (numberDomainNumberInput u) n
  rw [shiftedNumberPower_apply,numberDiagonal_apply,Real.rpow_one]
  change (↑((n:ℝ)+1):ℂ) • (show (shiftedNumberPower Sector 1).domain from u).val n -
    (show (shiftedNumberPower Sector 1).domain from u).val n =
    (n:ℂ) • (show (shiftedNumberPower Sector 1).domain from u).val n
  push_cast
  module

def numberDomainFieldLinear (f : OneBoson) : NumberWeightedDomain Sector 1 zero_le_one →ₗ[ℂ] Carrier where
  toFun u := ordinaryField f (numberConjugationFieldInput f u)
  map_add' u v := by
    have he : numberConjugationFieldInput f (u+v) =
        numberConjugationFieldInput f u+numberConjugationFieldInput f v := Subtype.ext rfl
    rw [he]
    exact (ordinaryField f).toFun.map_add _ _
  map_smul' c u := by
    have he : numberConjugationFieldInput f (c • u) = c • numberConjugationFieldInput f u := Subtype.ext rfl
    rw [he]
    exact (ordinaryField f).toFun.map_smul _ _

def numberDomainField (f : OneBoson) : NumberWeightedDomain Sector 1 zero_le_one →L[ℂ] Carrier :=
  (numberDomainFieldLinear f).mkContinuous (2*‖f‖) (numberConjugation_field_norm f)

lemma numberDomainField_apply (f : OneBoson) (u : NumberWeightedDomain Sector 1 zero_le_one) :
    numberDomainField f u = ordinaryField f (numberConjugationFieldInput f u) := rfl

lemma numberDomainField_norm (f : OneBoson) (u : NumberWeightedDomain Sector 1 zero_le_one) :
    ‖numberDomainField f u‖ ≤ (2*‖f‖)*‖u‖ := numberConjugation_field_norm f u


lemma numberDomainEmbedding_coherent (g : OneBoson) :
    numberDomainEmbedding 1 zero_le_one (coherentExponentialWeighted 1 zero_le_one g) = exponentialVector g := by
  rw [numberDomainEmbedding_apply,coherentExponentialWeighted_ambient]

lemma numberDomainNumber_coherent (g : OneBoson) :
    numberDomainNumber (coherentExponentialWeighted 1 zero_le_one g) = numberOperator (coherentNumberInput g) := by
  rw [numberDomainNumber_apply]
  apply congrArg numberOperator
  exact Subtype.ext (coherentExponentialWeighted_ambient 1 zero_le_one g)

lemma numberDomainField_coherent (f g : OneBoson) :
    numberDomainField f (coherentExponentialWeighted 1 zero_le_one g) = ordinaryField f (coherentFieldInput f g) := by
  rw [numberDomainField_apply]
  apply congrArg (ordinaryField f)
  exact Subtype.ext (coherentExponentialWeighted_ambient 1 zero_le_one g)

def numberConjugationRhs (f : OneBoson) : NumberWeightedDomain Sector 1 zero_le_one →L[ℂ] Carrier :=
  (weylUnitary f : Carrier →L[ℂ] Carrier).comp
    (numberDomainNumber+numberDomainField f+((‖f‖^2:ℝ):ℂ) • numberDomainEmbedding 1 zero_le_one)

lemma numberConjugationRhs_coherent (f g : OneBoson) :
    numberConjugationRhs f (coherentExponentialWeighted 1 zero_le_one g) =
      weylUnitary f (numberOperator (coherentNumberInput g)+ordinaryField f (coherentFieldInput f g)+
        ((‖f‖^2:ℝ):ℂ) • exponentialVector g) := by
  rw [numberConjugationRhs,ContinuousLinearMap.comp_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    numberDomainNumber_coherent,numberDomainField_coherent,numberDomainEmbedding_coherent]
  rfl

lemma weyl_number_coherent_graph (f g : OneBoson) :
    (weylUnitary f (numberDomainEmbedding 1 zero_le_one (coherentExponentialWeighted 1 zero_le_one g)),
      numberConjugationRhs f (coherentExponentialWeighted 1 zero_le_one g)) ∈ numberOperator.graph := by
  rw [numberDomainEmbedding_coherent]
  have h := congrArg (weylUnitary f) (weyl_number_coherent_conjugation f g)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  have hv : numberOperator (weylCoherentNumberInput f g) =
      numberConjugationRhs f (coherentExponentialWeighted 1 zero_le_one g) :=
    h.trans (numberConjugationRhs_coherent f g).symm
  exact numberOperator.mem_graph_iff.mpr ⟨weylCoherentNumberInput f g,rfl,hv⟩

lemma weyl_number_graph_extension (f : OneBoson) (u : NumberWeightedDomain Sector 1 zero_le_one) :
    (weylUnitary f (numberDomainEmbedding 1 zero_le_one u),numberConjugationRhs f u) ∈ numberOperator.graph := by
  let U := (weylUnitary f : Carrier →L[ℂ] Carrier).comp (numberDomainEmbedding 1 zero_le_one)
  let L := numberConjugationRhs f
  let K := numberOperator.graph.comap (U.prod L).toLinearMap
  have hspan : Submodule.span ℂ (Set.range (coherentExponentialWeighted 1 zero_le_one)) ≤ K := by
    apply Submodule.span_le.mpr
    rintro x ⟨g,rfl⟩
    exact weyl_number_coherent_graph f g
  have hclosed : IsClosed (K : Set (NumberWeightedDomain Sector 1 zero_le_one)) := by
    exact (scalarDiagonal_closed Sector (fun n => (n:ℝ))).preimage (U.prod L).continuous
  have hdense : Dense (K : Set (NumberWeightedDomain Sector 1 zero_le_one)) := by
    have he := coherentExponentialWeighted_graph_total 1 zero_le_one (⊤ : Submodule ℂ OneBoson) (by simp)
    have hr : Set.range (fun g : (⊤ : Submodule ℂ OneBoson) => coherentExponentialWeighted 1 zero_le_one g) =
        Set.range (coherentExponentialWeighted 1 zero_le_one) := by
      ext x
      constructor
      · rintro ⟨g,rfl⟩; exact ⟨g,rfl⟩
      · rintro ⟨g,rfl⟩; exact ⟨⟨g,Submodule.mem_top⟩,rfl⟩
    rw [hr] at he
    exact he.mono hspan
  have heq : (K : Set (NumberWeightedDomain Sector 1 zero_le_one)) = Set.univ :=
    hclosed.closure_eq.symm.trans hdense.closure_eq
  have hu : u ∈ K := by change u ∈ (K : Set (NumberWeightedDomain Sector 1 zero_le_one)); rw [heq]; trivial
  exact hu


lemma numberConjugation_graph_mem {x y : Carrier} (h : (x,y) ∈ numberOperator.graph) : x ∈ numberOperator.domain := by
  obtain ⟨u,hu,hy⟩ := numberOperator.mem_graph_iff.mp h
  have he : u.val = x := hu
  exact he ▸ u.property

def weylNumberWeightedInput (f : OneBoson) (u : NumberWeightedDomain Sector 1 zero_le_one) :
    NumberWeightedDomain Sector 1 zero_le_one :=
  show (shiftedNumberPower Sector 1).domain from
  ⟨weylUnitary f (numberDomainEmbedding 1 zero_le_one u),by
    rw [← ordinaryNumber_shiftedOne_domain]
    exact numberConjugation_graph_mem (weyl_number_graph_extension f u)⟩

lemma weylNumberWeighted_number (f : OneBoson) (u : NumberWeightedDomain Sector 1 zero_le_one) :
    numberDomainNumber (weylNumberWeightedInput f u) = numberConjugationRhs f u := by
  rw [numberDomainNumber_apply]
  exact numberOperator.mem_graph_snd_inj
    (numberOperator.mem_graph (numberDomainNumberInput (weylNumberWeightedInput f u)))
    (weyl_number_graph_extension f u) rfl

lemma weylNumberWeighted_embedding (f : OneBoson) (u : NumberWeightedDomain Sector 1 zero_le_one) :
    numberDomainEmbedding 1 zero_le_one (weylNumberWeightedInput f u) =
      weylUnitary f (numberDomainEmbedding 1 zero_le_one u) := by
  rw [numberDomainEmbedding_apply]
  rfl

lemma weylNumberWeighted_product (f : OneBoson) (u : NumberWeightedDomain Sector 1 zero_le_one) :
    numberDomainProduct (weylNumberWeightedInput f u) =
      weylUnitary f (numberDomainProduct u+numberDomainField f u+
        ((‖f‖^2:ℝ):ℂ) • numberDomainEmbedding 1 zero_le_one u) := by
  have hp : numberDomainProduct (weylNumberWeightedInput f u) =
      numberDomainNumber (weylNumberWeightedInput f u)+
        numberDomainEmbedding 1 zero_le_one (weylNumberWeightedInput f u) := by
    rw [numberDomainNumber,ContinuousLinearMap.sub_apply]
    abel
  rw [hp,weylNumberWeighted_number,weylNumberWeighted_embedding]
  change weylUnitary f (numberDomainNumber u+numberDomainField f u+
    ((‖f‖^2:ℝ):ℂ) • numberDomainEmbedding 1 zero_le_one u)+
      weylUnitary f (numberDomainEmbedding 1 zero_le_one u) = _
  rw [← map_add]
  congr 1
  rw [numberDomainNumber,ContinuousLinearMap.sub_apply]
  abel

lemma weylNumberWeighted_norm (f : OneBoson) (u : NumberWeightedDomain Sector 1 zero_le_one) :
    ‖weylNumberWeightedInput f u‖ ≤ (1+‖f‖)^2*‖u‖ := by
  have hp : ‖numberDomainProduct u‖ = ‖u‖ := (numberDomainIsometry Sector 1 zero_le_one).norm_map u
  have hs : ‖((‖f‖^2:ℝ):ℂ) • numberDomainEmbedding 1 zero_le_one u‖ ≤ ‖f‖^2*‖u‖ := by
    rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left (numberDomainEmbedding_norm 1 zero_le_one u) (sq_nonneg _)
  change ‖numberDomainProduct (weylNumberWeightedInput f u)‖ ≤ _
  rw [weylNumberWeighted_product,LinearIsometryEquiv.norm_map]
  calc
    _ ≤ ‖numberDomainProduct u+numberDomainField f u‖+
      ‖((‖f‖^2:ℝ):ℂ) • numberDomainEmbedding 1 zero_le_one u‖ := norm_add_le _ _
    _ ≤ (‖numberDomainProduct u‖+‖numberDomainField f u‖)+
      ‖((‖f‖^2:ℝ):ℂ) • numberDomainEmbedding 1 zero_le_one u‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ (‖u‖+(2*‖f‖)*‖u‖)+‖f‖^2*‖u‖ :=
      add_le_add (add_le_add hp.le (numberDomainField_norm f u)) hs
    _ = _ := by ring

def numberConjugationGraphInput (u : numberOperator.domain) : NumberWeightedDomain Sector 1 zero_le_one :=
  show (shiftedNumberPower Sector 1).domain from ccrNumberInput u

lemma numberConjugationGraphInput_embedding (u : numberOperator.domain) :
    numberDomainEmbedding 1 zero_le_one (numberConjugationGraphInput u) = u.val := by
  rw [numberDomainEmbedding_apply]
  rfl

def weylNumberInput (f : OneBoson) (u : numberOperator.domain) : numberOperator.domain :=
  ⟨weylUnitary f u.val,by
    have h := weyl_number_graph_extension f (numberConjugationGraphInput u)
    rw [numberConjugationGraphInput_embedding] at h
    exact numberConjugation_graph_mem h⟩

lemma weylNumber_action (f : OneBoson) (u : numberOperator.domain) :
    numberOperator (weylNumberInput f u) = numberConjugationRhs f (numberConjugationGraphInput u) := by
  have h := weyl_number_graph_extension f (numberConjugationGraphInput u)
  rw [numberConjugationGraphInput_embedding] at h
  exact numberOperator.mem_graph_snd_inj (numberOperator.mem_graph (weylNumberInput f u)) h rfl

lemma weyl_number_conjugation (f : OneBoson) (u : numberOperator.domain) :
    (weylUnitary f).symm (numberOperator (weylNumberInput f u)) =
      numberOperator u+ordinaryField f (numberConjugationFieldInput f (numberConjugationGraphInput u))+
        ((‖f‖^2:ℝ):ℂ) • u.val := by
  rw [weylNumber_action]
  change (weylUnitary f).symm (weylUnitary f
    (numberDomainNumber (numberConjugationGraphInput u)+numberDomainField f (numberConjugationGraphInput u)+
      ((‖f‖^2:ℝ):ℂ) • numberDomainEmbedding 1 zero_le_one (numberConjugationGraphInput u))) = _
  rw [LinearIsometryEquiv.symm_apply_apply,numberDomainNumber_apply,numberDomainField_apply,
    numberConjugationGraphInput_embedding]
  rfl

lemma weyl_number_domain_iff (f : OneBoson) (u : Carrier) :
    weylUnitary f u ∈ numberOperator.domain ↔ u ∈ numberOperator.domain := by
  constructor
  · intro h
    have hh := (weylNumberInput (-f) ⟨weylUnitary f u,h⟩).property
    change weylUnitary (-f) (weylUnitary f u) ∈ numberOperator.domain at hh
    rw [← weylUnitary_symm,LinearIsometryEquiv.symm_apply_apply] at hh
    exact hh
  · intro h
    exact (weylNumberInput f ⟨u,h⟩).property

lemma weyl_number_domain_image (f : OneBoson) :
    (weylUnitary f) '' (numberOperator.domain : Set Carrier) = (numberOperator.domain : Set Carrier) := by
  ext u
  constructor
  · rintro ⟨v,hv,rfl⟩
    exact (weyl_number_domain_iff f v).mpr hv
  · intro hu
    refine ⟨weylUnitary (-f) u,(weyl_number_domain_iff (-f) u).mpr hu,?_⟩
    rw [← weylUnitary_symm,LinearIsometryEquiv.apply_symm_apply]


lemma number_half_energy (u : numberOperator.domain) (v : (numberPower Sector (1/2)).domain)
    (hv : v.val = u.val) :
    ‖numberPower Sector (1/2) v‖^2 = RCLike.re ⟪u.val,numberOperator u⟫_ℂ := by
  rw [numberPower_norm_sq Sector (1/2) (by norm_num),lp.inner_eq_tsum,
    RCLike.re_tsum ℂ (lp.summable_inner (𝕜 := ℂ) u.val (numberOperator u))]
  apply tsum_congr
  intro n
  rw [numberDiagonal_apply,inner_smul_right]
  have he : RCLike.re ((n:ℂ)*⟪u.val n,u.val n⟫_ℂ) = (n:ℝ)*‖u.val n‖^2 := by
    calc
      _ = RCLike.re (((n:ℝ):ℂ)*⟪u.val n,u.val n⟫_ℂ) := by push_cast; rfl
      _ = (n:ℝ)*RCLike.re ⟪u.val n,u.val n⟫_ℂ := RCLike.re_ofReal_mul (K := ℂ) _ _
      _ = _ := by rw [← norm_sq_eq_re_inner (𝕜 := ℂ)]
  rw [he,hv,← Real.sqrt_eq_rpow,Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)]


def numberConjugationHalfInput (u : numberOperator.domain) : (numberPower Sector (1/2)).domain :=
  ⟨u.val,by
    rw [numberPower_domain_eq Sector (1/2) (by norm_num)]
    exact (numberConjugationLowerInput (1/2) 1 (by norm_num) (ccrNumberInput u)).property⟩

lemma numberConjugation_field_energy (f : OneBoson) (u : numberOperator.domain) :
    RCLike.re ⟪u.val,ordinaryField f (numberConjugationFieldInput f (numberConjugationGraphInput u))⟫_ℂ =
      2*RCLike.re ⟪u.val,ordinaryAnnihilation f
        (ordinaryAnnihilationRootInput f (numberConjugationFieldInput f (numberConjugationGraphInput u)))⟫_ℂ := by
  let w := numberConjugationFieldInput f (numberConjugationGraphInput u)
  let a := ordinaryAnnihilation f (ordinaryAnnihilationRootInput f w)
  let c := ordinaryCreation f (ordinaryCreationRootInput f w)
  have hp : ⟪c,u.val⟫_ℂ = ⟪u.val,a⟫_ℂ := ccr_graph_pair_creation f u.val c u.val a
    ((ordinaryCreation f).mem_graph (ordinaryCreationRootInput f w))
    ((ordinaryAnnihilation f).mem_graph (ordinaryAnnihilationRootInput f w))
  have hr : RCLike.re ⟪u.val,c⟫_ℂ = RCLike.re ⟪u.val,a⟫_ℂ :=
    (inner_re_symm (𝕜 := ℂ) u.val c).trans (congrArg (fun z : ℂ => RCLike.re z) hp)
  change RCLike.re ⟪u.val,a+c⟫_ℂ = 2*RCLike.re ⟪u.val,a⟫_ℂ
  rw [inner_add_right,map_add,hr]
  ring

lemma weyl_half_square_on_number (f : OneBoson) (u : numberOperator.domain) :
    ‖numberPower Sector (1/2) (numberConjugationHalfInput (weylNumberInput f u))‖^2 =
      ‖numberPower Sector (1/2) (numberConjugationHalfInput u)‖^2+
      2*RCLike.re ⟪u.val,ordinaryAnnihilation f
        (ordinaryAnnihilationRootInput f (numberConjugationFieldInput f (numberConjugationGraphInput u)))⟫_ℂ+
      ‖f‖^2*‖u.val‖^2 := by
  rw [number_half_energy (weylNumberInput f u) _ rfl,number_half_energy u _ rfl]
  have hn := congrArg (weylUnitary f) (weyl_number_conjugation f u)
  rw [LinearIsometryEquiv.apply_symm_apply] at hn
  have hs : RCLike.re ⟪u.val,((‖f‖^2:ℝ):ℂ) • u.val⟫_ℂ = ‖f‖^2*‖u.val‖^2 := by
    rw [inner_smul_right]
    calc
      _ = ‖f‖^2*RCLike.re ⟪u.val,u.val⟫_ℂ := RCLike.re_ofReal_mul (K := ℂ) _ _
      _ = _ := by rw [← norm_sq_eq_re_inner (𝕜 := ℂ)]
  change RCLike.re ⟪weylUnitary f u.val,numberOperator (weylNumberInput f u)⟫_ℂ = _
  rw [hn,LinearIsometryEquiv.inner_map_map,inner_add_right,inner_add_right,map_add,map_add,
    numberConjugation_field_energy,hs]

lemma weyl_half_bound_on_number (f : OneBoson) (u : numberOperator.domain) :
    ‖numberPower Sector (1/2) (numberConjugationHalfInput (weylNumberInput f u))‖ ≤
      ‖numberPower Sector (1/2) (numberConjugationHalfInput u)‖+‖f‖*‖u.val‖ := by
  let w := numberConjugationFieldInput f (numberConjugationGraphInput u)
  let a := ordinaryAnnihilation f (ordinaryAnnihilationRootInput f w)
  have hA : ‖a‖ ≤ ‖f‖*‖numberPower Sector (1/2) (numberConjugationHalfInput u)‖ := by
    have h := annihilation_root_norm ordinarySectorKernel (ordinaryKernel f) w
    rw [ordinaryKernel_opNorm] at h
    exact h
  have hr : RCLike.re ⟪u.val,a⟫_ℂ ≤
      ‖u.val‖*(‖f‖*‖numberPower Sector (1/2) (numberConjugationHalfInput u)‖) :=
    (re_inner_le_norm (𝕜 := ℂ) _ _).trans (mul_le_mul_of_nonneg_left hA (norm_nonneg _))
  apply (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))).mp
  rw [weyl_half_square_on_number]
  change ‖numberPower Sector (1/2) (numberConjugationHalfInput u)‖^2+
    2*RCLike.re ⟪u.val,a⟫_ℂ+‖f‖^2*‖u.val‖^2 ≤ _
  nlinarith [hr]


def numberHalfWeightedInput (u : NumberWeightedDomain Sector (1/2) (by norm_num)) :
    (numberPower Sector (1/2)).domain :=
  ⟨numberDomainEmbedding (1/2) (by norm_num) u,by
    rw [numberDomainEmbedding_apply,numberPower_domain_eq Sector (1/2) (by norm_num)]
    exact (show (shiftedNumberPower Sector (1/2)).domain from u).property⟩

def numberHalfInputLinear : NumberWeightedDomain Sector (1/2) (by norm_num) →ₗ[ℂ]
    (numberPower Sector (1/2)).domain where
  toFun := numberHalfWeightedInput
  map_add' u v := Subtype.ext ((numberDomainEmbedding (1/2) (by norm_num)).map_add u v)
  map_smul' c u := Subtype.ext ((numberDomainEmbedding (1/2) (by norm_num)).map_smul c u)

def numberHalfLinear : NumberWeightedDomain Sector (1/2) (by norm_num) →ₗ[ℂ] Carrier :=
  (numberPower Sector (1/2)).toFun.comp numberHalfInputLinear

lemma numberHalfLinear_norm (u : NumberWeightedDomain Sector (1/2) (by norm_num)) :
    ‖numberHalfLinear u‖ ≤ ‖u‖ := by
  have h := numberPower_graph_lower Sector (1/2) (by norm_num) (numberHalfWeightedInput u)
  have he : shiftedNumberInput Sector (1/2) (by norm_num) (numberHalfWeightedInput u) =
      (show (shiftedNumberPower Sector (1/2)).domain from u) :=
    Subtype.ext (numberDomainEmbedding_apply (1/2) (by norm_num) u)
  rw [he] at h
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  exact (add_le_add_iff_left (‖(numberHalfWeightedInput u : Carrier)‖^2)).mp h

def numberHalfMap : NumberWeightedDomain Sector (1/2) (by norm_num) →L[ℂ] Carrier :=
  numberHalfLinear.mkContinuous 1 (fun u => by simpa only [one_mul] using numberHalfLinear_norm u)

lemma numberHalfMap_norm (u : NumberWeightedDomain Sector (1/2) (by norm_num)) :
    ‖numberHalfMap u‖ ≤ ‖u‖ := numberHalfLinear_norm u

def numberHalfCore : Submodule ℂ (NumberWeightedDomain Sector (1/2) (by norm_num)) :=
  Submodule.span ℂ (Set.range (fun g : (⊤ : Submodule ℂ OneBoson) =>
    coherentExponentialWeighted (1/2) (by norm_num) g))

lemma numberHalfCore_dense : Dense (numberHalfCore : Set (NumberWeightedDomain Sector (1/2) (by norm_num))) :=
  coherentExponentialWeighted_graph_total (1/2) (by norm_num) ⊤ (by simp)

lemma numberHalfCore_subtype_dense : DenseRange numberHalfCore.subtype := by
  change Dense (Set.range (Subtype.val : numberHalfCore → NumberWeightedDomain Sector (1/2) (by norm_num)))
  rw [Subtype.range_coe_subtype]
  exact numberHalfCore_dense

lemma numberHalfCore_mem (u : numberHalfCore) :
    numberDomainEmbedding (1/2) (by norm_num) u.val ∈ numberOperator.domain := by
  let K := numberOperator.domain.comap (numberDomainEmbedding (1/2) (by norm_num)).toLinearMap
  have hle : numberHalfCore ≤ K := by
    apply Submodule.span_le.mpr
    rintro x ⟨g,rfl⟩
    change numberDomainEmbedding (1/2) (by norm_num) (coherentExponentialWeighted (1/2) (by norm_num) g) ∈ numberOperator.domain
    rw [numberDomainEmbedding_apply,coherentExponentialWeighted_ambient]
    exact (coherentNumberInput g).property
  exact hle u.property

def numberHalfCoreInput (f : OneBoson) (u : numberHalfCore) : (numberPower Sector (1/2)).domain :=
  numberConjugationHalfInput (weylNumberInput f ⟨numberDomainEmbedding (1/2) (by norm_num) u.val,numberHalfCore_mem u⟩)

def numberHalfCoreInputLinear (f : OneBoson) : numberHalfCore →ₗ[ℂ] (numberPower Sector (1/2)).domain where
  toFun := numberHalfCoreInput f
  map_add' u v := by
    apply Subtype.ext
    change weylUnitary f (numberDomainEmbedding (1/2) (by norm_num) (u.val+v.val)) =
      weylUnitary f (numberDomainEmbedding (1/2) (by norm_num) u.val)+
        weylUnitary f (numberDomainEmbedding (1/2) (by norm_num) v.val)
    rw [map_add,map_add]
  map_smul' c u := by
    apply Subtype.ext
    change weylUnitary f (numberDomainEmbedding (1/2) (by norm_num) (c • u.val)) =
      c • weylUnitary f (numberDomainEmbedding (1/2) (by norm_num) u.val)
    rw [map_smul,map_smul]

def numberHalfCoreOutput (f : OneBoson) : numberHalfCore →ₗ[ℂ] Carrier :=
  (numberPower Sector (1/2)).toFun.comp (numberHalfCoreInputLinear f)

lemma numberHalfCore_sharp (f : OneBoson) (u : numberHalfCore) :
    ‖numberHalfCoreOutput f u‖ ≤ ‖numberHalfMap u.val‖+‖f‖*‖numberDomainEmbedding (1/2) (by norm_num) u.val‖ :=
  weyl_half_bound_on_number f ⟨numberDomainEmbedding (1/2) (by norm_num) u.val,numberHalfCore_mem u⟩

lemma numberHalfCore_bound (f : OneBoson) (u : numberHalfCore) :
    ‖numberHalfCoreOutput f u‖ ≤ (1+‖f‖)*‖u.val‖ := by
  calc
    _ ≤ ‖numberHalfMap u.val‖+‖f‖*‖numberDomainEmbedding (1/2) (by norm_num) u.val‖ := numberHalfCore_sharp f u
    _ ≤ ‖u.val‖+‖f‖*‖u.val‖ := add_le_add (numberHalfMap_norm u.val)
      (mul_le_mul_of_nonneg_left (numberDomainEmbedding_norm (1/2) (by norm_num) u.val) (norm_nonneg _))
    _ = _ := by ring

def numberHalfExtended (f : OneBoson) : NumberWeightedDomain Sector (1/2) (by norm_num) →L[ℂ] Carrier :=
  (numberHalfCoreOutput f).extendOfNorm numberHalfCore.subtype

lemma numberHalfExtended_core (f : OneBoson) (u : numberHalfCore) :
    numberHalfExtended f u.val = numberHalfCoreOutput f u :=
  LinearMap.extendOfNorm_eq numberHalfCore_subtype_dense ⟨1+‖f‖,numberHalfCore_bound f⟩ u

lemma numberHalfExtended_graph (f : OneBoson) (u : NumberWeightedDomain Sector (1/2) (by norm_num)) :
    (weylUnitary f (numberDomainEmbedding (1/2) (by norm_num) u),numberHalfExtended f u) ∈
      (numberPower Sector (1/2)).graph := by
  let U := (weylUnitary f : Carrier →L[ℂ] Carrier).comp (numberDomainEmbedding (1/2) (by norm_num))
  let L := numberHalfExtended f
  let K := (numberPower Sector (1/2)).graph.comap (U.prod L).toLinearMap
  have hle : numberHalfCore ≤ K := by
    intro x hx
    have he := numberHalfExtended_core f ⟨x,hx⟩
    change (weylUnitary f (numberDomainEmbedding (1/2) (by norm_num) x),numberHalfExtended f x) ∈ (numberPower Sector (1/2)).graph
    rw [he]
    exact (numberPower Sector (1/2)).mem_graph (numberHalfCoreInput f ⟨x,hx⟩)
  have hclosed : IsClosed (K : Set (NumberWeightedDomain Sector (1/2) (by norm_num))) :=
    (scalarDiagonal_closed Sector (numberPowerCoefficient (1/2))).preimage (U.prod L).continuous
  have hdense : Dense (K : Set (NumberWeightedDomain Sector (1/2) (by norm_num))) := numberHalfCore_dense.mono hle
  have heq : (K : Set (NumberWeightedDomain Sector (1/2) (by norm_num))) = Set.univ :=
    hclosed.closure_eq.symm.trans hdense.closure_eq
  have hu : u ∈ (K : Set _) := (Set.eq_univ_iff_forall.mp heq) u
  exact hu

lemma numberHalfExtended_sharp (f : OneBoson) (u : NumberWeightedDomain Sector (1/2) (by norm_num)) :
    ‖numberHalfExtended f u‖ ≤ ‖numberHalfMap u‖+‖f‖*‖numberDomainEmbedding (1/2) (by norm_num) u‖ := by
  let S : Set (NumberWeightedDomain Sector (1/2) (by norm_num)) :=
    {x | ‖numberHalfExtended f x‖ ≤ ‖numberHalfMap x‖+‖f‖*‖numberDomainEmbedding (1/2) (by norm_num) x‖}
  have hclosed : IsClosed S := isClosed_le (numberHalfExtended f).continuous.norm (by fun_prop)
  have hdense : Dense S := numberHalfCore_dense.mono (by
    intro x hx
    change ‖numberHalfExtended f x‖ ≤ _
    rw [numberHalfExtended_core f ⟨x,hx⟩]
    exact numberHalfCore_sharp f ⟨x,hx⟩)
  have heq : S = Set.univ := hclosed.closure_eq.symm.trans hdense.closure_eq
  exact show u ∈ S from heq.symm ▸ Set.mem_univ u


def numberHalfGraphInput (u : (numberPower Sector (1/2)).domain) :
    NumberWeightedDomain Sector (1/2) (by norm_num) :=
  shiftedNumberInput Sector (1/2) (by norm_num) u

lemma numberHalfGraphInput_embedding (u : (numberPower Sector (1/2)).domain) :
    numberDomainEmbedding (1/2) (by norm_num) (numberHalfGraphInput u) = u.val := by
  rw [numberDomainEmbedding_apply]
  rfl

lemma numberHalfGraphInput_value (u : (numberPower Sector (1/2)).domain) :
    numberHalfMap (numberHalfGraphInput u) = numberPower Sector (1/2) u := by
  change numberPower Sector (1/2) (numberHalfWeightedInput (numberHalfGraphInput u)) = _
  congr 1
  exact Subtype.ext (numberHalfGraphInput_embedding u)

def weylHalfInput (f : OneBoson) (u : (numberPower Sector (1/2)).domain) :
    (numberPower Sector (1/2)).domain :=
  ⟨weylUnitary f u.val,by
    have h := numberHalfExtended_graph f (numberHalfGraphInput u)
    rw [numberHalfGraphInput_embedding] at h
    obtain ⟨v,hv,_⟩ := (numberPower Sector (1/2)).mem_graph_iff.mp h
    exact (show v.val = weylUnitary f u.val from hv) ▸ v.property⟩

lemma weylHalf_action (f : OneBoson) (u : (numberPower Sector (1/2)).domain) :
    numberPower Sector (1/2) (weylHalfInput f u) = numberHalfExtended f (numberHalfGraphInput u) := by
  have h := numberHalfExtended_graph f (numberHalfGraphInput u)
  rw [numberHalfGraphInput_embedding] at h
  exact (numberPower Sector (1/2)).mem_graph_snd_inj
    ((numberPower Sector (1/2)).mem_graph (weylHalfInput f u)) h rfl

lemma weyl_half_bound (f : OneBoson) (u : (numberPower Sector (1/2)).domain) :
    ‖numberPower Sector (1/2) (weylHalfInput f u)‖ ≤
      ‖numberPower Sector (1/2) u‖+‖f‖*‖u.val‖ := by
  rw [weylHalf_action]
  have h := numberHalfExtended_sharp f (numberHalfGraphInput u)
  rw [numberHalfGraphInput_value,numberHalfGraphInput_embedding] at h
  exact h

lemma weyl_half_domain_iff (f : OneBoson) (u : Carrier) :
    weylUnitary f u ∈ (numberPower Sector (1/2)).domain ↔ u ∈ (numberPower Sector (1/2)).domain := by
  constructor
  · intro h
    have hh := (weylHalfInput (-f) ⟨weylUnitary f u,h⟩).property
    change weylUnitary (-f) (weylUnitary f u) ∈ (numberPower Sector (1/2)).domain at hh
    rw [← weylUnitary_symm,LinearIsometryEquiv.symm_apply_apply] at hh
    exact hh
  · intro h
    exact (weylHalfInput f ⟨u,h⟩).property

lemma weyl_half_domain_image (f : OneBoson) :
    (weylUnitary f) '' ((numberPower Sector (1/2)).domain : Set Carrier) =
      ((numberPower Sector (1/2)).domain : Set Carrier) := by
  ext u
  constructor
  · rintro ⟨v,hv,rfl⟩
    exact (weyl_half_domain_iff f v).mpr hv
  · intro hu
    refine ⟨weylUnitary (-f) u,(weyl_half_domain_iff (-f) u).mpr hu,?_⟩
    rw [← weylUnitary_symm,LinearIsometryEquiv.apply_symm_apply]


def pointL2Isometry (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    H →ₗᵢ[ℂ] Lp H 2 (Measure.dirac (() : Unit)) where
  toLinearMap := Lp.constₗ 2 (Measure.dirac (() : Unit)) ℂ
  norm_map' u := by
    change ‖Lp.const 2 (Measure.dirac (() : Unit)) u‖ = ‖u‖
    rw [Lp.norm_const' (p := 2) (μ := Measure.dirac (() : Unit)) (c := u) (by norm_num) (by norm_num)]
    simp [measureReal_def]

lemma pointL2Isometry_surjective (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    Function.Surjective (pointL2Isometry H) := by
  intro v
  refine ⟨v (),?_⟩
  apply Lp.ext
  filter_upwards [Lp.coeFn_const (p := 2) (μ := Measure.dirac (() : Unit)) (c := v ())] with x hx
  change (Lp.const 2 (Measure.dirac (() : Unit)) (v ())) x = v x
  have he : x = () := Subsingleton.elim _ _
  simpa only [he,Function.const_apply] using hx

def pointL2Unitary (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    H ≃ₗᵢ[ℂ] Lp H 2 (Measure.dirac (() : Unit)) :=
  LinearIsometryEquiv.ofSurjective (pointL2Isometry H) (pointL2Isometry_surjective H)

section Family
variable {E F : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℂ (E n)]
  [∀ n, NormedAddCommGroup (F n)] [∀ n, InnerProductSpace ℂ (F n)]

def lpFamilyEquiv (U : ∀ n, E n ≃ₗᵢ[ℂ] F n) : lp E 2 ≃ₗ[ℂ] lp F 2 where
  toFun u := ⟨fun n => U n (u n),by
    apply (GW.Analysis.memℓp_two_iff_sq _).mpr
    simpa only [LinearIsometryEquiv.norm_map] using (GW.Analysis.memℓp_two_iff_sq _).mp u.property⟩
  invFun v := ⟨fun n => (U n).symm (v n),by
    apply (GW.Analysis.memℓp_two_iff_sq _).mpr
    simpa only [LinearIsometryEquiv.norm_map] using (GW.Analysis.memℓp_two_iff_sq _).mp v.property⟩
  left_inv u := by
    apply lp.ext
    funext n
    exact (U n).symm_apply_apply (u n)
  right_inv v := by
    apply lp.ext
    funext n
    exact (U n).apply_symm_apply (v n)
  map_add' u v := by
    apply lp.ext
    funext n
    exact (U n).map_add (u n) (v n)
  map_smul' c u := by
    apply lp.ext
    funext n
    exact (U n).map_smul c (u n)

lemma lpFamilyEquiv_apply (U : ∀ n, E n ≃ₗᵢ[ℂ] F n) (u : lp E 2) (n : ℕ) :
    lpFamilyEquiv U u n = U n (u n) := rfl

def lpFamilyUnitary (U : ∀ n, E n ≃ₗᵢ[ℂ] F n) : lp E 2 ≃ₗᵢ[ℂ] lp F 2 where
  toLinearEquiv := lpFamilyEquiv U
  norm_map' u := by
    have hs : ‖lpFamilyEquiv U u‖^2 = ‖u‖^2 := by
      rw [GW.Analysis.lp_norm_sq,GW.Analysis.lp_norm_sq]
      apply tsum_congr
      intro n
      rw [lpFamilyEquiv_apply,LinearIsometryEquiv.norm_map]
    nlinarith [norm_nonneg (lpFamilyEquiv U u),norm_nonneg u]
end Family

def numberInterpolationUnitary : Carrier ≃ₗᵢ[ℂ]
    GW.Spaces.WeightSum (F := Sector) (fun _ : ℕ => Measure.dirac (() : Unit)) :=
  lpFamilyUnitary (fun n => pointL2Unitary (Sector n))


abbrev numberInterpolationMeasure (_n : ℕ) : Measure Unit := Measure.dirac ()

lemma numberInterpolationUnitary_apply (u : Carrier) (n : ℕ) :
    numberInterpolationUnitary u n = pointL2Unitary (Sector n) (u n) := rfl

lemma numberInterpolationUnitary_symm_apply (v : GW.Spaces.WeightSum (F := Sector) numberInterpolationMeasure) (n : ℕ) :
    numberInterpolationUnitary.symm v n = (pointL2Unitary (Sector n)).symm (v n) := rfl

lemma numberInterpolation_weighted_ae (a : ℕ → ℝ) (u : (scalarDiagonal Sector a).domain) (n : ℕ) :
    (fun x : Unit => (a n:ℂ) • numberInterpolationUnitary u.val n x) =ᵐ[numberInterpolationMeasure n]
      numberInterpolationUnitary (scalarDiagonal Sector a u) n := by
  have he : numberInterpolationUnitary (scalarDiagonal Sector a u) n =
      (a n:ℂ) • numberInterpolationUnitary u.val n := by
    rw [numberInterpolationUnitary_apply,numberInterpolationUnitary_apply,scalarDiagonal_apply]
    exact (pointL2Unitary (Sector n)).map_smul _ _
  rw [he]
  exact (Lp.coeFn_smul (a n:ℂ) (numberInterpolationUnitary u.val n)).symm

lemma numberInterpolation_domain_iff (a : ℕ → ℝ) (u : Carrier) :
    u ∈ (scalarDiagonal Sector a).domain ↔ numberInterpolationUnitary u ∈
      GW.Spaces.sumWeightDomain (F := Sector) numberInterpolationMeasure (fun (n : ℕ) (_ : Unit) => a n) := by
  constructor
  · intro hu
    exact ⟨numberInterpolationUnitary (scalarDiagonal Sector a ⟨u,hu⟩),
      fun n => numberInterpolation_weighted_ae a ⟨u,hu⟩ n⟩
  · rintro ⟨v,hv⟩
    have hc (n : ℕ) : v n = (a n:ℂ) • numberInterpolationUnitary u n := by
      apply Lp.ext
      filter_upwards [hv n,Lp.coeFn_smul (a n:ℂ) (numberInterpolationUnitary u n)] with x hx hs
      exact hx.symm.trans hs.symm
    have he (n : ℕ) : numberInterpolationUnitary.symm v n = (a n:ℂ) • u n := by
      rw [numberInterpolationUnitary_symm_apply,hc,numberInterpolationUnitary_apply,
        map_smul,LinearIsometryEquiv.symm_apply_apply]
    change Memℓp (fun n => (a n:ℂ) • u n) 2
    have hf : (fun n => (a n:ℂ) • u n) = fun n => numberInterpolationUnitary.symm v n :=
      funext (fun n => (he n).symm)
    rw [hf]
    exact (numberInterpolationUnitary.symm v).property

def numberInterpolationForward (a : ℕ → ℝ) (u : (scalarDiagonal Sector a).domain) :
    GW.Spaces.sumWeightDomain (F := Sector) numberInterpolationMeasure (fun (n : ℕ) (_ : Unit) => a n) :=
  ⟨numberInterpolationUnitary u.val,(numberInterpolation_domain_iff a u.val).mp u.property⟩

def numberInterpolationBackward (a : ℕ → ℝ)
    (v : GW.Spaces.sumWeightDomain (F := Sector) numberInterpolationMeasure (fun (n : ℕ) (_ : Unit) => a n)) :
    (scalarDiagonal Sector a).domain :=
  ⟨numberInterpolationUnitary.symm v.val,(numberInterpolation_domain_iff a _).mpr (by
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact v.property)⟩

lemma numberInterpolation_forward_backward (a : ℕ → ℝ)
    (v : GW.Spaces.sumWeightDomain (F := Sector) numberInterpolationMeasure (fun (n : ℕ) (_ : Unit) => a n)) :
    numberInterpolationForward a (numberInterpolationBackward a v) = v :=
  Subtype.ext (numberInterpolationUnitary.apply_symm_apply v.val)

lemma numberInterpolation_value (a : ℕ → ℝ) (u : (scalarDiagonal Sector a).domain) :
    GW.Spaces.sumWeightValue (F := Sector) numberInterpolationMeasure (numberInterpolationForward a u) =
      numberInterpolationUnitary (scalarDiagonal Sector a u) := by
  apply lp.ext
  funext n
  apply Lp.ext
  filter_upwards [GW.Spaces.sumWeightValue_ae (F := Sector) numberInterpolationMeasure (numberInterpolationForward a u) n,
    numberInterpolation_weighted_ae a u n] with x hv hx
  exact hv.symm.trans hx

lemma numberInterpolation_norm (a : ℕ → ℝ) (u : (scalarDiagonal Sector a).domain) :
    ‖GW.Spaces.sumWeightValue (F := Sector) numberInterpolationMeasure (numberInterpolationForward a u)‖ =
      ‖scalarDiagonal Sector a u‖ := by
  rw [numberInterpolation_value,LinearIsometryEquiv.norm_map]


set_option backward.isDefEq.respectTransparency.types false in
lemma number_scalar_interpolation (a : ℕ → ℝ) (ha : ∀ n, 1 ≤ a n)
    (T : Carrier →L[ℂ] Carrier) (M₀ M₁ : ℝ) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (hT₀ : ∀ z, ‖T z‖ ≤ M₀*‖z‖)
    (hT₁ : ∀ x : (scalarDiagonal Sector a).domain,
      ∃ h : T x.val ∈ (scalarDiagonal Sector a).domain,
        ‖scalarDiagonal Sector a ⟨T x.val,h⟩‖ ≤ M₁*‖scalarDiagonal Sector a x‖)
    (θ : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (u : Carrier)
    (hu : u ∈ (scalarDiagonal Sector (fun n => (a n)^θ)).domain) :
    ∃ h : T u ∈ (scalarDiagonal Sector (fun n => (a n)^θ)).domain,
      ‖scalarDiagonal Sector (fun n => (a n)^θ) ⟨T u,h⟩‖ ≤
        M₀^(1-θ)*M₁^θ*‖scalarDiagonal Sector (fun n => (a n)^θ) ⟨u,hu⟩‖ := by
  let μ := numberInterpolationMeasure
  let w : ∀ n : ℕ, Unit → ℝ := fun n _ => a n
  have hEnd (v : GW.Spaces.sumWeightDomain (F := Sector) μ w) :
      ∃ b : GW.Spaces.sumWeightDomain (F := Sector) μ w,
        b.val = numberInterpolationUnitary (T (numberInterpolationUnitary.symm v.val)) ∧
        ‖GW.Spaces.sumWeightValue (F := Sector) μ b‖ ≤ M₁*‖GW.Spaces.sumWeightValue (F := Sector) μ v‖ := by
    let x := numberInterpolationBackward a v
    obtain ⟨hx,hbound⟩ := hT₁ x
    let y : (scalarDiagonal Sector a).domain := ⟨T x.val,hx⟩
    refine ⟨numberInterpolationForward a y,rfl,?_⟩
    rw [numberInterpolation_norm]
    have hn := numberInterpolation_norm a x
    rw [show numberInterpolationForward a x = v from numberInterpolation_forward_backward a v] at hn
    exact hbound.trans_eq (congrArg (fun r : ℝ => M₁*r) hn.symm)
  have hz : numberInterpolationUnitary u ∈
      GW.Spaces.sumWeightDomain (F := Sector) μ (fun n x => (w n x)^θ) :=
    (numberInterpolation_domain_iff (fun n => (a n)^θ) u).mp hu
  obtain ⟨b,hb,hbound⟩ := GW.Operators.sumWeightedInterpolation_unitary μ μ w w
    (fun _ => measurable_const) (fun _ => measurable_const) (fun n _ => ha n) (fun n _ => ha n)
    numberInterpolationUnitary numberInterpolationUnitary T M₀ M₁ hM₀ hM₁ hT₀ hEnd θ hθ₀ hθ₁ u hz
  have hmem : T u ∈ (scalarDiagonal Sector (fun n => (a n)^θ)).domain := by
    apply (numberInterpolation_domain_iff (fun n => (a n)^θ) (T u)).mpr
    rw [← hb]
    exact b.property
  refine ⟨hmem,?_⟩
  let y : (scalarDiagonal Sector (fun n => (a n)^θ)).domain := ⟨T u,hmem⟩
  have hy : numberInterpolationForward (fun n => (a n)^θ) y = b := Subtype.ext hb.symm
  have hn := numberInterpolation_norm (fun n => (a n)^θ) y
  rw [hy] at hn
  have hi : (⟨numberInterpolationUnitary u,hz⟩ : GW.Spaces.sumWeightDomain (F := Sector) μ (fun n x => (w n x)^θ)) =
      numberInterpolationForward (fun n => (a n)^θ) ⟨u,hu⟩ := Subtype.ext rfl
  rw [hn,hi,numberInterpolation_norm] at hbound
  exact hbound


set_option backward.isDefEq.respectTransparency.types false in
lemma weyl_shifted_fractional_bound (f : OneBoson) (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1)
    (u : (shiftedNumberPower Sector σ).domain) :
    ∃ h : weylUnitary f u.val ∈ (shiftedNumberPower Sector σ).domain,
      ‖shiftedNumberPower Sector σ ⟨weylUnitary f u.val,h⟩‖ ≤
        (1+‖f‖)^(2*σ)*‖shiftedNumberPower Sector σ u‖ := by
  let T := (weylUnitary f).toLinearIsometry.toContinuousLinearMap
  have hpos : 0 < 1+‖f‖ := by positivity
  have hend (x : (scalarDiagonal Sector (fun n => (n:ℝ)+1)).domain) :
      ∃ h : T x.val ∈ (scalarDiagonal Sector (fun n => (n:ℝ)+1)).domain,
        ‖scalarDiagonal Sector (fun n => (n:ℝ)+1) ⟨T x.val,h⟩‖ ≤
          (1+‖f‖)^2*‖scalarDiagonal Sector (fun n => (n:ℝ)+1) x‖ := by
    have he : shiftedNumberPower Sector 1 = scalarDiagonal Sector (fun n => (n:ℝ)+1) := by
      simp only [shiftedNumberPower,Real.rpow_one]
    let v : NumberWeightedDomain Sector 1 zero_le_one :=
      show (shiftedNumberPower Sector 1).domain from ⟨x.val,by rw [he]; exact x.property⟩
    have hy := (show (shiftedNumberPower Sector 1).domain from weylNumberWeightedInput f v).property
    change weylUnitary f (numberDomainEmbedding 1 zero_le_one v) ∈ (shiftedNumberPower Sector 1).domain at hy
    rw [numberDomainEmbedding_apply] at hy
    change weylUnitary f x.val ∈ (shiftedNumberPower Sector 1).domain at hy
    rw [he] at hy
    refine ⟨hy,?_⟩
    have hb := weylNumberWeighted_norm f v
    change ‖shiftedNumberPower Sector 1 (weylNumberWeightedInput f v)‖ ≤
      (1+‖f‖)^2*‖shiftedNumberPower Sector 1 v‖ at hb
    simp only [shiftedNumberPower,Real.rpow_one] at hb
    convert! hb using 1
    · apply congrArg norm
      apply lp.ext
      funext n
      simp only [scalarDiagonal_apply,Real.rpow_one]
      have hW := weylNumberWeighted_embedding f v
      rw [numberDomainEmbedding_apply,numberDomainEmbedding_apply] at hW
      have hn := congrArg (fun z : Carrier => z n) hW
      congr 1
      exact hn.symm
    · congr 1
      apply congrArg norm
      apply lp.ext
      funext n
      simp only [scalarDiagonal_apply,Real.rpow_one]
      rfl
  obtain ⟨h,hb⟩ := number_scalar_interpolation (fun n => (n:ℝ)+1)
    (fun n => by have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith) T 1 ((1+‖f‖)^2) zero_lt_one (sq_pos_of_pos hpos)
    (fun z => by simp [T]) hend σ hσ₀ hσ₁ u.val u.property
  refine ⟨h,?_⟩
  have he : ((1+‖f‖)^2)^σ = (1+‖f‖)^(2*σ) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (le_of_lt hpos)]
    norm_num
  simp only [Real.one_rpow,one_mul,he] at hb
  convert! hb using 1 <;> rfl


lemma weyl_fractional_domain_iff (f : OneBoson) (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1)
    (u : Carrier) :
    weylUnitary f u ∈ (numberPower Sector σ).domain ↔ u ∈ (numberPower Sector σ).domain := by
  by_cases hzero : σ = 0
  · subst σ
    simp only [numberPower_zero,LinearMap.toPMap_domain,Submodule.mem_top]
  have hpos : 0 < σ := lt_of_le_of_ne hσ₀ (Ne.symm hzero)
  rw [numberPower_domain_eq Sector σ hpos]
  constructor
  · intro h
    obtain ⟨hh,_⟩ := weyl_shifted_fractional_bound (-f) σ hσ₀ hσ₁ ⟨weylUnitary f u,h⟩
    change weylUnitary (-f) (weylUnitary f u) ∈ (shiftedNumberPower Sector σ).domain at hh
    rw [← weylUnitary_symm,LinearIsometryEquiv.symm_apply_apply] at hh
    exact hh
  · intro h
    exact (weyl_shifted_fractional_bound f σ hσ₀ hσ₁ ⟨u,h⟩).choose

lemma weyl_fractional_domain_image (f : OneBoson) (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) :
    (weylUnitary f) '' ((numberPower Sector σ).domain : Set Carrier) =
      ((numberPower Sector σ).domain : Set Carrier) := by
  ext u
  constructor
  · rintro ⟨v,hv,rfl⟩
    exact (weyl_fractional_domain_iff f σ hσ₀ hσ₁ v).mpr hv
  · intro hu
    refine ⟨weylUnitary (-f) u,(weyl_fractional_domain_iff (-f) σ hσ₀ hσ₁ u).mpr hu,?_⟩
    rw [← weylUnitary_symm,LinearIsometryEquiv.apply_symm_apply]

end GW.Fock
