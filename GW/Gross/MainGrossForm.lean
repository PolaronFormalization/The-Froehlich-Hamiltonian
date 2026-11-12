module
public import GW.Analysis.L2Domination
public import GW.Fock.FockTwoFields
public import GW.Gross.MainCommutators
public import GW.Gross.MainGrossConvergence
public import GW.Regularity.RegComponentDomain
public import GW.Regularity.RegNumberField

/-! Source main:gross-form, manuscript6076–6283.
Original form and Hamiltonian domains, actual Weyl/field/momentum graphs,
sharp finite and uniform estimates, density and real-cutoff strong Q limits.
No operator-graph convergence at infinite cutoff is asserted. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Gross
open GW.Model GW.Fock GW.Analysis

/- Source argument component: Bounds01. -/
lemma grossForm_shiftedRoot_bound (u : freeFormOperator.domain) :
    ∃ hn : u.val ∈ (physicalShiftedNumberPower (1/2)).domain,
      ‖physicalShiftedNumberPower (1/2) ⟨u.val,hn⟩‖ ≤ ‖freeFormOperator u‖ := by
  rw [physicalShiftedNumberHalf_eq_sectorMultiplier]
  have hh := physicalSectorMultiplier_domination (fun n _ => Real.sqrt ((n:ℝ)+1)) freeFormWeight
    (fun _ => measurable_const) zero_le_one (fun n q => by
      rw [abs_of_nonneg (Real.sqrt_nonneg _),
        abs_of_nonneg (zero_le_one.trans (freeFormWeight_one n q)),one_mul]
      unfold freeFormWeight
      apply Real.sqrt_le_sqrt
      unfold freeGraphWeight freeEnergySymbol
      nlinarith [sq_nonneg ‖q‖]) u
  simpa only [one_mul,freeFormOperator] using hh

def grossFormRoot (u : FreeFormDomain) : FiberPhysicalRoot :=
  ⟨(show freeFormOperator.domain from u).val,(grossForm_shiftedRoot_bound u).choose⟩

def grossFormRootMap : FreeFormDomain →L[ℂ] FiberPhysicalRoot :=
  ({ toFun := grossFormRoot
     map_add' := fun u v => Subtype.ext rfl
     map_smul' := fun c u => Subtype.ext rfl } : FreeFormDomain →ₗ[ℂ] FiberPhysicalRoot).mkContinuous
    1 (fun u => by
      rw [one_mul,← fiberPhysicalRoot_norm,freeFormDomain_norm]
      exact (grossForm_shiftedRoot_bound u).choose_spec)

lemma grossFormRootMap_value (u : FreeFormDomain) :
    (fiberPhysicalRootInput (grossFormRootMap u)).val = freeFormDomainInclusion u :=
  (freeFormDomainInclusion_apply u).symm

lemma grossForm_coordinate_bound (u : freeFormOperator.domain) (j : Fin 3) :
    ∃ hp : u.val ∈ (electronMomentumCoordinate j).domain,
      ‖electronMomentumCoordinate j ⟨u.val,hp⟩‖ ≤ ‖freeFormOperator u‖ := by
  have hh := physicalSectorMultiplier_domination (fun _ q => q j) freeFormWeight
    (fun _ => electronCoordinate_measurable j) zero_le_one (fun n q => by
      rw [abs_of_nonneg (zero_le_one.trans (freeFormWeight_one n q)),one_mul]
      refine (electronCoordinate_abs_le q j).trans ?_
      apply (sq_le_sq₀ (norm_nonneg q) (zero_le_one.trans (freeFormWeight_one n q))).mp
      rw [freeFormWeight_square_split]
      nlinarith [sq_nonneg (Real.sqrt (n:ℝ))]) u
  simpa only [one_mul,freeFormOperator,electronMomentumCoordinate] using hh

def grossFormMomentumInput (j : Fin 3) (u : FreeFormDomain) : (electronMomentumCoordinate j).domain :=
  ⟨(show freeFormOperator.domain from u).val,(grossForm_coordinate_bound u j).choose⟩

def grossFormMomentumLinear (j : Fin 3) : FreeFormDomain →ₗ[ℂ] Physical where
  toFun u := electronMomentumCoordinate j (grossFormMomentumInput j u)
  map_add' u v := by
    have he : grossFormMomentumInput j (u+v) = grossFormMomentumInput j u+grossFormMomentumInput j v :=
      Subtype.ext rfl
    rw [he]
    exact (electronMomentumCoordinate j).toFun.map_add _ _
  map_smul' c u := by
    have he : grossFormMomentumInput j (c • u) = c • grossFormMomentumInput j u := Subtype.ext rfl
    rw [he]
    exact (electronMomentumCoordinate j).toFun.map_smul _ _

def grossFormMomentumMap (j : Fin 3) : FreeFormDomain →L[ℂ] Physical :=
  (grossFormMomentumLinear j).mkContinuous 1 (fun u => by
    rw [one_mul,freeFormDomain_norm]
    exact (grossForm_coordinate_bound u j).choose_spec)

lemma grossFormMomentumMap_graph (j : Fin 3) (u : FreeFormDomain) :
    (freeFormDomainInclusion u,grossFormMomentumMap j u) ∈ (electronMomentumCoordinate j).graph := by
  have h := (electronMomentumCoordinate j).mem_graph (grossFormMomentumInput j u)
  exact (freeFormDomainInclusion_apply u).symm ▸ h

def grossFormSmoothInput (φ : SmoothScalarTest) (v : Carrier) (hv : v ∈ finiteSectorDomain Sector) : FreeFormDomain :=
  smoothProductGraphToFormMap (smoothProductSmoothInput φ v hv)

lemma grossFormSmoothInput_ambient (φ : SmoothScalarTest) (v : Carrier) (hv : v ∈ finiteSectorDomain Sector) :
    freeFormDomainInclusion (grossFormSmoothInput φ v hv) = (ContinuousLinearMap.toSpanSingleton ℂ v).compLp φ.toL2 :=
  (smoothProductGraphToForm_inclusion _).trans (smoothProductSmoothInput_ambient φ v hv)

lemma grossFormRoot_tensor (φ : SmoothScalarTest) (v : Carrier) (hv : v ∈ finiteSectorDomain Sector) :
    grossFormRootMap (grossFormSmoothInput φ v hv) =
      weightedSimpleTensor volume Sector (1/2) (by norm_num) φ.toL2 (commutatorFiniteRoot v hv) := by
  have ht : (fiberPhysicalRootInput (weightedSimpleTensor volume Sector (1/2) (by norm_num)
      φ.toL2 (commutatorFiniteRoot v hv))).val =
      (ContinuousLinearMap.toSpanSingleton ℂ (numberDomainInclusion Sector (1/2) (by norm_num)
        (commutatorFiniteRoot v hv))).compLp φ.toL2 :=
    weightedSimpleTensor_ambient volume Sector (1/2) (by norm_num) φ.toL2 (commutatorFiniteRoot v hv)
  rw [commutatorFiniteRoot_value] at ht
  apply Subtype.ext
  exact (grossFormRootMap_value _).trans ((grossFormSmoothInput_ambient φ v hv).trans ht.symm)

lemma grossFormMomentum_tensor (φ : SmoothScalarTest) (j : Fin 3) (v : Carrier)
    (hv : v ∈ finiteSectorDomain Sector) :
    grossFormMomentumMap j (grossFormSmoothInput φ v hv) =
      (ContinuousLinearMap.toSpanSingleton ℂ v).compLp (commutatorScalarMomentum φ j) := by
  apply (electronMomentumCoordinate j).mem_graph_snd_inj
    (grossFormMomentumMap_graph j (grossFormSmoothInput φ v hv)) (commutatorTensor_momentum_graph φ j v)
  exact grossFormSmoothInput_ambient φ v hv

lemma grossFormCore_span {C : Submodule ℂ FreeFormDomain}
    (h : ∀ (φ : SmoothScalarTest) (v : Carrier) (hv : v ∈ finiteSectorDomain Sector),
      grossFormSmoothInput φ v hv ∈ C) : smoothFiniteFormCore ≤ C := by
  have hs : smoothFiniteProductCore ≤ C.map freeFormDomainInclusion.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro u ⟨φ,v,hv,rfl⟩
    exact ⟨grossFormSmoothInput φ v hv,h φ v hv,grossFormSmoothInput_ambient φ v hv⟩
  intro u hu
  obtain ⟨v,hv,he⟩ := hs hu
  have he' : v = u := by
    apply Subtype.ext
    exact (freeFormDomainInclusion_apply v).symm.trans (he.trans (freeFormDomainInclusion_apply u))
  exact he' ▸ hv

/- Source argument component: Core01. -/
def grossFormFieldMap (f : OneBoson) : FiberPhysicalRoot →L[ℂ] Physical :=
  commutatorPhaseAnnihilatorMap f+commutatorPhaseCreatorMap f

lemma grossFormFieldMap_tensor_ae (f : OneBoson) (γ : ElectronL2) (u : FiberRootDomain) :
    grossFormFieldMap f (weightedSimpleTensor volume Sector (1/2) (by norm_num) γ u) =ᵐ[volume]
      (fun x => γ x • ordinaryFieldHalfMap (phaseAt f x) u) := by
  let U := weightedSimpleTensor volume Sector (1/2) (by norm_num) γ u
  filter_upwards [commutatorPhaseAnnihilator_tensor_ae f γ u,commutatorPhaseCreator_tensor_ae f γ u,
    Lp.coeFn_add (commutatorPhaseAnnihilatorMap f U) (commutatorPhaseCreatorMap f U)] with x ha hc hs
  change (commutatorPhaseAnnihilatorMap f U+commutatorPhaseCreatorMap f U) x = _
  rw [hs]
  change commutatorPhaseAnnihilatorMap f U x+commutatorPhaseCreatorMap f U x = _
  rw [ha,hc,← smul_add,fiberOrdinaryField_eq]

lemma grossFormRoot_ordinary_ambient (u : FiberRootDomain) :
    numberDomainEmbedding (1/2) (by norm_num) u = numberDomainInclusion Sector (1/2) (by norm_num) u :=
  (numberDomainEmbedding_apply (1/2) (by norm_num) u).trans
    (numberDomainInclusion_apply Sector (1/2) (by norm_num) u).symm

lemma grossFormWeyl_tensor (f : OneBoson) (φ : SmoothScalarTest) (u : FiberRootDomain) :
    grossWeylCoefficient f ((ContinuousLinearMap.toSpanSingleton ℂ (numberDomainInclusion Sector (1/2) (by norm_num) u)).compLp φ.toL2) =
      weylPhaseProductClass f u φ := by
  apply Lp.ext
  let v := numberDomainInclusion Sector (1/2) (by norm_num) u
  filter_upwards [grossWeylCoefficient_ae f ((ContinuousLinearMap.toSpanSingleton ℂ v).compLp φ.toL2),
    (ContinuousLinearMap.toSpanSingleton ℂ v).coeFn_compLp φ.toL2,φ.toL2_ae,
    weylPhaseProductClass_ae f u φ] with x hw ht hφ hc
  rw [hw,hc,ht,hφ]
  change weylUnitary (phaseAt f x) (φ.value x • v) = _
  rw [map_smul,grossFormRoot_ordinary_ambient]

lemma grossFormWeyl_tensor_momentum_graph (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2)
    (φ : SmoothScalarTest) (u : FiberRootDomain) :
    (grossWeylCoefficient f ((ContinuousLinearMap.toSpanSingleton ℂ (numberDomainInclusion Sector (1/2) (by norm_num) u)).compLp φ.toL2),
      grossWeylCoefficient f ((ContinuousLinearMap.toSpanSingleton ℂ (numberDomainInclusion Sector (1/2) (by norm_num) u)).compLp
        (commutatorScalarMomentum φ j)-grossFormFieldMap (weylMomentumCoefficient f j hj)
          (weightedSimpleTensor volume Sector (1/2) (by norm_num) φ.toL2 u))) ∈
      (electronMomentumCoordinate j).graph := by
  obtain ⟨V,hV,hAE⟩ := weylPhaseProduct_momentum_graph f j hj heven u φ
  have hfirst := grossFormWeyl_tensor f φ u
  let v := numberDomainInclusion Sector (1/2) (by norm_num) u
  let a := (ContinuousLinearMap.toSpanSingleton ℂ v).compLp (commutatorScalarMomentum φ j)
  let b := grossFormFieldMap (weylMomentumCoefficient f j hj)
    (weightedSimpleTensor volume Sector (1/2) (by norm_num) φ.toL2 u)
  have hsecond : V = grossWeylCoefficient f (a-b) := by
    apply Lp.ext
    filter_upwards [hAE,grossWeylCoefficient_ae f (a-b),Lp.coeFn_sub a b,
      (ContinuousLinearMap.toSpanSingleton ℂ v).coeFn_compLp (commutatorScalarMomentum φ j),
      commutatorScalarMomentum_ae φ j,grossFormFieldMap_tensor_ae (weylMomentumCoefficient f j hj) φ.toL2 u,
      φ.toL2_ae] with x h₁ h₂ h₃ h₄ h₅ h₆ h₇
    rw [h₁,h₂,h₃]
    change weylUnitary (phaseAt f x) _ = weylUnitary (phaseAt f x) (a x-b x)
    rw [show a x = commutatorScalarMomentum φ j x • v from h₄,
      show b x = φ.toL2 x • ordinaryFieldHalfMap (phaseAt (weylMomentumCoefficient f j hj) x) u from h₆,
      h₅,h₇,grossFormRoot_ordinary_ambient]
    rfl
  rw [hsecond] at hV
  rw [hfirst]
  exact (commutatorMomentum_graph j _ _).mpr hV

/- Source argument component: Extension01. -/
def grossFormWeylRightMap (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) : FreeFormDomain →L[ℂ] Physical :=
  (grossWeylCoefficient f).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (grossFormMomentumMap j-(grossFormFieldMap (weylMomentumCoefficient f j hj)).comp grossFormRootMap)

lemma grossFormWeyl_momentum_core (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2)
    (u : FreeFormDomain) (hu : u ∈ smoothFiniteFormCore) :
    (grossWeylCoefficient f (freeFormDomainInclusion u),grossFormWeylRightMap f j hj u) ∈
      (electronMomentumCoordinate j).graph := by
  let T := (grossWeylCoefficient f).toContinuousLinearEquiv.toContinuousLinearMap.comp freeFormDomainInclusion
  let C := (electronMomentumCoordinate j).graph.comap (T.prod (grossFormWeylRightMap f j hj)).toLinearMap
  have hc : smoothFiniteFormCore ≤ C := grossFormCore_span (fun φ v hv => by
    change (grossWeylCoefficient f (freeFormDomainInclusion (grossFormSmoothInput φ v hv)),
      grossFormWeylRightMap f j hj (grossFormSmoothInput φ v hv)) ∈ (electronMomentumCoordinate j).graph
    have hh := grossFormWeyl_tensor_momentum_graph f j hj heven φ (commutatorFiniteRoot v hv)
    rw [commutatorFiniteRoot_value] at hh
    change (grossWeylCoefficient f (freeFormDomainInclusion (grossFormSmoothInput φ v hv)),
      grossWeylCoefficient f (grossFormMomentumMap j (grossFormSmoothInput φ v hv)-
        grossFormFieldMap (weylMomentumCoefficient f j hj) (grossFormRootMap (grossFormSmoothInput φ v hv)))) ∈
      (electronMomentumCoordinate j).graph
    rw [grossFormSmoothInput_ambient,grossFormMomentum_tensor,grossFormRoot_tensor]
    exact hh)

  exact hc hu

lemma grossFormWeyl_momentum_graph (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2) (u : FreeFormDomain) :
    (grossWeylCoefficient f (freeFormDomainInclusion u),grossFormWeylRightMap f j hj u) ∈
      (electronMomentumCoordinate j).graph := by
  have hc : ∀ c : smoothFiniteFormCore,
      ∃ hc : grossWeylCoefficient f (freeFormDomainInclusion c) ∈ (electronMomentumCoordinate j).domain,
        electronMomentumCoordinate j ⟨grossWeylCoefficient f (freeFormDomainInclusion c),hc⟩ = grossFormWeylRightMap f j hj c := by
    intro c
    have hg := grossFormWeyl_momentum_core f j hj heven c.val c.property
    have hm := (electronMomentumCoordinate j).mem_domain_of_mem_graph hg
    exact ⟨hm,(electronMomentumCoordinate j).mem_graph_snd_inj ((electronMomentumCoordinate j).mem_graph ⟨_,hm⟩) hg rfl⟩
  have hclosed : (electronMomentumCoordinate j).IsClosed :=
    GW.Operators.selfadjoint_closed _ (physicalSectorMultiplier_selfadjoint (fun _ => electronCoordinate_measurable j))
  obtain ⟨hm,he⟩ := GW.Operators.closed_graph_extension freeFormDomainInclusion
    (grossWeylCoefficient f).toContinuousLinearEquiv.toContinuousLinearMap (grossFormWeylRightMap f j hj)
    (electronMomentumCoordinate j) hclosed smoothFiniteFormCore smoothFiniteFormCore_dense hc u
  exact (electronMomentumCoordinate j).mem_graph_iff.mpr ⟨⟨_,hm⟩,rfl,he⟩

/- Source argument component: Coefficient03. -/
lemma grossForm_raw_momentum_sq_bound (α K : ℝ) (j : Fin 3) (k : GW.Space) :
    ‖(k j : ℂ)*(b α K k : ℂ)‖^2 ≤ grossCoefficientMajorant α K k := by
  rw [norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,mul_pow,sq_abs,sq_abs]
  by_cases hk : K < ‖k‖
  · rw [grossCoefficientMajorant,indicator_of_mem hk]
    have hp : 0 < 1+‖k‖^2 := by positivity
    have hj : (k j)^2 ≤ ‖k‖^2 := by
      have h := electronCoordinate_abs_le k j
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (k j)) (norm_nonneg k)).mpr h
    have he : (1+‖k‖^2)*(b α K k)^2 = (v α k)^2/(1+‖k‖^2) := by
      rw [b,if_pos hk]
      field_simp
      <;> ring
    exact (mul_le_mul_of_nonneg_right (hj.trans (by linarith)) (sq_nonneg _)).trans_eq he
  · rw [b,if_neg hk,grossCoefficientMajorant,indicator_of_notMem hk]
    norm_num

lemma grossForm_momentum_memLp (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (j : Fin 3) :
    MemLp (fun k => (k j : ℂ)*grossDressingCoefficient α K hα hK k) 2 (volume : Measure GW.Space) := by
  have hm : Measurable (fun k : GW.Space => (k j : ℂ)*(b α K k : ℂ)) :=
    (Complex.continuous_ofReal.measurable.comp (electronCoordinate_measurable j)).mul
      (Complex.continuous_ofReal.measurable.comp (b_measurable α K))
  have hh : MemLp (fun k : GW.Space => (k j : ℂ)*(b α K k : ℂ)) 2 (volume : Measure GW.Space) := by
    apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
    apply (grossCoefficientMajorant_integrable α K hα hK).mono' (hm.norm.pow_const 2).aestronglyMeasurable
    exact Eventually.of_forall fun k => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact grossForm_raw_momentum_sq_bound α K j k
  apply (memLp_congr_ae _).mp hh
  filter_upwards [grossDressingCoefficient_ae α K hα hK] with k hk
  rw [hk]

lemma grossForm_coefficient_even (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    ∀ᵐ k ∂(volume : Measure GW.Space),
      ‖grossDressingCoefficient α K hα hK (-k)‖^2 = ‖grossDressingCoefficient α K hα hK k‖^2 := by
  have hn := (Measure.measurePreserving_neg (volume : Measure GW.Space)).quasiMeasurePreserving.ae
    (grossDressingCoefficient_ae α K hα hK)
  filter_upwards [hn,grossDressingCoefficient_ae α K hα hK] with k h₁ h₂
  rw [h₁,h₂,b_even]

lemma grossForm_truncate_momentum_memLp (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) (Λ : ℝ) :
    MemLp (fun k => (k j : ℂ)*grossTruncateCoefficient f Λ k) 2 (volume : Measure GW.Space) := by
  have hh := hj.indicator (lowRegion_measurable Λ).nullMeasurableSet
  apply (memLp_congr_ae _).mp hh
  filter_upwards [grossTruncateCoefficient_ae f Λ] with k hk
  rw [hk]
  by_cases h : k ∈ lowRegion Λ
  · rw [indicator_of_mem h,indicator_of_mem h]
  · rw [indicator_of_notMem h,indicator_of_notMem h,mul_zero]

lemma grossForm_truncate_even (f : OneBoson) (Λ : ℝ)
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2) :
    ∀ᵐ k ∂(volume : Measure GW.Space),
      ‖grossTruncateCoefficient f Λ (-k)‖^2 = ‖grossTruncateCoefficient f Λ k‖^2 := by
  have hn := (Measure.measurePreserving_neg (volume : Measure GW.Space)).quasiMeasurePreserving.ae
    (grossTruncateCoefficient_ae f Λ)
  filter_upwards [hn,grossTruncateCoefficient_ae f Λ,heven] with k h₁ h₂ h₃
  rw [h₁,h₂]
  have he : (-k) ∈ lowRegion Λ ↔ k ∈ lowRegion Λ := by
    change ‖-k‖ ≤ Λ ↔ ‖k‖ ≤ Λ
    rw [norm_neg]
  by_cases hk : k ∈ lowRegion Λ
  · rw [indicator_of_mem hk,indicator_of_mem (he.mpr hk),h₃]
  · rw [indicator_of_notMem hk,indicator_of_notMem (fun h => hk (he.mp h))]

lemma grossForm_neg_momentum_memLp (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) :
    MemLp (fun k => (k j : ℂ)*(-f) k) 2 (volume : Measure GW.Space) := by
  apply (memLp_congr_ae _).mp hj.neg
  filter_upwards [Lp.coeFn_neg f] with k hk
  rw [hk]
  simp only [Pi.neg_apply,mul_neg]

lemma grossForm_neg_even (f : OneBoson)
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2) :
    ∀ᵐ k ∂(volume : Measure GW.Space), ‖(-f) (-k)‖^2 = ‖(-f) k‖^2 := by
  have hn := (Measure.measurePreserving_neg (volume : Measure GW.Space)).quasiMeasurePreserving.ae (Lp.coeFn_neg f)
  filter_upwards [hn,Lp.coeFn_neg f,heven] with k h₁ h₂ h₃
  rw [h₁,h₂]
  simpa only [Pi.neg_apply,norm_neg] using h₃

/- Source argument component: Membership01. -/
lemma grossForm_allMomentum_mem (U : Physical)
    (h : ∀ j : Fin 3, U ∈ (electronMomentumCoordinate j).domain) :
    U ∈ freeMomentumModulus.domain := by
  have hh := (radial_component_domain 0 (by norm_num) U).mpr (fun j => by
    refine ⟨h j,?_⟩
    rw [radialPower_zero]
    change _ ∈ (⊤ : Submodule ℂ Physical)
    trivial)
  simpa only [add_zero,Real.rpow_one,freeMomentumModulus] using hh

lemma grossFormWeyl_mem (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2) (u : FreeFormDomain) :
    grossWeylCoefficient f (freeFormDomainInclusion u) ∈ freeFormOperator.domain := by
  have hp : grossWeylCoefficient f (freeFormDomainInclusion u) ∈ freeMomentumModulus.domain :=
    grossForm_allMomentum_mem _ (fun j => (electronMomentumCoordinate j).mem_domain_of_mem_graph
      (grossFormWeyl_momentum_graph f j (hj j) heven u))
  have hroot : freeFormDomainInclusion u ∈ (physicalShiftedNumberPower (1/2)).domain := by
    rw [← grossFormRootMap_value]
    exact (fiberPhysicalRootInput (grossFormRootMap u)).property
  have hn := fiberWeyl_shifted_domain (1/2) (by norm_num) (by norm_num)
    (phaseAt f) (phaseAt_continuous f).stronglyMeasurable ‖f‖ (commutatorPhase_norm_bound f)
    (freeFormDomainInclusion u) hroot
  have hn' : grossWeylCoefficient f (freeFormDomainInclusion u) ∈ freeRootNumber.domain := by
    rw [freeRootNumber_eq,physicalNumberPower_domains_eq (1/2) (by norm_num)]
    exact hn
  exact (freeFormDomain_mem_norm _ hp hn').choose

def grossFormWeylInput (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2)
    (u : FreeFormDomain) : FreeFormDomain :=
  ⟨grossWeylCoefficient f (freeFormDomainInclusion u),grossFormWeyl_mem f hj heven u⟩

lemma grossFormWeylInput_value (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2) (u : FreeFormDomain) :
    freeFormDomainInclusion (grossFormWeylInput f hj heven u) = grossWeylCoefficient f (freeFormDomainInclusion u) :=
  freeFormDomainInclusion_apply _

lemma grossFormDomainInclusion_injective : Function.Injective freeFormDomainInclusion := by
  intro u v h
  apply Subtype.ext
  exact (freeFormDomainInclusion_apply u).symm.trans (h.trans (freeFormDomainInclusion_apply v))

lemma grossFormWeyl_left_inverse (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2) (u : FreeFormDomain) :
    grossFormWeylInput (-f) (fun j => grossForm_neg_momentum_memLp f j (hj j)) (grossForm_neg_even f heven)
      (grossFormWeylInput f hj heven u) = u := by
  apply grossFormDomainInclusion_injective
  rw [grossFormWeylInput_value,grossFormWeylInput_value,← grossWeylCoefficient_symm_apply,
    LinearIsometryEquiv.symm_apply_apply]

lemma grossFormWeyl_right_inverse (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2) (u : FreeFormDomain) :
    grossFormWeylInput f hj heven
      (grossFormWeylInput (-f) (fun j => grossForm_neg_momentum_memLp f j (hj j)) (grossForm_neg_even f heven) u) = u := by
  apply grossFormDomainInclusion_injective
  rw [grossFormWeylInput_value,grossFormWeylInput_value,← grossWeylCoefficient_symm_apply,
    LinearIsometryEquiv.apply_symm_apply]

lemma grossFormWeyl_domain_image (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2) :
    grossWeylCoefficient f '' (freeFormOperator.domain : Set Physical) = freeFormOperator.domain := by
  apply Set.Subset.antisymm
  · rintro _ ⟨U,hU,rfl⟩
    let u : FreeFormDomain := ⟨U,hU⟩
    have hu : freeFormDomainInclusion u = U := freeFormDomainInclusion_apply u
    exact hu ▸ grossFormWeyl_mem f hj heven u
  · intro U hU
    let u : FreeFormDomain := ⟨U,hU⟩
    let v := grossFormWeylInput (-f) (fun j => grossForm_neg_momentum_memLp f j (hj j)) (grossForm_neg_even f heven) u
    refine ⟨freeFormDomainInclusion v,?_,?_⟩
    · exact (freeFormDomainInclusion_apply v).symm ▸ (show freeFormOperator.domain from v).property
    · change grossWeylCoefficient f (freeFormDomainInclusion v) = U
      rw [grossFormWeylInput_value,← grossWeylCoefficient_symm_apply,LinearIsometryEquiv.apply_symm_apply]
      exact freeFormDomainInclusion_apply u

/- Source argument component: FieldGraph04. -/
lemma grossFormFieldMap_bound (f : OneBoson) (u : FiberPhysicalRoot) :
    ‖grossFormFieldMap f u‖ ≤ 2*‖f‖*‖u‖ := by
  change ‖commutatorPhaseAnnihilatorMap f u+commutatorPhaseCreatorMap f u‖ ≤ _
  exact (norm_add_le _ _).trans ((add_le_add (commutatorPhaseAnnihilatorMap_bound f u)
    (commutatorPhaseCreatorMap_bound f u)).trans_eq (by ring))

lemma grossInitialField_graph {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (C A : H →ₗ.[ℂ] H) (V : Submodule ℂ H) (hC : V ≤ C.domain) (hA : V ≤ A.domain)
    (u a c : H) (hu : u ∈ V) (ha : (u,a) ∈ A.graph) (hc : (u,c) ∈ C.graph) :
    (u,a+c) ∈ (initialField C A V hC hA).graph := by
  refine (initialField C A V hC hA).mem_graph_iff.mpr ⟨⟨u,hu⟩,rfl,?_⟩
  rw [initialField_action]
  exact congrArg₂ (fun a c : H => a+c)
    (A.mem_graph_snd_inj (A.mem_graph _) ha rfl)
    (C.mem_graph_snd_inj (C.mem_graph _) hc rfl)

lemma grossGeneralizedField_graph (K : BosonKernel ElectronL2) (u a c : Physical)
    (hu : u ∈ (physicalNumberPower (1/2)).domain)
    (ha : (u,a) ∈ (generalizedAnnihilation K).graph)
    (hc : (u,c) ∈ (generalizedCreation K).graph) :
    (u,a+c) ∈ (generalizedField K).graph :=
  grossInitialField_graph (generalizedCreation K) (generalizedAnnihilation K)
    (physicalNumberPower (1/2)).domain
    (fun v hv => generalizedCreation_mem_root K ⟨v,hv⟩)
    (fun v hv => generalizedAnnihilation_mem_root K ⟨v,hv⟩) u a c hu ha hc

lemma grossForm_root_mem_unshifted (u : FiberPhysicalRoot) :
    (fiberPhysicalRootInput u).val ∈ (physicalNumberPower (1/2)).domain :=
  (congrArg (fun D : Submodule ℂ Physical => (fiberPhysicalRootInput u).val ∈ D)
    physicalRootNumber_domains_eq).mpr (fiberPhysicalRootInput u).property

lemma grossFormFieldMap_graph (f : OneBoson) (u : FiberPhysicalRoot) :
    ((fiberPhysicalRootInput u).val,grossFormFieldMap f u) ∈
      (generalizedField (phaseMultiplicationKernel f)).graph := by
  have hs : grossFormFieldMap f u = commutatorPhaseAnnihilatorMap f u+commutatorPhaseCreatorMap f u :=
    ContinuousLinearMap.add_apply _ _ _
  rw [hs]
  exact grossGeneralizedField_graph (phaseMultiplicationKernel f) (fiberPhysicalRootInput u).val
    (commutatorPhaseAnnihilatorMap f u) (commutatorPhaseCreatorMap f u)
    (grossForm_root_mem_unshifted u)
    (commutatorPhaseAnnihilatorMap_graph f u) (commutatorPhaseCreatorMap_graph f u)

/- Source argument component: FieldQ01. -/
lemma grossGraph_field_momentum_graph (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (u : FreeGraphDomain) :
    (grossFormFieldMap f (commutatorGraphRootMap u),
      commutatorAnnihilatorRightMap f j hj u+commutatorCreatorRightMap f j hj u) ∈
      (electronMomentumCoordinate j).graph := by
  have h := (electronMomentumCoordinate j).graph.add_mem
    (commutatorAnnihilator_graph_all f j hj u) (commutatorCreator_graph_all f j hj u)
  change (commutatorPhaseAnnihilatorMap f (commutatorGraphRootMap u)+
    commutatorPhaseCreatorMap f (commutatorGraphRootMap u),_) ∈ _ at h
  exact h

lemma grossGraph_field_number_mem (f : OneBoson) (u : FreeGraphDomain) :
    grossFormFieldMap f (commutatorGraphRootMap u) ∈ (physicalNumberPower (1/2)).domain := by
  let U : physicalNumberOperator.domain := ⟨(freeGraphH0Input u).val,
    freeHamiltonian_number_mem (freeGraphH0Input u)⟩
  have h₁ := grossFormFieldMap_graph f (commutatorGraphRootMap u)
  rw [commutatorGraphRootMap_value] at h₁
  have h₂ := physicalRegField_graph (phaseMultiplicationKernel f) U
  have hi : U.val = freeGraphDomainInclusion u := (freeGraphDomainInclusion_apply u).symm
  rw [hi] at h₂
  have he := (generalizedField (phaseMultiplicationKernel f)).mem_graph_snd_inj h₁ h₂ rfl
  rw [he]
  exact (physicalRegFieldOutput (phaseMultiplicationKernel f) U).property

lemma grossGraph_field_form_mem (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (u : FreeGraphDomain) :
    grossFormFieldMap f (commutatorGraphRootMap u) ∈ freeFormOperator.domain := by
  rw [freeForm_domain_intersection]
  exact ⟨grossForm_allMomentum_mem _ (fun j => (electronMomentumCoordinate j).mem_domain_of_mem_graph
    (grossGraph_field_momentum_graph f j (hj j) u)),grossGraph_field_number_mem f u⟩

/- Source argument component: GraphMomentum02. -/
lemma grossGraph_momentum_form_bound (u : freeGraphOperator.domain) (j : Fin 3) :
    ∃ hn : electronMomentumCoordinate j (commutatorMomentumInput u j) ∈ freeFormOperator.domain,
      ‖freeFormOperator ⟨electronMomentumCoordinate j (commutatorMomentumInput u j),hn⟩‖ ≤
        ‖freeGraphOperator u‖ := by
  have hq (n : ℕ) (q : GW.Space) : ‖q‖ ≤ freeFormWeight n q := by
    apply (sq_le_sq₀ (norm_nonneg q) (zero_le_one.trans (freeFormWeight_one n q))).mp
    rw [freeFormWeight_square_split]
    nlinarith [sq_nonneg (Real.sqrt (n:ℝ))]
  obtain ⟨hm,hb⟩ := physicalSectorMultiplier_domination (fun n q => freeFormWeight n q*q j) freeGraphWeight
    (fun n => (freeFormWeight_measurable n).mul (electronCoordinate_measurable j)) zero_le_one
    (fun n q => by
      rw [abs_mul,abs_of_nonneg (zero_le_one.trans (freeFormWeight_one n q)),
        abs_of_nonneg (zero_le_one.trans (freeGraphWeight_one n q)),one_mul]
      calc
        _ ≤ freeFormWeight n q*‖q‖ :=
          mul_le_mul_of_nonneg_left (electronCoordinate_abs_le q j) (zero_le_one.trans (freeFormWeight_one n q))
        _ ≤ freeFormWeight n q*freeFormWeight n q :=
          mul_le_mul_of_nonneg_left (hq n q) (zero_le_one.trans (freeFormWeight_one n q))
        _ = freeGraphWeight n q := by rw [← pow_two,freeFormWeight_sq]) u
  obtain ⟨hn,he⟩ := physicalSectorMultiplier_composition (fun _ q => q j) freeFormWeight u.val
    (commutatorMomentumInput u j).property hm
  refine ⟨hn,?_⟩
  change ‖physicalSectorMultiplier freeFormWeight
    ⟨electronMomentumCoordinate j (commutatorMomentumInput u j),hn⟩‖ ≤ _
  have he' : physicalSectorMultiplier freeFormWeight
    ⟨electronMomentumCoordinate j (commutatorMomentumInput u j),hn⟩ =
    physicalSectorMultiplier (fun n q => freeFormWeight n q*q j) ⟨u.val,hm⟩ := he
  exact (congrArg norm he').le.trans (by simpa only [one_mul,freeGraphOperator] using hb)

/- Source argument component: Operators01. -/
lemma grossPhysicalFourierMultiplier_graph (m : GW.Space → ℝ) (u v : Physical) :
    (u,v) ∈ (physicalSectorMultiplier (fun _ => m)).graph ↔
      (u,v) ∈ (fourierMultiplier (H := Carrier) m).graph := by
  unfold fourierMultiplier
  rw [commutatorPhysicalMultiplier_graph,GW.Operators.unitaryTransport_graph_iff,
    realMultiplier_graph_ae,commutatorCoordinate_multiplier_ae]
  simp_rw [commutatorFourier_coordinate]

lemma grossPhysicalFourierMultiplier_operator (m : GW.Space → ℝ) :
    physicalSectorMultiplier (fun _ => m) = fourierMultiplier (H := Carrier) m := by
  apply LinearPMap.ext
  · ext u
    rw [LinearPMap.mem_domain_iff,LinearPMap.mem_domain_iff]
    exact exists_congr fun v => grossPhysicalFourierMultiplier_graph m u v
  · intro u hu hv
    exact (fourierMultiplier (H := Carrier) m).mem_graph_snd_inj
      ((grossPhysicalFourierMultiplier_graph m u _).mp
        ((physicalSectorMultiplier (fun _ => m)).mem_graph ⟨u,hu⟩))
      ((fourierMultiplier (H := Carrier) m).mem_graph ⟨u,hv⟩) rfl

lemma grossMomentumSquare_operator : freeMomentumSquare = absoluteMomentumPower (H := Carrier) 2 := by
  have h := grossPhysicalFourierMultiplier_operator (fun q => ‖q‖^(2:ℝ))
  simpa only [Real.rpow_two,freeMomentumSquare,absoluteMomentumPower] using h

/- Source argument component: FiniteKinetic05. -/
lemma grossGraph_to_form_root (u : FreeGraphDomain) :
    grossFormRootMap (smoothProductGraphToFormMap u) = commutatorGraphRootMap u := by
  apply Subtype.ext
  exact (grossFormRootMap_value _).trans
    ((smoothProductGraphToForm_inclusion u).trans (commutatorGraphRootMap_value u).symm)

lemma grossGraph_to_form_momentum (u : FreeGraphDomain) (j : Fin 3) :
    grossFormMomentumMap j (smoothProductGraphToFormMap u) =
      electronMomentumCoordinate j (commutatorMomentumInput u j) := by
  have h := grossFormMomentumMap_graph j (smoothProductGraphToFormMap u)
  rw [smoothProductGraphToForm_inclusion,freeGraphDomainInclusion_apply] at h
  exact (electronMomentumCoordinate j).mem_graph_snd_inj h
    ((electronMomentumCoordinate j).mem_graph (commutatorMomentumInput u j)) rfl

lemma grossGraph_covariant_momentum_form_mem (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (hjj : ∀ i j : Fin 3, MemLp (fun k => (k j : ℂ)*(weylMomentumCoefficient f i (hj i)) k)
      2 (volume : Measure GW.Space)) (u : FreeGraphDomain) (j : Fin 3) :
    grossFormMomentumMap j (smoothProductGraphToFormMap u)-
      grossFormFieldMap (weylMomentumCoefficient f j (hj j))
        (grossFormRootMap (smoothProductGraphToFormMap u)) ∈ freeFormOperator.domain := by
  rw [grossGraph_to_form_root,grossGraph_to_form_momentum]
  exact freeFormOperator.domain.sub_mem (grossGraph_momentum_form_bound u j).choose
    (grossGraph_field_form_mem _ (hjj j) u)

lemma grossGraphWeyl_second_momentum (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (hjj : ∀ i j : Fin 3, MemLp (fun k => (k j : ℂ)*(weylMomentumCoefficient f i (hj i)) k)
      2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2)
    (u : FreeGraphDomain) :
    grossWeylCoefficient f (freeGraphDomainInclusion u) ∈ freeMomentumSquare.domain := by
  rw [grossMomentumSquare_operator]
  apply momentum_second_domain_reverse (E := Carrier)
  let q := smoothProductGraphToFormMap u
  let eta (j : Fin 3) : FreeFormDomain :=
    ⟨grossFormMomentumMap j q-grossFormFieldMap (weylMomentumCoefficient f j (hj j))
      (grossFormRootMap q),grossGraph_covariant_momentum_form_mem f hj hjj u j⟩
  refine ⟨fun j => grossWeylCoefficient f (freeFormDomainInclusion (eta j)),?_,?_⟩
  · intro j
    rw [← commutatorMomentum_graph,← smoothProductGraphToForm_inclusion]
    have h := grossFormWeyl_momentum_graph f j (hj j) heven q
    have heta : freeFormDomainInclusion (eta j) = grossFormMomentumMap j q-
        grossFormFieldMap (weylMomentumCoefficient f j (hj j)) (grossFormRootMap q) :=
      freeFormDomainInclusion_apply (eta j)
    dsimp only
    rw [heta]
    exact h
  · intro j
    refine ⟨grossFormWeylRightMap f j (hj j) (eta j),?_⟩
    rw [← commutatorMomentum_graph]
    exact grossFormWeyl_momentum_graph f j (hj j) heven (eta j)

lemma grossGraphWeyl_number_mem (f : OneBoson) (u : FreeGraphDomain) :
    grossWeylCoefficient f (freeGraphDomainInclusion u) ∈ physicalNumberOperator.domain := by
  let U : physicalNumberOperator.domain := ⟨(freeGraphH0Input u).val,
    freeHamiltonian_number_mem (freeGraphH0Input u)⟩
  have hfin : eLpNormEssSup (phaseAt f) (volume : Measure GW.Space) < ⊤ :=
    eLpNormEssSup_lt_top_of_ae_bound (commutatorPhase_norm_bound f)
  have h := fiberWeyl_number_mem_domain (phaseAt f) (phaseAt_continuous f).stronglyMeasurable hfin U
  have hi : U.val = freeGraphDomainInclusion u := (freeGraphDomainInclusion_apply u).symm
  change grossWeylCoefficient f U.val ∈ _ at h
  rw [hi] at h
  exact h

lemma grossGraphWeyl_H0_mem (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (hjj : ∀ i j : Fin 3, MemLp (fun k => (k j : ℂ)*(weylMomentumCoefficient f i (hj i)) k)
      2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2)
    (u : FreeGraphDomain) :
    grossWeylCoefficient f (freeGraphDomainInclusion u) ∈ freeHamiltonian.domain := by
  rw [freeHamiltonian_domain_intersection]
  exact ⟨grossGraphWeyl_second_momentum f hj hjj heven u,grossGraphWeyl_number_mem f u⟩

/- Source argument component: KineticFormula02. -/
def grossGraphCovariantInput (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (hjj : ∀ i j : Fin 3, MemLp (fun k => (k j : ℂ)*(weylMomentumCoefficient f i (hj i)) k)
      2 (volume : Measure GW.Space)) (u : FreeGraphDomain) (j : Fin 3) : FreeFormDomain :=
  ⟨grossFormMomentumMap j (smoothProductGraphToFormMap u)-
    grossFormFieldMap (weylMomentumCoefficient f j (hj j))
      (grossFormRootMap (smoothProductGraphToFormMap u)),
    grossGraph_covariant_momentum_form_mem f hj hjj u j⟩

lemma grossGraphWeyl_first_graph (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (hjj : ∀ i j : Fin 3, MemLp (fun k => (k j : ℂ)*(weylMomentumCoefficient f i (hj i)) k)
      2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2)
    (u : FreeGraphDomain) (j : Fin 3) :
    (grossWeylCoefficient f (freeGraphDomainInclusion u),
      grossWeylCoefficient f (freeFormDomainInclusion (grossGraphCovariantInput f hj hjj u j))) ∈
      (electronMomentumCoordinate j).graph := by
  have h := grossFormWeyl_momentum_graph f j (hj j) heven (smoothProductGraphToFormMap u)
  rw [smoothProductGraphToForm_inclusion] at h
  have heta : freeFormDomainInclusion (grossGraphCovariantInput f hj hjj u j) =
      grossFormMomentumMap j (smoothProductGraphToFormMap u)-
      grossFormFieldMap (weylMomentumCoefficient f j (hj j))
        (grossFormRootMap (smoothProductGraphToFormMap u)) :=
    freeFormDomainInclusion_apply _
  rw [heta]
  exact h

lemma grossGraphWeyl_kinetic_graph (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (hjj : ∀ i j : Fin 3, MemLp (fun k => (k j : ℂ)*(weylMomentumCoefficient f i (hj i)) k)
      2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2)
    (u : FreeGraphDomain) :
    (grossWeylCoefficient f (freeGraphDomainInclusion u),grossWeylCoefficient f
      (∑ j : Fin 3, (grossFormMomentumMap j (grossGraphCovariantInput f hj hjj u j)-
        grossFormFieldMap (weylMomentumCoefficient f j (hj j))
          (grossFormRootMap (grossGraphCovariantInput f hj hjj u j))))) ∈
      freeMomentumSquare.graph := by
  let eta := grossGraphCovariantInput f hj hjj u
  have hv (j : Fin 3) := (commutatorMomentum_graph j _ _).mp
    (grossGraphWeyl_first_graph f hj hjj heven u j)
  have hw (j : Fin 3) := (commutatorMomentum_graph j _ _).mp
    (grossFormWeyl_momentum_graph f j (hj j) heven (eta j))
  have h := momentum_second_sum_graph (E := Carrier) _ _ _ hv hw
  rw [← grossMomentumSquare_operator] at h
  rw [map_sum]
  exact h

/- Source argument component: FieldAlgebra01. -/
lemma grossFormCreator_ae (f : OneBoson) (u : FiberPhysicalRoot) :
    commutatorPhaseCreatorMap f u =ᵐ[volume]
      (fun x => fiberOrdinaryCreator (phaseAt f x) (fiberRootRepresentative u x)) := by
  unfold commutatorPhaseCreatorMap
  rw [← commutatorPhase_kernel]
  change fiberGeneralizedCreator (fiberKernel (phaseAt f) (phaseAt_continuous f).aestronglyMeasurable
    (commutatorPhase_norm_bound f)) u =ᵐ[volume] _
  rw [fiberCreation_identification_root]
  exact fiberCreatorClass_ae _ _ _ _

lemma grossFormAnnihilator_ae (f : OneBoson) (u : FiberPhysicalRoot) :
    commutatorPhaseAnnihilatorMap f u =ᵐ[volume]
      (fun x => fiberOrdinaryAnnihilator (phaseAt f x) (fiberRootRepresentative u x)) := by
  unfold commutatorPhaseAnnihilatorMap
  rw [← commutatorPhase_kernel,fiberAnnihilationMap_identification_root]
  exact fiberAnnihilatorClass_ae _ _ _ _

lemma grossFormFieldMap_ae (f : OneBoson) (u : FiberPhysicalRoot) :
    grossFormFieldMap f u =ᵐ[volume]
      (fun x => ordinaryFieldHalfMap (phaseAt f x) (fiberRootRepresentative u x)) := by
  filter_upwards [grossFormAnnihilator_ae f u,grossFormCreator_ae f u,
    Lp.coeFn_add (commutatorPhaseAnnihilatorMap f u) (commutatorPhaseCreatorMap f u)] with x ha hc hs
  change (commutatorPhaseAnnihilatorMap f u+commutatorPhaseCreatorMap f u) x = _
  rw [hs]
  change commutatorPhaseAnnihilatorMap f u x+commutatorPhaseCreatorMap f u x = _
  rw [ha,hc,fiberOrdinaryField_eq]

lemma grossFormFieldMap_add (f g : OneBoson) (u : FiberPhysicalRoot) :
    grossFormFieldMap (f+g) u = grossFormFieldMap f u+grossFormFieldMap g u := by
  apply Lp.ext
  filter_upwards [grossFormFieldMap_ae (f+g) u,grossFormFieldMap_ae f u,grossFormFieldMap_ae g u,
    Lp.coeFn_add (grossFormFieldMap f u) (grossFormFieldMap g u)] with x h₁ h₂ h₃ h₄
  rw [h₁,h₄]
  change ordinaryFieldHalfMap (phaseAt (f+g) x) _ = grossFormFieldMap f u x+grossFormFieldMap g u x
  rw [h₂,h₃,show phaseAt (f+g) x = phaseAt f x+phaseAt g x from (weylPhaseIsometry x).map_add f g]
  simp only [← fiberOrdinaryField_eq,fiberOrdinaryAnnihilator_add_kernel,fiberOrdinaryCreator_add_kernel]
  abel

lemma grossFormFieldMap_zero (u : FiberPhysicalRoot) : grossFormFieldMap 0 u = 0 := by
  have h := grossFormFieldMap_add 0 0 u
  rw [zero_add] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

lemma grossFormFieldMap_neg (f : OneBoson) (u : FiberPhysicalRoot) :
    grossFormFieldMap (-f) u = -grossFormFieldMap f u := by
  apply eq_neg_iff_add_eq_zero.mpr
  rw [← grossFormFieldMap_add,neg_add_cancel,grossFormFieldMap_zero]

lemma grossFormFieldMap_sub (f g : OneBoson) (u : FiberPhysicalRoot) :
    grossFormFieldMap (f-g) u = grossFormFieldMap f u-grossFormFieldMap g u := by
  rw [sub_eq_add_neg,grossFormFieldMap_add,grossFormFieldMap_neg,sub_eq_add_neg]

/- Source argument component: ExpansionInputs01. -/
def grossGraphMomentumQ (u : FreeGraphDomain) (j : Fin 3) : FreeFormDomain :=
  ⟨electronMomentumCoordinate j (commutatorMomentumInput u j),(grossGraph_momentum_form_bound u j).choose⟩

def grossGraphFieldQ (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (u : FreeGraphDomain) : FreeFormDomain :=
  ⟨grossFormFieldMap f (commutatorGraphRootMap u),grossGraph_field_form_mem f hj u⟩

lemma grossGraphMomentumQ_root (u : FreeGraphDomain) (j : Fin 3) :
    grossFormRootMap (grossGraphMomentumQ u j) = commutatorGraphMomentumRootMap j u := by
  apply Subtype.ext
  exact (grossFormRootMap_value _).trans ((freeFormDomainInclusion_apply _).trans
    (commutatorGraphMomentumRootMap_value j u).symm)

lemma grossGraphFieldQ_momentum (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (u : FreeGraphDomain) (j : Fin 3) :
    grossFormMomentumMap j (grossGraphFieldQ f hj u) =
      commutatorAnnihilatorRightMap f j (hj j) u+commutatorCreatorRightMap f j (hj j) u := by
  have h := grossFormMomentumMap_graph j (grossGraphFieldQ f hj u)
  have he : freeFormDomainInclusion (grossGraphFieldQ f hj u) = grossFormFieldMap f (commutatorGraphRootMap u) :=
    freeFormDomainInclusion_apply _
  rw [he] at h
  exact (electronMomentumCoordinate j).mem_graph_snd_inj h (grossGraph_field_momentum_graph f j (hj j) u) rfl

def grossGraphNumberOne (u : FreeGraphDomain) : (physicalShiftedNumberPower 1).domain :=
  ⟨(show freeGraphOperator.domain from u).val,(freeGraph_shiftedNumber_bound u).choose⟩

lemma grossGraphFieldQ_square (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (u : FreeGraphDomain) :
    grossFormFieldMap f (grossFormRootMap (grossGraphFieldQ f hj u)) =
      generalizedFieldSquare (phaseMultiplicationKernel f) (grossGraphNumberOne u) := by
  obtain ⟨w,hw,hww⟩ := generalizedFieldSquare_graph (phaseMultiplicationKernel f) (grossGraphNumberOne u)
  have h₁ := grossFormFieldMap_graph f (commutatorGraphRootMap u)
  rw [commutatorGraphRootMap_value] at h₁
  have hu : (grossGraphNumberOne u).val = freeGraphDomainInclusion u :=
    (freeGraphDomainInclusion_apply u).symm
  rw [hu] at hw
  have hwval := (generalizedField (phaseMultiplicationKernel f)).mem_graph_snd_inj h₁ hw rfl
  have h₂ := grossFormFieldMap_graph f (grossFormRootMap (grossGraphFieldQ f hj u))
  have hval : (fiberPhysicalRootInput (grossFormRootMap (grossGraphFieldQ f hj u))).val =
      grossFormFieldMap f (commutatorGraphRootMap u) :=
    (grossFormRootMap_value _).trans (freeFormDomainInclusion_apply _)
  rw [hval,hwval] at h₂
  exact (generalizedField (phaseMultiplicationKernel f)).mem_graph_snd_inj h₂ hww rfl

/- Source argument component: KineticExpansion01. -/
lemma grossGraphCovariantInput_eq (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (hjj : ∀ i j : Fin 3, MemLp (fun k => (k j : ℂ)*(weylMomentumCoefficient f i (hj i)) k)
      2 (volume : Measure GW.Space)) (u : FreeGraphDomain) (j : Fin 3) :
    grossGraphCovariantInput f hj hjj u j = grossGraphMomentumQ u j-
      grossGraphFieldQ (weylMomentumCoefficient f j (hj j)) (hjj j) u := by
  apply Subtype.ext
  change grossFormMomentumMap j (smoothProductGraphToFormMap u)-
    grossFormFieldMap (weylMomentumCoefficient f j (hj j))
      (grossFormRootMap (smoothProductGraphToFormMap u)) = _
  rw [grossGraph_to_form_root,grossGraph_to_form_momentum]
  rfl

lemma grossGraphCovariant_square_expansion (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (hjj : ∀ i j : Fin 3, MemLp (fun k => (k j : ℂ)*(weylMomentumCoefficient f i (hj i)) k)
      2 (volume : Measure GW.Space)) (u : FreeGraphDomain) (j : Fin 3) :
    grossFormMomentumMap j (grossGraphCovariantInput f hj hjj u j)-
      grossFormFieldMap (weylMomentumCoefficient f j (hj j))
        (grossFormRootMap (grossGraphCovariantInput f hj hjj u j)) =
    grossFormMomentumMap j (grossGraphMomentumQ u j)-
      2 • grossFormFieldMap (weylMomentumCoefficient f j (hj j)) (commutatorGraphMomentumRootMap j u)-
      commutatorPhaseAnnihilatorMap (weylMomentumCoefficient (weylMomentumCoefficient f j (hj j)) j (hjj j j))
        (commutatorGraphRootMap u)+
      commutatorPhaseCreatorMap (weylMomentumCoefficient (weylMomentumCoefficient f j (hj j)) j (hjj j j))
        (commutatorGraphRootMap u)+
      generalizedFieldSquare (phaseMultiplicationKernel (weylMomentumCoefficient f j (hj j))) (grossGraphNumberOne u) := by
  rw [grossGraphCovariantInput_eq,map_sub,map_sub,map_sub,grossGraphMomentumQ_root,
    grossGraphFieldQ_momentum,grossGraphFieldQ_square]
  simp only [commutatorAnnihilatorRightMap,commutatorCreatorRightMap,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.add_apply,sub_apply,grossFormFieldMap,two_smul]
  abel

lemma grossGraph_momentum_square_sum (u : FreeGraphDomain) :
    (freeGraphDomainInclusion u,∑ j : Fin 3, grossFormMomentumMap j (grossGraphMomentumQ u j)) ∈
      freeMomentumSquare.graph := by
  have hv (j : Fin 3) := (commutatorMomentum_graph j _ _).mp
    ((electronMomentumCoordinate j).mem_graph (commutatorMomentumInput u j))
  have hw (j : Fin 3) := grossFormMomentumMap_graph j (grossGraphMomentumQ u j)
  have hval (j : Fin 3) : freeFormDomainInclusion (grossGraphMomentumQ u j) =
      electronMomentumCoordinate j (commutatorMomentumInput u j) := freeFormDomainInclusion_apply _
  have hw' (j : Fin 3) := (commutatorMomentum_graph j _ _).mp ((hval j) ▸ hw j)
  have h := momentum_second_sum_graph (E := Carrier) _ _ _ hv hw'
  rw [← grossMomentumSquare_operator] at h
  simpa only [freeGraphDomainInclusion_apply] using h

/- Source argument component: CoefficientSums01. -/
lemma grossFormCreator_add (f g : OneBoson) (u : FiberPhysicalRoot) :
    commutatorPhaseCreatorMap (f+g) u = commutatorPhaseCreatorMap f u+commutatorPhaseCreatorMap g u := by
  apply Lp.ext
  filter_upwards [grossFormCreator_ae (f+g) u,grossFormCreator_ae f u,grossFormCreator_ae g u,
    Lp.coeFn_add (commutatorPhaseCreatorMap f u) (commutatorPhaseCreatorMap g u)] with x h₁ h₂ h₃ h₄
  rw [h₁,h₄]
  change _ = commutatorPhaseCreatorMap f u x+commutatorPhaseCreatorMap g u x
  rw [h₂,h₃,show phaseAt (f+g) x = phaseAt f x+phaseAt g x from (weylPhaseIsometry x).map_add f g,
    fiberOrdinaryCreator_add_kernel]

lemma grossFormCreator_zero (u : FiberPhysicalRoot) : commutatorPhaseCreatorMap 0 u = 0 := by
  have h := grossFormCreator_add 0 0 u
  rw [zero_add] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

def grossFormCreatorCoefficientAdd (u : FiberPhysicalRoot) : OneBoson →+ Physical where
  toFun f := commutatorPhaseCreatorMap f u
  map_zero' := grossFormCreator_zero u
  map_add' f g := grossFormCreator_add f g u

lemma grossFormCreator_sum (fs : Fin 3 → OneBoson) (u : FiberPhysicalRoot) :
    commutatorPhaseCreatorMap (∑ j,fs j) u = ∑ j,commutatorPhaseCreatorMap (fs j) u :=
  map_sum (grossFormCreatorCoefficientAdd u) fs Finset.univ

lemma grossFormAnnihilator_add (f g : OneBoson) (u : FiberPhysicalRoot) :
    commutatorPhaseAnnihilatorMap (f+g) u = commutatorPhaseAnnihilatorMap f u+commutatorPhaseAnnihilatorMap g u := by
  apply Lp.ext
  filter_upwards [grossFormAnnihilator_ae (f+g) u,grossFormAnnihilator_ae f u,grossFormAnnihilator_ae g u,
    Lp.coeFn_add (commutatorPhaseAnnihilatorMap f u) (commutatorPhaseAnnihilatorMap g u)] with x h₁ h₂ h₃ h₄
  rw [h₁,h₄]
  change _ = commutatorPhaseAnnihilatorMap f u x+commutatorPhaseAnnihilatorMap g u x
  rw [h₂,h₃,show phaseAt (f+g) x = phaseAt f x+phaseAt g x from (weylPhaseIsometry x).map_add f g,
    fiberOrdinaryAnnihilator_add_kernel]

lemma grossFormAnnihilator_zero (u : FiberPhysicalRoot) : commutatorPhaseAnnihilatorMap 0 u = 0 := by
  have h := grossFormAnnihilator_add 0 0 u
  rw [zero_add] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

def grossFormAnnihilatorCoefficientAdd (u : FiberPhysicalRoot) : OneBoson →+ Physical where
  toFun f := commutatorPhaseAnnihilatorMap f u
  map_zero' := grossFormAnnihilator_zero u
  map_add' f g := grossFormAnnihilator_add f g u

lemma grossFormAnnihilator_sum (fs : Fin 3 → OneBoson) (u : FiberPhysicalRoot) :
    commutatorPhaseAnnihilatorMap (∑ j,fs j) u = ∑ j,commutatorPhaseAnnihilatorMap (fs j) u :=
  map_sum (grossFormAnnihilatorCoefficientAdd u) fs Finset.univ

/- Source argument component: RootBound01. -/
lemma grossFormRootMap_norm (u : FreeFormDomain) : ‖grossFormRootMap u‖ ≤ ‖u‖ := by
  rw [← fiberPhysicalRoot_norm,freeFormDomain_norm]
  exact (grossForm_shiftedRoot_bound u).choose_spec

lemma grossFormWeyl_root_map (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2) (u : FreeFormDomain) :
    grossFormRootMap (grossFormWeylInput f hj heven u) =
      fiberWeylPhysicalGraphMap (1/2) (by norm_num) (by norm_num) (phaseAt f)
        (phaseAt_continuous f).stronglyMeasurable ‖f‖ (commutatorPhase_norm_bound f) (grossFormRootMap u) := by
  let V := fiberWeylPhysicalGraphMap (1/2) (by norm_num) (by norm_num) (phaseAt f)
    (phaseAt_continuous f).stronglyMeasurable ‖f‖ (commutatorPhase_norm_bound f) (grossFormRootMap u)
  have ht : (fiberPhysicalRootInput V).val = grossWeylCoefficient f (freeFormDomainInclusion u) := by
    have h := fiberWeylPhysicalGraphMap_inclusion (1/2) (by norm_num) (by norm_num) (phaseAt f)
      (phaseAt_continuous f).stronglyMeasurable ‖f‖ (commutatorPhase_norm_bound f) (grossFormRootMap u)
    change (fiberPhysicalRootInput V).val = grossWeylCoefficient f (fiberPhysicalRootInput (grossFormRootMap u)).val at h
    exact h.trans (congrArg (grossWeylCoefficient f) (grossFormRootMap_value u))
  apply Subtype.ext
  exact (grossFormRootMap_value _).trans ((grossFormWeylInput_value f hj heven u).trans ht.symm)

lemma grossFormWeyl_root_bound (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2) (u : FreeFormDomain) :
    ‖grossFormRootMap (grossFormWeylInput f hj heven u)‖ ≤ (1+‖f‖)*‖u‖ := by
  rw [grossFormWeyl_root_map]
  have h := fiberWeylPhysicalGraphMap_bound (1/2) (by norm_num) (by norm_num) (phaseAt f)
    (phaseAt_continuous f).stronglyMeasurable ‖f‖ (commutatorPhase_norm_bound f) (grossFormRootMap u)
  have he : (2:ℝ)*(1/2)=1 := by norm_num
  rw [he,Real.rpow_one] at h
  exact h.trans (mul_le_mul_of_nonneg_left (grossFormRootMap_norm u) (by positivity))

/- Source argument component: MomentumNorm02. -/
lemma grossFormMomentum_norm_sq (u : FreeFormDomain) :
    ‖freeMomentumModulus ⟨(show freeFormOperator.domain from u).val,freeForm_momentum_mem u⟩‖^2 =
      ∑ j : Fin 3, ‖grossFormMomentumMap j u‖^2 := by
  let U := (show freeFormOperator.domain from u).val
  have hp : U ∈ (physicalSectorMultiplier (fun _ q => ‖q‖^(1+(0:ℝ)))).domain := by
    simpa only [U,freeMomentumModulus,add_zero,Real.rpow_one] using freeForm_momentum_mem u
  have hj (j : Fin 3) : U ∈ (physicalSectorMultiplier (fun _ q => q j)).domain :=
    (grossFormMomentumInput j u).property
  have h0 (j : Fin 3) : physicalSectorMultiplier (fun _ q => q j) ⟨U,hj j⟩ ∈
      (physicalSectorMultiplier (fun _ q => ‖q‖^(0:ℝ))).domain := by
    rw [radialPower_zero]
    change _ ∈ (⊤ : Submodule ℂ Physical)
    trivial
  have h := radial_component_norm_sq 0 (by norm_num) ⟨U,hp⟩ hj h0
  have he : physicalSectorMultiplier (fun _ q => ‖q‖^(1+(0:ℝ))) = freeMomentumModulus := by
    simp only [add_zero,Real.rpow_one]
    rfl
  have hl := partialMap_action_eq_of_same_input he
    (⟨U,hp⟩ : (physicalSectorMultiplier (fun _ q => ‖q‖^(1+(0:ℝ)))).domain)
    (⟨U,freeForm_momentum_mem u⟩ : freeMomentumModulus.domain) rfl
  rw [hl] at h
  refine h.trans (Finset.sum_congr rfl (fun j _ => ?_))
  have hz := partialMap_action_eq_of_same_input radialPower_zero
    (⟨physicalSectorMultiplier (fun _ q => q j) ⟨U,hj j⟩,h0 j⟩ :
      (physicalSectorMultiplier (fun _ q => ‖q‖^(0:ℝ))).domain)
    (⟨physicalSectorMultiplier (fun _ q => q j) ⟨U,hj j⟩,Submodule.mem_top⟩ :
      ((LinearMap.id : Physical →ₗ[ℂ] Physical).toPMap ⊤).domain) rfl
  rw [hz]
  rfl

lemma grossFormMomentum_norm_sq_le (u : FreeFormDomain) :
    (∑ j : Fin 3, ‖grossFormMomentumMap j u‖^2) ≤ ‖u‖^2 := by
  rw [← grossFormMomentum_norm_sq]
  have h := freeForm_norm_identity u
  dsimp only at h
  nlinarith [sq_nonneg ‖(show freeFormOperator.domain from u).val‖,
    sq_nonneg ‖freeRootNumber ⟨(show freeFormOperator.domain from u).val,freeForm_rootNumber_mem u⟩‖]

/- Source argument component: NormSplit01. -/
lemma grossFormWeight_split (n : ℕ) (q : GW.Space) :
    freeFormWeight n q^2 = (Real.sqrt ((n:ℝ)+1))^2+‖q‖^2 := by
  rw [freeFormWeight_sq,Real.sq_sqrt (by positivity : 0 ≤ (n:ℝ)+1)]
  unfold freeGraphWeight freeEnergySymbol
  ring

lemma grossFormMass_split (U : Physical) :
    fourierWeightMass freeFormWeight U =
      fourierWeightMass (fun n _ => Real.sqrt ((n:ℝ)+1)) U+fourierWeightMass (fun _ q => ‖q‖) U := by
  have he (n : ℕ) (q : GW.Space) : fourierWeightSquare freeFormWeight U n q =
      fourierWeightSquare (fun n _ => Real.sqrt ((n:ℝ)+1)) U n q+
        fourierWeightSquare (fun _ q => ‖q‖) U n q := by
    unfold fourierWeightSquare
    simp only [norm_smul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
    rw [← ENNReal.ofReal_add (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (mul_nonneg (sq_nonneg _) (sq_nonneg _)),← add_mul,grossFormWeight_split]
  unfold fourierWeightMass
  simp_rw [he]
  have hi (n : ℕ) :
      (∫⁻ q, fourierWeightSquare (fun n _ => Real.sqrt ((n:ℝ)+1)) U n q+
        fourierWeightSquare (fun _ q => ‖q‖) U n q ∂volume) =
      (∫⁻ q, fourierWeightSquare (fun n _ => Real.sqrt ((n:ℝ)+1)) U n q ∂volume)+
        ∫⁻ q, fourierWeightSquare (fun _ q => ‖q‖) U n q ∂volume :=
    lintegral_add_left' (fourierWeightSquare_aemeasurable _ (fun _ => measurable_const) U n) _
  simp_rw [hi]
  exact ENNReal.tsum_add

lemma grossForm_norm_split (u : freeFormOperator.domain)
    (hn : u.val ∈ (physicalShiftedNumberPower (1/2)).domain) :
    ‖freeFormOperator u‖^2 = ‖physicalShiftedNumberPower (1/2) ⟨u.val,hn⟩‖^2+
      ‖freeMomentumModulus ⟨u.val,freeForm_momentum_mem u⟩‖^2 := by
  have hr : u.val ∈ (physicalSectorMultiplier (fun n _ => Real.sqrt ((n:ℝ)+1))).domain := by
    rw [← physicalShiftedNumberHalf_eq_sectorMultiplier]
    exact hn
  have he := grossFormMass_split u.val
  rw [fourierWeightMass_norm freeFormWeight u,
    fourierWeightMass_norm (fun n _ => Real.sqrt ((n:ℝ)+1)) ⟨u.val,hr⟩,
    fourierWeightMass_norm (fun _ q => ‖q‖) ⟨u.val,freeForm_momentum_mem u⟩,
    ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)] at he
  have h := (ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _))).mp he
  have hh := partialMap_action_eq_of_same_input physicalShiftedNumberHalf_eq_sectorMultiplier
    (⟨u.val,hn⟩ : (physicalShiftedNumberPower (1/2)).domain)
    (⟨u.val,hr⟩ : (physicalSectorMultiplier (fun n _ => Real.sqrt ((n:ℝ)+1))).domain) rfl
  rw [← hh] at h
  exact h

/- Source argument component: Radial01. -/
lemma grossForm_radial_density (f : OneBoson) (k : GW.Space) :
    ‖(‖k‖:ℂ)*f k‖^2 = ∑ j : Fin 3, ‖(k j:ℂ)*f k‖^2 := by
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
  rw [EuclideanSpace.real_norm_sq_eq,Finset.sum_mul]

lemma grossForm_radial_memLp (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) :
    MemLp (fun k => (‖k‖:ℂ)*f k) 2 (volume : Measure GW.Space) := by
  have hm : Measurable (fun k : GW.Space => (‖k‖:ℂ)*f k) :=
    (Complex.continuous_ofReal.measurable.comp measurable_norm).mul (Lp.stronglyMeasurable f).measurable
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  have hi := integrable_finsetSum Finset.univ (fun j _ => (hj j).integrable_norm_pow (p := 2) (by norm_num))
  simpa only [← grossForm_radial_density] using hi

def grossFormRadialCoefficient (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) : OneBoson :=
  (grossForm_radial_memLp f hj).toLp (fun k => (‖k‖:ℂ)*f k)

lemma grossFormRadialCoefficient_ae (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) :
    grossFormRadialCoefficient f hj =ᵐ[volume] fun k => (‖k‖:ℂ)*f k := MemLp.coeFn_toLp _

lemma grossFormRadialCoefficient_norm_sq (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) :
    ‖grossFormRadialCoefficient f hj‖^2 = ∑ j : Fin 3, ‖weylMomentumCoefficient f j (hj j)‖^2 := by
  rw [GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
  calc
    _ = ∫ k, ∑ j : Fin 3, ‖(k j:ℂ)*f k‖^2 ∂volume := by
      apply integral_congr_ae
      filter_upwards [grossFormRadialCoefficient_ae f hj] with k hk
      rw [hk,grossForm_radial_density]
    _ = ∑ j : Fin 3, ∫ k, ‖(k j:ℂ)*f k‖^2 ∂volume :=
      integral_finsetSum _ (fun j _ => (hj j).integrable_norm_pow (p := 2) (by norm_num))
    _ = _ := Finset.sum_congr rfl (fun j _ => by
      rw [GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
      apply integral_congr_ae
      filter_upwards [weylMomentumCoefficient_ae f j (hj j)] with k hk
      rw [hk])

lemma grossForm_radial_original_sq_bound (α K : ℝ) (k : GW.Space) :
    ‖(‖k‖:ℂ)*(b α K k:ℂ)‖^2 ≤ grossCoefficientMajorant α K k := by
  rw [norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,mul_pow,sq_abs,sq_abs]
  by_cases hk : K < ‖k‖
  · rw [grossCoefficientMajorant,indicator_of_mem hk]
    have he : (1+‖k‖^2)*(b α K k)^2 = (v α k)^2/(1+‖k‖^2) := by
      rw [b,if_pos hk]
      field_simp
      <;> ring
    exact (mul_le_mul_of_nonneg_right (by linarith : ‖k‖^2 ≤ 1+‖k‖^2) (sq_nonneg _)).trans_eq he
  · rw [b,if_neg hk,grossCoefficientMajorant,indicator_of_notMem hk]
    norm_num

lemma grossForm_radial_original_bound (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    ‖grossFormRadialCoefficient (grossDressingCoefficient α K hα hK)
      (grossForm_momentum_memLp α K hα hK)‖^2 ≤ coefficientDTail α K := by
  rw [GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
  calc
    _ ≤ ∫ k, grossCoefficientMajorant α K k ∂volume := by
      apply integral_mono_ae
        ((Lp.memLp (grossFormRadialCoefficient (grossDressingCoefficient α K hα hK)
          (grossForm_momentum_memLp α K hα hK))).integrable_norm_pow (p := 2) (by norm_num))
        (grossCoefficientMajorant_integrable α K hα hK)
      filter_upwards [grossFormRadialCoefficient_ae (grossDressingCoefficient α K hα hK)
        (grossForm_momentum_memLp α K hα hK),grossDressingCoefficient_ae α K hα hK] with k h₁ h₂
      rw [h₁,h₂]
      exact grossForm_radial_original_sq_bound α K k
    _ = coefficientETail α K := grossCoefficientMajorant_integral α K hα hK
    _ ≤ _ := coefficientETail_le_D α K hα hK

/- Source argument component: FiniteNorm01. -/
lemma grossForm_finite_minkowski (p g : Fin 3 → ℝ) (R : ℝ) (hR : 0 ≤ R) :
    (∑ j, (p j+2*g j*R)^2) ≤
      (Real.sqrt (∑ j, (p j)^2)+2*Real.sqrt (∑ j, (g j)^2)*R)^2 := by
  have hP : 0 ≤ ∑ j, (p j)^2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hG : 0 ≤ ∑ j, (g j)^2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have he : (∑ j, (p j+2*g j*R)^2) =
      (∑ j, (p j)^2)+4*R*(∑ j, p j*g j)+4*R^2*(∑ j, (g j)^2) := by
    have hx (j : Fin 3) : (p j+2*g j*R)^2 = (p j)^2+4*R*(p j*g j)+4*R^2*(g j)^2 := by ring
    simp_rw [hx,Finset.sum_add_distrib,← Finset.mul_sum]
  rw [he]
  calc
    _ ≤ (∑ j, (p j)^2)+4*R*(Real.sqrt (∑ j, (p j)^2)*Real.sqrt (∑ j, (g j)^2))+
        4*R^2*(∑ j, (g j)^2) := by
      gcongr
      exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = (Real.sqrt (∑ j, (p j)^2))^2+
        4*R*(Real.sqrt (∑ j, (p j)^2)*Real.sqrt (∑ j, (g j)^2))+
        4*R^2*(Real.sqrt (∑ j, (g j)^2))^2 := by rw [Real.sq_sqrt hP,Real.sq_sqrt hG]
    _ = _ := by ring

/- Source argument component: Uniform03. -/
lemma grossForm_norm_coordinates (u : FreeFormDomain) :
    ‖u‖^2 = ‖grossFormRootMap u‖^2+∑ j : Fin 3, ‖grossFormMomentumMap j u‖^2 := by
  have h := grossForm_norm_split (show freeFormOperator.domain from u) (grossForm_shiftedRoot_bound u).choose
  have hr : ‖physicalShiftedNumberPower (1/2) ⟨(show freeFormOperator.domain from u).val,
      (grossForm_shiftedRoot_bound u).choose⟩‖ = ‖grossFormRootMap u‖ := fiberPhysicalRoot_norm _
  calc
    _ = ‖freeFormOperator u‖^2 := congrArg (fun r : ℝ => r^2) (freeFormDomain_norm u)
    _ = _ := h.trans (by rw [hr,grossFormMomentum_norm_sq])

lemma grossFormWeyl_momentum_action (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2)
    (u : FreeFormDomain) (j : Fin 3) :
    grossFormMomentumMap j (grossFormWeylInput f hj heven u) = grossFormWeylRightMap f j (hj j) u := by
  have h := grossFormMomentumMap_graph j (grossFormWeylInput f hj heven u)
  rw [grossFormWeylInput_value] at h
  exact (electronMomentumCoordinate j).mem_graph_snd_inj h (grossFormWeyl_momentum_graph f j (hj j) heven u) rfl

lemma grossFormWeyl_momentum_bound (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2) (u : FreeFormDomain) :
    (∑ j : Fin 3, ‖grossFormMomentumMap j (grossFormWeylInput f hj heven u)‖^2) ≤
      ((1+2*‖grossFormRadialCoefficient f hj‖)*‖u‖)^2 := by
  let p := fun j : Fin 3 => ‖grossFormMomentumMap j u‖
  let g := fun j : Fin 3 => ‖weylMomentumCoefficient f j (hj j)‖
  let R := ‖grossFormRootMap u‖
  have hc (j : Fin 3) : ‖grossFormMomentumMap j (grossFormWeylInput f hj heven u)‖ ≤ p j+2*g j*R := by
    rw [grossFormWeyl_momentum_action]
    change ‖grossWeylCoefficient f (grossFormMomentumMap j u-
      grossFormFieldMap (weylMomentumCoefficient f j (hj j)) (grossFormRootMap u))‖ ≤ _
    rw [LinearIsometryEquiv.norm_map]
    change ‖grossFormMomentumMap j u-grossFormFieldMap (weylMomentumCoefficient f j (hj j)) (grossFormRootMap u)‖ ≤
      ‖grossFormMomentumMap j u‖+2*‖weylMomentumCoefficient f j (hj j)‖*‖grossFormRootMap u‖
    have hb := grossFormFieldMap_bound (weylMomentumCoefficient f j (hj j)) (grossFormRootMap u)
    exact (norm_sub_le (grossFormMomentumMap j u)
      (grossFormFieldMap (weylMomentumCoefficient f j (hj j)) (grossFormRootMap u))).trans
      (add_le_add le_rfl hb)
  have hP : Real.sqrt (∑ j, (p j)^2) ≤ ‖u‖ := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (norm_nonneg u)).mp
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
    exact grossFormMomentum_norm_sq_le u
  have hG : Real.sqrt (∑ j, (g j)^2) = ‖grossFormRadialCoefficient f hj‖ := by
    change Real.sqrt (∑ j : Fin 3, ‖weylMomentumCoefficient f j (hj j)‖^2) = _
    rw [← grossFormRadialCoefficient_norm_sq f hj,Real.sqrt_sq (norm_nonneg _)]
  calc
    _ ≤ ∑ j : Fin 3, (p j+2*g j*R)^2 := Finset.sum_le_sum (fun j _ =>
      pow_le_pow_left₀ (norm_nonneg _) (hc j) 2)
    _ ≤ (Real.sqrt (∑ j, (p j)^2)+2*Real.sqrt (∑ j, (g j)^2)*R)^2 :=
      grossForm_finite_minkowski p g R (norm_nonneg _)
    _ ≤ (‖u‖+2*‖grossFormRadialCoefficient f hj‖*‖u‖)^2 := by
      rw [hG]
      apply pow_le_pow_left₀ (by positivity)
      exact add_le_add hP (mul_le_mul_of_nonneg_left (grossFormRootMap_norm u) (by positivity))
    _ = _ := by ring

def grossFormWeylBound (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) : ℝ :=
  Real.sqrt ((1+‖f‖)^2+(1+2*‖grossFormRadialCoefficient f hj‖)^2)

lemma grossFormWeyl_bound (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2) (u : FreeFormDomain) :
    ‖grossFormWeylInput f hj heven u‖ ≤ grossFormWeylBound f hj*‖u‖ := by
  have hsq : ‖grossFormWeylInput f hj heven u‖^2 ≤
      ((1+‖f‖)^2+(1+2*‖grossFormRadialCoefficient f hj‖)^2)*‖u‖^2 := by
    rw [grossForm_norm_coordinates]
    calc
      _ ≤ ((1+‖f‖)*‖u‖)^2+((1+2*‖grossFormRadialCoefficient f hj‖)*‖u‖)^2 :=
        add_le_add (pow_le_pow_left₀ (norm_nonneg _) (grossFormWeyl_root_bound f hj heven u) 2)
          (grossFormWeyl_momentum_bound f hj heven u)
      _ = _ := by ring
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg u))).mp
  change _ ≤ (Real.sqrt ((1+‖f‖)^2+(1+2*‖grossFormRadialCoefficient f hj‖)^2)*‖u‖)^2
  rw [mul_pow,Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
  exact hsq

/- Source argument component: MixedMass03. -/
lemma grossMixed_coordinate_mass (c : ℕ → ℝ) (u : Physical) :
    fourierWeightMass (fun n q => c n*‖q‖) u =
      ∑ j : Fin 3, fourierWeightMass (fun n q => c n*q j) u := by
  have hmeas (n : ℕ) (j : Fin 3) : Measurable (fun q : GW.Space => c n*q j) :=
    measurable_const.mul (PiLp.continuous_apply 2 _ j).measurable
  have he (n : ℕ) (q : GW.Space) : fourierWeightSquare (fun n q => c n*‖q‖) u n q =
      ∑ j : Fin 3, fourierWeightSquare (fun n q => c n*q j) u n q := by
    let z : ℝ := ‖freeFourierRepresentation u n q‖
    let a : ℝ := c n
    let f (j : Fin 3) : ℝ := a^2 * (q j)^2 * z^2
    have hcalc : (a * ‖q‖)^2 * z^2 = ∑ j, f j := by
      rw [mul_pow,EuclideanSpace.real_norm_sq_eq q,Finset.mul_sum,Finset.sum_mul]
    calc
      _ = ENNReal.ofReal ((a * ‖q‖)^2 * z^2) := by
        unfold fourierWeightSquare
        rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
      _ = ENNReal.ofReal (∑ j, f j) := congrArg ENNReal.ofReal hcalc
      _ = ∑ j, ENNReal.ofReal (f j) :=
        ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (mul_nonneg (sq_nonneg a) (sq_nonneg (q j))) (sq_nonneg z))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        unfold f a z fourierWeightSquare
        simp only [norm_smul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
  let F (n : ℕ) (j : Fin 3) (q : GW.Space) := fourierWeightSquare (fun n q => c n*q j) u n q
  let M (n : ℕ) (j : Fin 3) := ∫⁻ q, F n j q ∂(volume : Measure GW.Space)
  have hi (n : ℕ) : (∫⁻ q, fourierWeightSquare (fun n q => c n*‖q‖) u n q
      ∂(volume : Measure GW.Space)) = ∑ j : Fin 3, M n j := by
    calc
      _ = ∫⁻ q, ∑ j : Fin 3, F n j q ∂(volume : Measure GW.Space) :=
        lintegral_congr_ae (Eventually.of_forall (he n))
      _ = _ := lintegral_finsetSum' Finset.univ
        (fun j _ => fourierWeightSquare_aemeasurable _ (fun n => hmeas n j) u n)
  change (∑' n, ∫⁻ q, fourierWeightSquare (fun n q => c n*‖q‖) u n q ∂(volume : Measure GW.Space)) =
    ∑ j : Fin 3, ∑' n, M n j
  calc
    _ = ∑' n, ∑ j : Fin 3, M n j := tsum_congr hi
    _ = ∑' n, ∑' j : Fin 3, M n j := tsum_congr (fun n => (tsum_fintype (M n)).symm)
    _ = ∑' j : Fin 3, ∑' n, M n j := tsum_comm
    _ = _ := tsum_fintype _

/- Source argument component: MixedBound03. -/
lemma grossMixed_component_mem (u : freeGraphOperator.domain) (j : Fin 3) :
    u.val ∈ (physicalSectorMultiplier (mixedNumberMomentumComponentSymbol j)).domain := by
  apply (physicalSectorMultiplier_domination (mixedNumberMomentumComponentSymbol j) freeGraphWeight
    (fun _ => measurable_const.mul (electronCoordinate_measurable j)) (by norm_num : (0:ℝ) ≤ 1/2) ?_ u).choose
  intro n q
  rw [mixedNumberMomentumComponentSymbol,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (mul_le_mul_of_nonneg_left (electronCoordinate_abs_le q j) (Real.sqrt_nonneg _)).trans
    (by simpa only [mixedNumberMomentumSymbol,abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))]
      using mixedNumberMomentum_bound n q)

lemma grossMixed_component_action (u : freeGraphOperator.domain) (j : Fin 3) :
    physicalSectorMultiplier (mixedNumberMomentumComponentSymbol j) ⟨u.val,grossMixed_component_mem u j⟩ =
      physicalShiftedNumberPower (1/2) (freeGraphMomentumShiftedRoot u j) := by
  obtain ⟨hn,he⟩ := physicalSectorMultiplier_composition (fun _ q => q j)
    (fun n _ => Real.sqrt ((n:ℝ)+1)) u.val (freeGraphMomentumInput u j).property (grossMixed_component_mem u j)
  let v := physicalSectorMultiplier (fun _ q => q j) ⟨u.val,(freeGraphMomentumInput u j).property⟩
  let w := physicalSectorMultiplier (fun n _ => Real.sqrt ((n:ℝ)+1)) ⟨v,hn⟩
  have hg : (v,w) ∈ (physicalShiftedNumberPower (1/2)).graph :=
    (congrArg (fun A : Physical →ₗ.[ℂ] Physical => (v,w) ∈ A.graph)
      physicalShiftedNumberHalf_eq_sectorMultiplier).mpr
      ((physicalSectorMultiplier (fun n _ => Real.sqrt ((n:ℝ)+1))).mem_graph ⟨v,hn⟩)
  exact he.symm.trans ((physicalShiftedNumberPower (1/2)).mem_graph_snd_inj hg
    ((physicalShiftedNumberPower (1/2)).mem_graph (freeGraphMomentumShiftedRoot u j)) rfl)

lemma grossMixed_collective_bound (u : freeGraphOperator.domain) :
    Real.sqrt (∑ j : Fin 3, ‖physicalShiftedNumberPower (1/2) (freeGraphMomentumShiftedRoot u j)‖^2) ≤
      (1/2:ℝ)*‖freeGraphOperator u‖ := by
  obtain ⟨hm,hb⟩ := freeGraph_mixed_momentum u
  have hmass := grossMixed_coordinate_mass (fun n => Real.sqrt ((n:ℝ)+1)) u.val
  have hleft : fourierWeightMass (fun n q => Real.sqrt ((n:ℝ)+1)*‖q‖) u.val =
      ENNReal.ofReal (‖physicalSectorMultiplier mixedNumberMomentumSymbol ⟨u.val,hm⟩‖^2) :=
    fourierWeightMass_norm mixedNumberMomentumSymbol ⟨u.val,hm⟩
  have hright (j : Fin 3) : fourierWeightMass (fun n q => Real.sqrt ((n:ℝ)+1)*q j) u.val =
      ENNReal.ofReal (‖physicalShiftedNumberPower (1/2) (freeGraphMomentumShiftedRoot u j)‖^2) := by
    have h := fourierWeightMass_norm (mixedNumberMomentumComponentSymbol j)
      ⟨u.val,grossMixed_component_mem u j⟩
    rw [grossMixed_component_action] at h
    exact h
  rw [hleft] at hmass
  simp_rw [hright] at hmass
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg
    ‖physicalShiftedNumberPower (1/2) (freeGraphMomentumShiftedRoot u j)‖)] at hmass
  have he := congrArg ENNReal.toReal hmass
  rw [ENNReal.toReal_ofReal (sq_nonneg _),
    ENNReal.toReal_ofReal (Finset.sum_nonneg (fun _ _ => sq_nonneg _))] at he
  rw [← he,Real.sqrt_sq (norm_nonneg _)]
  exact hb

/- Source argument component: FieldMomentumBound02. -/
lemma grossGraphMomentumRoot_norm (u : FreeGraphDomain) (j : Fin 3) :
    ‖commutatorGraphMomentumRootMap j u‖ =
      ‖physicalShiftedNumberPower (1/2) (freeGraphMomentumShiftedRoot u j)‖ := by
  rw [← fiberPhysicalRoot_norm]
  have he : fiberPhysicalRootInput (commutatorGraphMomentumRootMap j u) =
      freeGraphMomentumShiftedRoot u j := Subtype.ext rfl
  rw [he]

lemma grossGraph_field_momentum_bound (fs : Fin 3 → OneBoson) (u : FreeGraphDomain) :
    ‖∑ j : Fin 3, grossFormFieldMap (fs j) (commutatorGraphMomentumRootMap j u)‖ ≤
      Real.sqrt (∑ j : Fin 3, ‖fs j‖^2)*‖u‖ := by
  have hb := grossMixed_collective_bound (show freeGraphOperator.domain from u)
  have hs : (∑ j : Fin 3, ‖fs j‖*‖commutatorGraphMomentumRootMap j u‖) ≤
      Real.sqrt (∑ j : Fin 3, ‖fs j‖^2)*
        Real.sqrt (∑ j : Fin 3, ‖physicalShiftedNumberPower (1/2) (freeGraphMomentumShiftedRoot u j)‖^2) := by
    simp_rw [grossGraphMomentumRoot_norm]
    exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  calc
    _ ≤ ∑ j : Fin 3, ‖grossFormFieldMap (fs j) (commutatorGraphMomentumRootMap j u)‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin 3, 2*‖fs j‖*‖commutatorGraphMomentumRootMap j u‖ :=
      Finset.sum_le_sum (fun j _ => grossFormFieldMap_bound (fs j) (commutatorGraphMomentumRootMap j u))
    _ = 2*(∑ j : Fin 3, ‖fs j‖*‖commutatorGraphMomentumRootMap j u‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ 2*(Real.sqrt (∑ j : Fin 3, ‖fs j‖^2)*
        Real.sqrt (∑ j : Fin 3, ‖physicalShiftedNumberPower (1/2) (freeGraphMomentumShiftedRoot u j)‖^2)) :=
      mul_le_mul_of_nonneg_left hs (by norm_num)
    _ ≤ 2*(Real.sqrt (∑ j : Fin 3, ‖fs j‖^2)*((1/2:ℝ)*‖freeGraphOperator u‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)) (by norm_num)
    _ = _ := by rw [freeGraphDomain_norm]; ring

/- Source argument component: KineticBound05. -/
lemma grossGraph_momentum_square_sum_bound (u : FreeGraphDomain) :
    ‖∑ j : Fin 3,grossFormMomentumMap j (grossGraphMomentumQ u j)‖ ≤ ‖u‖ := by
  obtain ⟨hm,hb⟩ := physicalSectorMultiplier_domination (fun _ q => ‖q‖^2) freeGraphWeight
    (fun _ => continuous_norm.measurable.pow_const 2) zero_le_one
    (fun n q => by
      rw [abs_of_nonneg (sq_nonneg _),abs_of_nonneg (zero_le_one.trans (freeGraphWeight_one n q)),one_mul]
      change ‖q‖^2 ≤ 1+(‖q‖^2+(n:ℝ))
      nlinarith [Nat.cast_nonneg (α := ℝ) n]) (show freeGraphOperator.domain from u)
  have hg := grossGraph_momentum_square_sum u
  rw [freeGraphDomainInclusion_apply] at hg
  have he := freeMomentumSquare.mem_graph_snd_inj hg (freeMomentumSquare.mem_graph ⟨u.val,hm⟩) rfl
  rw [he,freeGraphDomain_norm]
  simpa only [freeMomentumSquare,one_mul,freeGraphOperator] using hb

lemma grossGraph_kinetic_sum_expansion (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (hjj : ∀ i j : Fin 3, MemLp (fun k => (k j : ℂ)*(weylMomentumCoefficient f i (hj i)) k)
      2 (volume : Measure GW.Space)) (u : FreeGraphDomain) :
    (∑ j : Fin 3, (grossFormMomentumMap j (grossGraphCovariantInput f hj hjj u j)-
      grossFormFieldMap (weylMomentumCoefficient f j (hj j))
        (grossFormRootMap (grossGraphCovariantInput f hj hjj u j)))) =
    (∑ j : Fin 3,grossFormMomentumMap j (grossGraphMomentumQ u j))-
      (2:ℝ) • (∑ j : Fin 3,grossFormFieldMap (weylMomentumCoefficient f j (hj j)) (commutatorGraphMomentumRootMap j u))-
      commutatorPhaseAnnihilatorMap (∑ j : Fin 3,weylMomentumCoefficient (weylMomentumCoefficient f j (hj j)) j (hjj j j))
        (commutatorGraphRootMap u)+
      commutatorPhaseCreatorMap (∑ j : Fin 3,weylMomentumCoefficient (weylMomentumCoefficient f j (hj j)) j (hjj j j))
        (commutatorGraphRootMap u)+
      (∑ j : Fin 3,generalizedFieldSquare (phaseMultiplicationKernel (weylMomentumCoefficient f j (hj j))) (grossGraphNumberOne u)) := by
  simp_rw [grossGraphCovariant_square_expansion]
  rw [grossFormAnnihilator_sum,grossFormCreator_sum]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.smul_sum,two_smul]

lemma grossGraph_kinetic_sum_bound (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (hjj : ∀ i j : Fin 3, MemLp (fun k => (k j : ℂ)*(weylMomentumCoefficient f i (hj i)) k)
      2 (volume : Measure GW.Space)) (u : FreeGraphDomain) :
    ‖∑ j : Fin 3, (grossFormMomentumMap j (grossGraphCovariantInput f hj hjj u j)-
      grossFormFieldMap (weylMomentumCoefficient f j (hj j))
        (grossFormRootMap (grossGraphCovariantInput f hj hjj u j)))‖ ≤
    (1+2*Real.sqrt (∑ j : Fin 3,‖weylMomentumCoefficient f j (hj j)‖^2)+
      2*‖∑ j : Fin 3,weylMomentumCoefficient (weylMomentumCoefficient f j (hj j)) j (hjj j j)‖+
      4*Real.sqrt 2*(∑ j : Fin 3,‖weylMomentumCoefficient f j (hj j)‖^2))*‖u‖ := by
  let c := ∑ j : Fin 3,weylMomentumCoefficient (weylMomentumCoefficient f j (hj j)) j (hjj j j)
  let g := fun j : Fin 3 => weylMomentumCoefficient f j (hj j)
  have hp := grossGraph_momentum_square_sum_bound u
  have hf := grossGraph_field_momentum_bound g u
  have ha := (commutatorPhaseAnnihilatorMap_bound c (commutatorGraphRootMap u)).trans
    (mul_le_mul_of_nonneg_left (commutatorGraphRootMap_norm u) (norm_nonneg c))
  have hc := (commutatorPhaseCreatorMap_bound c (commutatorGraphRootMap u)).trans
    (mul_le_mul_of_nonneg_left (commutatorGraphRootMap_norm u) (norm_nonneg c))
  have hsq := (phaseFieldSquare_vector_bound g (grossGraphNumberOne u)).trans
    (mul_le_mul_of_nonneg_left (freeGraph_shiftedNumber_bound u).choose_spec (by positivity))
  rw [← freeGraphDomain_norm] at hsq
  have htwo : ‖(2:ℝ) • (∑ j : Fin 3,grossFormFieldMap (g j) (commutatorGraphMomentumRootMap j u))‖ ≤
      2*(Real.sqrt (∑ j : Fin 3,‖g j‖^2)*‖u‖) := by
    rw [norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left hf (by norm_num)
  rw [grossGraph_kinetic_sum_expansion]
  have ht : ‖(∑ j : Fin 3,grossFormMomentumMap j (grossGraphMomentumQ u j))-
      (2:ℝ) • (∑ j : Fin 3,grossFormFieldMap (g j) (commutatorGraphMomentumRootMap j u))-
      commutatorPhaseAnnihilatorMap c (commutatorGraphRootMap u)+
      commutatorPhaseCreatorMap c (commutatorGraphRootMap u)+
      (∑ j : Fin 3,generalizedFieldSquare (phaseMultiplicationKernel (g j)) (grossGraphNumberOne u))‖ ≤
      ((‖u‖+2*(Real.sqrt (∑ j : Fin 3,‖g j‖^2)*‖u‖))+‖c‖*‖u‖)+‖c‖*‖u‖+
        (4*Real.sqrt 2*(∑ j : Fin 3,‖g j‖^2))*‖u‖ := by
    apply (norm_add_le _ _).trans
    apply add_le_add _ hsq
    apply (norm_add_le _ _).trans
    apply add_le_add _ hc
    apply (norm_sub_le _ _).trans
    apply add_le_add _ ha
    exact (norm_sub_le _ _).trans (add_le_add hp htwo)
  exact ht.trans_eq (by ring)

/- Source argument component: WeylKineticBound02. -/
lemma grossGraphWeyl_kinetic_bound (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (hjj : ∀ i j : Fin 3, MemLp (fun k => (k j : ℂ)*(weylMomentumCoefficient f i (hj i)) k)
      2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2)
    (u : FreeGraphDomain) :
    ‖freeMomentumSquare ⟨grossWeylCoefficient f (freeGraphDomainInclusion u),
      grossGraphWeyl_second_momentum f hj hjj heven u⟩‖ ≤
      (1+2*‖grossFormRadialCoefficient f hj‖+
        2*‖∑ j : Fin 3,weylMomentumCoefficient (weylMomentumCoefficient f j (hj j)) j (hjj j j)‖+
        4*Real.sqrt 2*‖grossFormRadialCoefficient f hj‖^2)*‖u‖ := by
  have hg := grossGraphWeyl_kinetic_graph f hj hjj heven u
  have he := freeMomentumSquare.mem_graph_snd_inj
    (freeMomentumSquare.mem_graph ⟨grossWeylCoefficient f (freeGraphDomainInclusion u),
      grossGraphWeyl_second_momentum f hj hjj heven u⟩) hg rfl
  rw [he,LinearIsometryEquiv.norm_map]
  have hb := grossGraph_kinetic_sum_bound f hj hjj u
  rw [← grossFormRadialCoefficient_norm_sq f hj,Real.sqrt_sq (norm_nonneg _)] at hb
  exact hb

/- Source argument component: NumberBound05. -/
lemma grossNumberOne_norm (U : PhysicalNumberDomain 1 zero_le_one) :
    ‖U‖ = ‖physicalShiftedNumberPower 1 (show (physicalShiftedNumberPower 1).domain from U)‖ :=
  GW.Spaces.weightedDomain_norm
    (bochnerWeightedGraph (volume : Measure GW.Space) Sector (fun n => ((n:ℝ)+1)^(1:ℝ))
      (shiftedNumber_weight_one 1 zero_le_one)) U

lemma grossGraphNumberOne_norm (u : FreeGraphDomain) :
    ‖(show PhysicalNumberDomain 1 zero_le_one from grossGraphNumberOne u)‖ ≤ ‖u‖ := by
  rw [grossNumberOne_norm]
  rw [freeGraphDomain_norm]
  exact (freeGraph_shiftedNumber_bound u).choose_spec

lemma grossGraphWeyl_shifted_number_bound (f : OneBoson) (u : FreeGraphDomain) :
    ∃ h : grossWeylCoefficient f (freeGraphDomainInclusion u) ∈ (physicalShiftedNumberPower 1).domain,
      ‖physicalShiftedNumberPower 1 ⟨grossWeylCoefficient f (freeGraphDomainInclusion u),h⟩‖ ≤
        (1+‖f‖)^2*‖u‖ := by
  let U : PhysicalNumberDomain 1 zero_le_one := grossGraphNumberOne u
  let V := fiberWeylPhysicalGraphMap 1 zero_le_one le_rfl (phaseAt f)
    (phaseAt_continuous f).stronglyMeasurable ‖f‖ (commutatorPhase_norm_bound f) U
  have hv := fiberWeylPhysicalGraphMap_inclusion 1 zero_le_one le_rfl (phaseAt f)
    (phaseAt_continuous f).stronglyMeasurable ‖f‖ (commutatorPhase_norm_bound f) U
  have hi : U.val = freeGraphDomainInclusion u := (freeGraphDomainInclusion_apply u).symm
  change V.val = grossWeylCoefficient f U.val at hv
  rw [hi] at hv
  have hm : grossWeylCoefficient f (freeGraphDomainInclusion u) ∈ (physicalShiftedNumberPower 1).domain :=
    hv ▸ V.property
  refine ⟨hm,?_⟩
  have hnorm : ‖physicalShiftedNumberPower 1 ⟨grossWeylCoefficient f (freeGraphDomainInclusion u),hm⟩‖ = ‖V‖ := by
    have he : (⟨grossWeylCoefficient f (freeGraphDomainInclusion u),hm⟩ : (physicalShiftedNumberPower 1).domain) =
        (show (physicalShiftedNumberPower 1).domain from V) := Subtype.ext hv.symm
    rw [he]
    exact (grossNumberOne_norm V).symm
  rw [hnorm]
  have hb := fiberWeylPhysicalGraphMap_bound 1 zero_le_one le_rfl (phaseAt f)
    (phaseAt_continuous f).stronglyMeasurable ‖f‖ (commutatorPhase_norm_bound f) U
  norm_num only [mul_one,Real.rpow_two] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (grossGraphNumberOne_norm u) (sq_nonneg _))

lemma grossGraphWeyl_number_bound (f : OneBoson) (u : FreeGraphDomain) :
    ‖physicalNumberOperator ⟨grossWeylCoefficient f (freeGraphDomainInclusion u),grossGraphWeyl_number_mem f u⟩‖ ≤
      (1+‖f‖)^2*‖u‖ := by
  let V : physicalNumberOperator.domain :=
    ⟨grossWeylCoefficient f (freeGraphDomainInclusion u),grossGraphWeyl_number_mem f u⟩
  obtain ⟨hm,hb⟩ := grossGraphWeyl_shifted_number_bound f u
  have he : physicalRegShiftedNumberInput V =
      (⟨grossWeylCoefficient f (freeGraphDomainInclusion u),hm⟩ : (physicalShiftedNumberPower 1).domain) :=
    Subtype.ext (physicalRegShiftedNumberInput_val V)
  have hn := regNumber_norm_le_shifted V
  rw [he] at hn
  exact hn.trans hb

/- Source argument component: H0Split03. -/
lemma grossH0_action_split (u : freeHamiltonian.domain) :
    freeHamiltonian u = freeMomentumSquare ⟨u.val,freeHamiltonian_momentum_mem u⟩+
      physicalNumberOperator ⟨u.val,freeHamiltonian_number_mem u⟩ := by
  let Ninput : physicalNumberOperator.domain := ⟨u.val,freeHamiltonian_number_mem u⟩
  let symbol := fun n : ℕ => fun _ : GW.Space => (n:ℝ)
  have hn : u.val ∈ (physicalSectorMultiplier symbol).domain :=
    (congrArg (fun A : Physical →ₗ.[ℂ] Physical => u.val ∈ A.domain) physicalNumber_eq_sectorMultiplier).mp Ninput.property
  let ns : (physicalSectorMultiplier symbol).domain := ⟨u.val,hn⟩
  have hg : (u.val,physicalNumberOperator Ninput) ∈ (physicalSectorMultiplier symbol).graph :=
    (congrArg (fun A : Physical →ₗ.[ℂ] Physical => (u.val,physicalNumberOperator Ninput) ∈ A.graph)
      physicalNumber_eq_sectorMultiplier).mp (physicalNumberOperator.mem_graph Ninput)
  have he := (physicalSectorMultiplier symbol).mem_graph_snd_inj hg
    ((physicalSectorMultiplier symbol).mem_graph ns) rfl
  change freeHamiltonian u = freeMomentumSquare ⟨u.val,freeHamiltonian_momentum_mem u⟩+physicalNumberOperator Ninput
  rw [he]
  apply freeFourierRepresentation.injective
  rw [map_add]
  apply lp.ext
  funext n
  apply Lp.ext
  filter_upwards [physicalSectorMultiplier_action freeEnergySymbol u n,
    physicalSectorMultiplier_action (fun _ q => ‖q‖^2) ⟨u.val,freeHamiltonian_momentum_mem u⟩ n,
    physicalSectorMultiplier_action symbol ns n,
    Lp.coeFn_add (freeFourierRepresentation (freeMomentumSquare ⟨u.val,freeHamiltonian_momentum_mem u⟩) n)
      (freeFourierRepresentation (physicalSectorMultiplier symbol ns) n)] with q h₀ hp hn' ha
  change freeFourierRepresentation (freeHamiltonian u) n q =
    (freeFourierRepresentation (freeMomentumSquare ⟨u.val,freeHamiltonian_momentum_mem u⟩) n+
      freeFourierRepresentation (physicalSectorMultiplier symbol ns) n) q
  rw [ha]
  change _ = freeFourierRepresentation (freeMomentumSquare ⟨u.val,freeHamiltonian_momentum_mem u⟩) n q+
    freeFourierRepresentation (physicalSectorMultiplier symbol ns) n q
  change (freeEnergySymbol n q : ℂ) • freeFourierRepresentation u.val n q =
    freeFourierRepresentation (freeHamiltonian u) n q at h₀
  change ((‖q‖^2:ℝ):ℂ) • freeFourierRepresentation u.val n q =
    freeFourierRepresentation (freeMomentumSquare ⟨u.val,freeHamiltonian_momentum_mem u⟩) n q at hp
  change (symbol n q : ℂ) • freeFourierRepresentation u.val n q =
    freeFourierRepresentation (physicalSectorMultiplier symbol ns) n q at hn'
  rw [← h₀,← hp,← hn']
  change ((‖q‖^2+(n:ℝ):ℝ):ℂ) • freeFourierRepresentation u.val n q = _
  rw [Complex.ofReal_add,add_smul]

/- Source argument component: GraphBound02. -/
def grossGraphWeylH0Input (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (hjj : ∀ i j : Fin 3, MemLp (fun k => (k j : ℂ)*(weylMomentumCoefficient f i (hj i)) k)
      2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2)
    (u : FreeGraphDomain) : freeHamiltonian.domain :=
  ⟨grossWeylCoefficient f (freeGraphDomainInclusion u),grossGraphWeyl_H0_mem f hj hjj heven u⟩

lemma grossGraphWeyl_graph_bound (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (hjj : ∀ i j : Fin 3, MemLp (fun k => (k j : ℂ)*(weylMomentumCoefficient f i (hj i)) k)
      2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2)
    (u : FreeGraphDomain) :
    ‖freeHamiltonian (grossGraphWeylH0Input f hj hjj heven u)+(grossGraphWeylH0Input f hj hjj heven u).val‖ ≤
      (2+2*‖grossFormRadialCoefficient f hj‖+
        2*‖∑ j : Fin 3,weylMomentumCoefficient (weylMomentumCoefficient f j (hj j)) j (hjj j j)‖+
        4*Real.sqrt 2*‖grossFormRadialCoefficient f hj‖^2+(1+‖f‖)^2)*‖u‖ := by
  let v := grossGraphWeylH0Input f hj hjj heven u
  have hp := grossGraphWeyl_kinetic_bound f hj hjj heven u
  have hn := grossGraphWeyl_number_bound f u
  have hv : ‖v.val‖ ≤ ‖u‖ := by
    change ‖grossWeylCoefficient f (freeGraphDomainInclusion u)‖ ≤ ‖u‖
    rw [LinearIsometryEquiv.norm_map]
    exact (freeGraph_norm_lower u).1
  rw [grossH0_action_split]
  have hsum : ‖freeMomentumSquare ⟨v.val,freeHamiltonian_momentum_mem v⟩+
      physicalNumberOperator ⟨v.val,freeHamiltonian_number_mem v⟩+v.val‖ ≤
      ((1+2*‖grossFormRadialCoefficient f hj‖+
        2*‖∑ j : Fin 3,weylMomentumCoefficient (weylMomentumCoefficient f j (hj j)) j (hjj j j)‖+
        4*Real.sqrt 2*‖grossFormRadialCoefficient f hj‖^2)*‖u‖+(1+‖f‖)^2*‖u‖)+‖u‖ :=
    (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hp hn)) hv)
  exact hsum.trans_eq (by ring)

/- Source argument component: FiniteMoments02. -/
lemma grossForm_truncate_multiplier_memLp (f : OneBoson) (Λ : ℝ) (m : GW.Space → ℂ)
    (hm : Measurable m) (C : ℝ) (hC : ∀ k : GW.Space, ‖k‖ ≤ Λ → ‖m k‖ ≤ C) :
    MemLp (fun k => m k*grossTruncateCoefficient f Λ k) 2 (volume : Measure GW.Space) := by
  apply (Lp.memLp (grossTruncateCoefficient f Λ)).of_le_mul (c := C)
    (hm.mul (Lp.stronglyMeasurable (grossTruncateCoefficient f Λ)).measurable).aestronglyMeasurable
  filter_upwards [grossTruncateCoefficient_ae f Λ] with k hk
  change ‖m k*grossTruncateCoefficient f Λ k‖ ≤ C*‖grossTruncateCoefficient f Λ k‖
  by_cases h : ‖k‖ ≤ Λ
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hC k h) (norm_nonneg _)
  · have hnot : k ∉ lowRegion Λ := h
    rw [hk,indicator_of_notMem hnot,mul_zero,norm_zero,mul_zero]

lemma grossForm_finite_first_memLp (f : OneBoson) (Λ : ℝ) (j : Fin 3) :
    MemLp (fun k => (k j:ℂ)*grossTruncateCoefficient f Λ k) 2 (volume : Measure GW.Space) := by
  apply grossForm_truncate_multiplier_memLp f Λ (fun k => (k j:ℂ))
    (Complex.continuous_ofReal.measurable.comp (electronCoordinate_measurable j)) |Λ|
  intro k hk
  rw [Complex.norm_real,Real.norm_eq_abs]
  exact (electronCoordinate_abs_le k j).trans (hk.trans (le_abs_self Λ))

lemma grossForm_finite_second_raw_memLp (f : OneBoson) (Λ : ℝ) (i j : Fin 3) :
    MemLp (fun k => ((k i:ℂ)*(k j:ℂ))*grossTruncateCoefficient f Λ k) 2 (volume : Measure GW.Space) := by
  apply grossForm_truncate_multiplier_memLp f Λ (fun k => (k i:ℂ)*(k j:ℂ))
    ((Complex.continuous_ofReal.measurable.comp (electronCoordinate_measurable i)).mul
      (Complex.continuous_ofReal.measurable.comp (electronCoordinate_measurable j))) (Λ^2)
  intro k hk
  rw [norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,pow_two]
  exact mul_le_mul ((electronCoordinate_abs_le k i).trans hk) ((electronCoordinate_abs_le k j).trans hk)
    (abs_nonneg _) ((norm_nonneg k).trans hk)

lemma grossForm_finite_second_memLp (f : OneBoson) (Λ : ℝ) (i j : Fin 3) :
    MemLp (fun k => (k i:ℂ)*weylMomentumCoefficient (grossTruncateCoefficient f Λ) j
      (grossForm_finite_first_memLp f Λ j) k) 2 (volume : Measure GW.Space) := by
  apply (memLp_congr_ae _).mp (grossForm_finite_second_raw_memLp f Λ i j)
  filter_upwards [weylMomentumCoefficient_ae (grossTruncateCoefficient f Λ) j
    (grossForm_finite_first_memLp f Λ j)] with k hk
  rw [hk,mul_assoc]

lemma grossForm_finite_radial_second_memLp (f : OneBoson) (Λ : ℝ) :
    MemLp (fun k => ((‖k‖^2:ℝ):ℂ)*grossTruncateCoefficient f Λ k) 2 (volume : Measure GW.Space) := by
  apply grossForm_truncate_multiplier_memLp f Λ (fun k => ((‖k‖^2:ℝ):ℂ))
    (Complex.continuous_ofReal.measurable.comp (measurable_norm.pow_const 2)) (Λ^2)
  intro k hk
  rw [Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg k) hk 2

def grossFormFiniteSecondRadial (f : OneBoson) (Λ : ℝ) : OneBoson :=
  (grossForm_finite_radial_second_memLp f Λ).toLp (fun k => ((‖k‖^2:ℝ):ℂ)*grossTruncateCoefficient f Λ k)

lemma grossFormFiniteSecondRadial_ae (f : OneBoson) (Λ : ℝ) :
    grossFormFiniteSecondRadial f Λ =ᵐ[volume] fun k => ((‖k‖^2:ℝ):ℂ)*grossTruncateCoefficient f Λ k :=
  MemLp.coeFn_toLp _

/- Source argument component: SecondCoefficient01. -/
lemma grossFormSecondCoefficient_sum (f : OneBoson) (Λ : ℝ) :
    (∑ j : Fin 3, weylMomentumCoefficient
      (weylMomentumCoefficient (grossTruncateCoefficient f Λ) j (grossForm_finite_first_memLp f Λ j)) j
      (grossForm_finite_second_memLp f Λ j j)) = grossFormFiniteSecondRadial f Λ := by
  let g := fun j : Fin 3 => weylMomentumCoefficient (grossTruncateCoefficient f Λ) j
    (grossForm_finite_first_memLp f Λ j)
  let h := fun j : Fin 3 => weylMomentumCoefficient (g j) j (grossForm_finite_second_memLp f Λ j j)
  have ha (j : Fin 3) := weylMomentumCoefficient_ae (grossTruncateCoefficient f Λ) j (grossForm_finite_first_memLp f Λ j)
  have hb (j : Fin 3) := weylMomentumCoefficient_ae (g j) j (grossForm_finite_second_memLp f Λ j j)
  apply Lp.ext
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ h,ae_all_iff.mpr ha,ae_all_iff.mpr hb,
    grossFormFiniteSecondRadial_ae f Λ] with k hs h₁ h₂ hc
  change (∑ j : Fin 3,h j) k = _
  rw [hs,hc]
  change (∑ j : Fin 3,h j k) = _
  have he (j : Fin 3) : h j k = (k j : ℂ)*((k j : ℂ)*grossTruncateCoefficient f Λ k) :=
    (h₂ j).trans (congrArg (fun z : ℂ => (k j : ℂ)*z) (h₁ j))
  simp_rw [he]
  rw [EuclideanSpace.real_norm_sq_eq,Complex.ofReal_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.ofReal_pow]
  ring

/- Source argument component: NegativeMoments02. -/
lemma grossFormMoment_neg (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) :
    weylMomentumCoefficient (-f) j (grossForm_neg_momentum_memLp f j hj) =
      -weylMomentumCoefficient f j hj := by
  apply Lp.ext
  filter_upwards [weylMomentumCoefficient_ae (-f) j (grossForm_neg_momentum_memLp f j hj),
    weylMomentumCoefficient_ae f j hj,Lp.coeFn_neg f,
    Lp.coeFn_neg (weylMomentumCoefficient f j hj)] with k h₁ h₂ h₃ h₄
  rw [h₁,h₄,h₃]
  simp only [Pi.neg_apply,mul_neg,h₂]

lemma grossForm_second_neg_memLp (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (hjj : ∀ i j : Fin 3, MemLp (fun k => (k j : ℂ)*(weylMomentumCoefficient f i (hj i)) k)
      2 (volume : Measure GW.Space)) (i j : Fin 3) :
    MemLp (fun k => (k j : ℂ)*(weylMomentumCoefficient (-f) i
      (grossForm_neg_momentum_memLp f i (hj i))) k) 2 (volume : Measure GW.Space) := by
  rw [grossFormMoment_neg f i (hj i)]
  exact grossForm_neg_momentum_memLp _ j (hjj i j)

/- Source argument component: SecondNegative01. -/
lemma grossFormSecondMoment_neg (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (hjj : ∀ i j : Fin 3, MemLp (fun k => (k j : ℂ)*(weylMomentumCoefficient f i (hj i)) k)
      2 (volume : Measure GW.Space)) (j : Fin 3) :
    weylMomentumCoefficient (weylMomentumCoefficient (-f) j (grossForm_neg_momentum_memLp f j (hj j))) j
      (grossForm_second_neg_memLp f hj hjj j j) =
      -weylMomentumCoefficient (weylMomentumCoefficient f j (hj j)) j (hjj j j) := by
  apply Lp.ext
  have hg := grossFormMoment_neg f j (hj j)
  have he := congrArg (fun a : OneBoson => (a : GW.Space → ℂ)) hg
  have hneg := Lp.coeFn_neg (weylMomentumCoefficient f j (hj j))
  filter_upwards [weylMomentumCoefficient_ae
      (weylMomentumCoefficient (-f) j (grossForm_neg_momentum_memLp f j (hj j))) j
      (grossForm_second_neg_memLp f hj hjj j j),
    weylMomentumCoefficient_ae (weylMomentumCoefficient f j (hj j)) j (hjj j j),hneg,
    Lp.coeFn_neg (weylMomentumCoefficient (weylMomentumCoefficient f j (hj j)) j (hjj j j))] with k h₁ h₂ h₃ h₄
  rw [h₁,h₄]
  rw [congrFun he k,h₃]
  simp only [Pi.neg_apply,mul_neg,h₂]

/- Source argument component: CutoffNorm01. -/
lemma grossFormTruncate_norm_le (f : OneBoson) (Λ : ℝ) : ‖grossTruncateCoefficient f Λ‖ ≤ ‖f‖ := by
  calc
    _ ≤ (1:ℝ)*‖f‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [grossTruncateCoefficient_ae f Λ] with k hk
      rw [hk,one_mul]
      by_cases h : k ∈ lowRegion Λ
      · rw [indicator_of_mem h]
      · rw [indicator_of_notMem h,norm_zero]
        exact norm_nonneg _
    _ = _ := one_mul _

lemma grossFormRadial_truncate (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) (Λ : ℝ) :
    grossFormRadialCoefficient (grossTruncateCoefficient f Λ)
      (fun j => grossForm_truncate_momentum_memLp f j (hj j) Λ) =
      grossTruncateCoefficient (grossFormRadialCoefficient f hj) Λ := by
  apply Lp.ext
  filter_upwards [grossFormRadialCoefficient_ae (grossTruncateCoefficient f Λ)
      (fun j => grossForm_truncate_momentum_memLp f j (hj j) Λ),
    grossTruncateCoefficient_ae f Λ,grossTruncateCoefficient_ae (grossFormRadialCoefficient f hj) Λ,
    grossFormRadialCoefficient_ae f hj] with k h₁ h₂ h₃ h₄
  rw [h₁,h₂,h₃]
  by_cases h : k ∈ lowRegion Λ
  · rw [indicator_of_mem h,indicator_of_mem h,h₄]
  · rw [indicator_of_notMem h,indicator_of_notMem h,mul_zero]

lemma grossFormRadial_truncate_norm_le (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) (Λ : ℝ) :
    ‖grossFormRadialCoefficient (grossTruncateCoefficient f Λ)
      (fun j => grossForm_truncate_momentum_memLp f j (hj j) Λ)‖ ≤ ‖grossFormRadialCoefficient f hj‖ := by
  rw [grossFormRadial_truncate]
  exact grossFormTruncate_norm_le _ _

lemma grossFormRadial_neg (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) :
    grossFormRadialCoefficient (-f) (fun j => grossForm_neg_momentum_memLp f j (hj j)) =
      -grossFormRadialCoefficient f hj := by
  apply Lp.ext
  filter_upwards [grossFormRadialCoefficient_ae (-f) (fun j => grossForm_neg_momentum_memLp f j (hj j)),
    Lp.coeFn_neg f,Lp.coeFn_neg (grossFormRadialCoefficient f hj),grossFormRadialCoefficient_ae f hj] with k h₁ h₂ h₃ h₄
  rw [h₁,h₃,h₂]
  change (‖k‖:ℂ)*(-f k) = -grossFormRadialCoefficient f hj k
  rw [h₄,mul_neg]

/- Source argument component: H0Image02. -/
lemma grossH0Weyl_mem (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (hjj : ∀ i j : Fin 3, MemLp (fun k => (k j : ℂ)*(weylMomentumCoefficient f i (hj i)) k)
      2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2)
    (u : freeHamiltonian.domain) : grossWeylCoefficient f u.val ∈ freeHamiltonian.domain := by
  have h := grossGraphWeyl_H0_mem f hj hjj heven (commutatorSourceGraphInput u)
  rw [commutatorSourceGraphInput_value] at h
  exact h

lemma grossH0Weyl_domain_image (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (hjj : ∀ i j : Fin 3, MemLp (fun k => (k j : ℂ)*(weylMomentumCoefficient f i (hj i)) k)
      2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2) :
    (grossWeylCoefficient f) '' (freeHamiltonian.domain : Set Physical) =
      (freeHamiltonian.domain : Set Physical) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨u,hu,rfl⟩
    exact grossH0Weyl_mem f hj hjj heven ⟨u,hu⟩
  · intro v hv
    have hminus := grossH0Weyl_mem (-f) (fun j => grossForm_neg_momentum_memLp f j (hj j))
      (grossForm_second_neg_memLp f hj hjj) (grossForm_neg_even f heven) ⟨v,hv⟩
    refine ⟨grossWeylCoefficient (-f) v,hminus,?_⟩
    rw [← grossWeylCoefficient_symm_apply]
    exact (grossWeylCoefficient f).apply_symm_apply v

/- Source argument component: FiniteSides03. -/
def grossFiniteSideCoefficient (adj : Bool) (f : OneBoson) (Λ : ℝ) : OneBoson :=
  if adj then grossTruncateCoefficient f Λ else -grossTruncateCoefficient f Λ

lemma grossFiniteSideFirst (adj : Bool) (f : OneBoson) (Λ : ℝ) (j : Fin 3) :
    MemLp (fun k => (k j : ℂ)*grossFiniteSideCoefficient adj f Λ k) 2 (volume : Measure GW.Space) := by
  cases adj
  · exact grossForm_neg_momentum_memLp _ j (grossForm_finite_first_memLp f Λ j)
  · exact grossForm_finite_first_memLp f Λ j

lemma grossFiniteSideSecond (adj : Bool) (f : OneBoson) (Λ : ℝ) (i j : Fin 3) :
    MemLp (fun k => (k j : ℂ)*(weylMomentumCoefficient (grossFiniteSideCoefficient adj f Λ) i
      (grossFiniteSideFirst adj f Λ i)) k) 2 (volume : Measure GW.Space) := by
  cases adj
  · exact grossForm_second_neg_memLp _ (grossForm_finite_first_memLp f Λ) (fun i j => grossForm_finite_second_memLp f Λ j i) i j
  · exact grossForm_finite_second_memLp f Λ j i

lemma grossFiniteSideEven (adj : Bool) (f : OneBoson) (Λ : ℝ)
    (he : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2) :
    ∀ᵐ k ∂(volume : Measure GW.Space),
      ‖grossFiniteSideCoefficient adj f Λ (-k)‖^2 = ‖grossFiniteSideCoefficient adj f Λ k‖^2 := by
  cases adj
  · exact grossForm_neg_even _ (grossForm_truncate_even f Λ he)
  · exact grossForm_truncate_even f Λ he

lemma grossFiniteSide_value (adj : Bool) (f : OneBoson) (Λ : ℝ) (U : Physical) :
    grossWeylCoefficient (grossFiniteSideCoefficient adj f Λ) U =
      grossWeylSide adj (grossTruncateCoefficient f Λ) U := by
  cases adj
  · exact (grossWeylCoefficient_symm_apply _ U).symm
  · rfl

lemma grossFiniteSide_norm (adj : Bool) (f : OneBoson) (Λ : ℝ) :
    ‖grossFiniteSideCoefficient adj f Λ‖ ≤ ‖f‖ := by
  cases adj
  · change ‖-grossTruncateCoefficient f Λ‖ ≤ ‖f‖
    rw [norm_neg]
    exact grossFormTruncate_norm_le f Λ
  · exact grossFormTruncate_norm_le f Λ

lemma grossFiniteSide_radial_norm (adj : Bool) (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) (Λ : ℝ) :
    ‖grossFormRadialCoefficient (grossFiniteSideCoefficient adj f Λ) (grossFiniteSideFirst adj f Λ)‖ ≤
      ‖grossFormRadialCoefficient f hj‖ := by
  cases adj
  · change ‖grossFormRadialCoefficient (-grossTruncateCoefficient f Λ)
      (fun j => grossForm_neg_momentum_memLp _ j (grossForm_finite_first_memLp f Λ j))‖ ≤ _
    rw [grossFormRadial_neg (grossTruncateCoefficient f Λ) (grossForm_finite_first_memLp f Λ),norm_neg]
    exact grossFormRadial_truncate_norm_le f hj Λ
  · exact grossFormRadial_truncate_norm_le f hj Λ

lemma grossFiniteSide_second_norm (adj : Bool) (f : OneBoson) (Λ : ℝ) :
    ‖∑ j : Fin 3,weylMomentumCoefficient
      (weylMomentumCoefficient (grossFiniteSideCoefficient adj f Λ) j (grossFiniteSideFirst adj f Λ j)) j
      (grossFiniteSideSecond adj f Λ j j)‖ = ‖grossFormFiniteSecondRadial f Λ‖ := by
  cases adj
  · have he (j : Fin 3) := grossFormSecondMoment_neg (grossTruncateCoefficient f Λ)
      (grossForm_finite_first_memLp f Λ) (fun i j => grossForm_finite_second_memLp f Λ j i) j
    change ‖∑ j : Fin 3,weylMomentumCoefficient
      (weylMomentumCoefficient (-grossTruncateCoefficient f Λ) j
        (grossForm_neg_momentum_memLp _ j (grossForm_finite_first_memLp f Λ j))) j
      (grossForm_second_neg_memLp _ (grossForm_finite_first_memLp f Λ) (fun i j => grossForm_finite_second_memLp f Λ j i) j j)‖ = _
    simp_rw [he]
    rw [Finset.sum_neg_distrib,norm_neg,grossFormSecondCoefficient_sum]
  · exact congrArg norm (grossFormSecondCoefficient_sum f Λ)

/- Source argument component: FiniteBounds02. -/
lemma grossFiniteSide_kinetic_bound (adj : Bool) (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (he : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2)
    (Λ : ℝ) (u : FreeGraphDomain) :
    ‖freeMomentumSquare ⟨grossWeylCoefficient (grossFiniteSideCoefficient adj f Λ) (freeGraphDomainInclusion u),
      grossGraphWeyl_second_momentum _ (grossFiniteSideFirst adj f Λ) (grossFiniteSideSecond adj f Λ)
        (grossFiniteSideEven adj f Λ he) u⟩‖ ≤
      (1+2*‖grossFormRadialCoefficient f hj‖+2*‖grossFormFiniteSecondRadial f Λ‖+
        4*Real.sqrt 2*‖grossFormRadialCoefficient f hj‖^2)*‖u‖ := by
  have hb := grossGraphWeyl_kinetic_bound _ (grossFiniteSideFirst adj f Λ) (grossFiniteSideSecond adj f Λ)
    (grossFiniteSideEven adj f Λ he) u
  rw [grossFiniteSide_second_norm] at hb
  have ha := grossFiniteSide_radial_norm adj f hj Λ
  have hasq := pow_le_pow_left₀ (norm_nonneg _) ha 2
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg u)
  exact add_le_add (add_le_add (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left ha (by norm_num))) le_rfl)
    (mul_le_mul_of_nonneg_left hasq (by positivity))

lemma grossFiniteSide_graph_bound (adj : Bool) (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (he : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2)
    (Λ : ℝ) (u : FreeGraphDomain) :
    ‖freeHamiltonian (grossGraphWeylH0Input _ (grossFiniteSideFirst adj f Λ) (grossFiniteSideSecond adj f Λ)
        (grossFiniteSideEven adj f Λ he) u)+
      (grossGraphWeylH0Input _ (grossFiniteSideFirst adj f Λ) (grossFiniteSideSecond adj f Λ)
        (grossFiniteSideEven adj f Λ he) u).val‖ ≤
      (2+2*‖grossFormRadialCoefficient f hj‖+2*‖grossFormFiniteSecondRadial f Λ‖+
        4*Real.sqrt 2*‖grossFormRadialCoefficient f hj‖^2+(1+‖f‖)^2)*‖u‖ := by
  have hb := grossGraphWeyl_graph_bound _ (grossFiniteSideFirst adj f Λ) (grossFiniteSideSecond adj f Λ)
    (grossFiniteSideEven adj f Λ he) u
  rw [grossFiniteSide_second_norm] at hb
  have ha := grossFiniteSide_radial_norm adj f hj Λ
  have hasq := pow_le_pow_left₀ (norm_nonneg _) ha 2
  have hbeta := pow_le_pow_left₀ (by positivity : 0 ≤ 1+‖grossFiniteSideCoefficient adj f Λ‖)
    (add_le_add le_rfl (grossFiniteSide_norm adj f Λ)) 2
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg u)
  exact add_le_add (add_le_add (add_le_add (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left ha (by norm_num))) le_rfl)
    (mul_le_mul_of_nonneg_left hasq (by positivity))) hbeta

/- Source argument component: WeightedLimit07. -/
def grossWeightedClass (r : ℝ) (hr : 0 ≤ r) (hs : r ≤ 1) (f : OneBoson)
    (G : Lp (NumberWeightedDomain Sector r hr) 2 (volume : Measure GW.Space)) :
    Lp (NumberWeightedDomain Sector r hr) 2 (volume : Measure GW.Space) :=
  fiberWeylGraphClass r hr hs (phaseAt f)
    (phaseAt_continuous f).stronglyMeasurable ‖f‖ (commutatorPhase_norm_bound f) G

lemma grossWeightedClass_ae (r : ℝ) (hr : 0 ≤ r) (hs : r ≤ 1) (f : OneBoson)
    (G : Lp (NumberWeightedDomain Sector r hr) 2 (volume : Measure GW.Space)) :
    grossWeightedClass r hr hs f G =ᵐ[volume]
      fun x => weylWeightedMap r hr hs (phaseAt f x) (G x) :=
  fiberWeylGraphClass_ae _ _ _ _ _ _ _ _

lemma grossPhase_sequence (fs : ℕ → OneBoson) (f : OneBoson)
    (hf : Tendsto fs atTop (𝓝 f)) (x : GW.Space) :
    Tendsto (fun n => phaseAt (fs n) x) atTop (𝓝 (phaseAt f x)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have he : (fun n => ‖phaseAt (fs n) x-phaseAt f x‖) = (fun n => ‖fs n-f‖) :=
    funext fun n => grossPhase_difference_norm (fs n) f x
  rw [he]
  exact tendsto_iff_norm_sub_tendsto_zero.mp hf

set_option backward.isDefEq.respectTransparency.types false in
lemma grossGraphRep_pointwise (r : ℝ) (hr : 0 ≤ r) (hs : r ≤ 1)
    (bs : ℕ → GW.Space → OneBoson) (b : GW.Space → OneBoson)
    (G : Lp (NumberWeightedDomain Sector r hr) 2 (volume : Measure GW.Space))
    (hb : ∀ x, Tendsto (fun n => bs n x) atTop (𝓝 (b x))) :
    ∀ᵐ x ∂(volume : Measure GW.Space), Tendsto
      (fun n => fiberWeylGraphRep r hr hs (bs n) G x) atTop
      (𝓝 (fiberWeylGraphRep r hr hs b G x)) := by
  apply Eventually.of_forall
  intro x
  change Tendsto (fun n => weylWeightedMap r hr hs (bs n x) (G x)) atTop
    (𝓝 (weylWeightedMap r hr hs (b x) (G x)))
  have hp : Tendsto (fun n => (bs n x,G x)) atTop (𝓝 (b x,G x)) :=
    (hb x).prodMk_nhds (tendsto_const_nhds : Tendsto (fun _ : ℕ => G x) atTop (𝓝 (G x)))
  have hh := ((weylWeightedMap_joint_continuous r hr hs).tendsto (b x,G x)).comp hp
  convert! hh using 1 <;> rfl

lemma grossGraphRep_dominated (r : ℝ) (hr : 0 ≤ r) (hsr : r ≤ 1)
    (bs : ℕ → GW.Space → OneBoson) (b : GW.Space → OneBoson)
    (hbs : ∀ n, StronglyMeasurable (bs n))
    (hb : ∀ x, Tendsto (fun n => bs n x) atTop (𝓝 (b x)))
    (M : ℝ) (hM : ∀ n, ∀ᵐ x ∂(volume : Measure GW.Space), ‖bs n x‖ ≤ M)
    (G : Lp (NumberWeightedDomain Sector r hr) 2 (volume : Measure GW.Space)) :
    ∃ (hns : ∀ n, MemLp (fiberWeylGraphRep r hr hsr (bs n) G) 2 volume)
      (hn : MemLp (fiberWeylGraphRep r hr hsr b G) 2 volume),
      Tendsto (fun n => ‖(hns n).toLp (fiberWeylGraphRep r hr hsr (bs n) G)-
        hn.toLp (fiberWeylGraphRep r hr hsr b G)‖) atTop (𝓝 0) := by
  let g : GW.Space → ℝ := fun x => (1+M)^(2*r)*‖G x‖
  have hm (n : ℕ) : AEStronglyMeasurable (fiberWeylGraphRep r hr hsr (bs n) G) (volume : Measure GW.Space) := (fiberWeylGraphRep_stronglyMeasurable r hr hsr (bs n) (hbs n) G).aestronglyMeasurable
  have hl := grossGraphRep_pointwise r hr hsr bs b G hb
  have hg : Measurable g := measurable_const.mul (Lp.stronglyMeasurable G).norm.measurable
  have hi : Integrable (fun x => (g x)^2) volume := by
    simpa only [g,mul_pow] using ((Lp.memLp G).integrable_norm_pow (p := 2) (by norm_num)).const_mul (((1+M)^(2*r))^2)
  exact dominated_l2_convergence (𝕜 := ℂ) hm hl hg hi
    (fun n => fiberWeylGraphRep_bound r hr hsr (bs n) M (hM n) G)

lemma grossWeightedClass_sequence (r : ℝ) (hr : 0 ≤ r) (hsr : r ≤ 1) (fs : ℕ → OneBoson) (f : OneBoson)
    (hf : Tendsto fs atTop (𝓝 f)) (M : ℝ) (hM : ∀ n, ‖fs n‖ ≤ M)
    (G : Lp (NumberWeightedDomain Sector r hr) 2 (volume : Measure GW.Space)) :
    Tendsto (fun n => ‖grossWeightedClass r hr hsr (fs n) G-grossWeightedClass r hr hsr f G‖) atTop (𝓝 0) := by
  obtain ⟨hns,hn,ht⟩ := grossGraphRep_dominated r hr hsr (fun n => phaseAt (fs n)) (phaseAt f)
    (fun n => (phaseAt_continuous (fs n)).stronglyMeasurable)
    (fun x => grossPhase_sequence fs f hf x) M
    (fun n => Eventually.of_forall fun x => (phaseAt_norm (fs n) x).le.trans (hM n)) G
  have hc (n : ℕ) : (hns n).toLp (fiberWeylGraphRep r hr hsr (phaseAt (fs n)) G) = grossWeightedClass r hr hsr (fs n) G := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp (hns n)).trans (grossWeightedClass_ae r hr hsr (fs n) G).symm
  have hw : hn.toLp (fiberWeylGraphRep r hr hsr (phaseAt f) G) = grossWeightedClass r hr hsr f G := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp hn).trans (grossWeightedClass_ae r hr hsr f G).symm
  simpa only [hc,hw] using ht

/- Source argument component: RootLimit05. -/
lemma grossFormWeyl_root_representative (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2) (u : FreeFormDomain) :
    fiberRootRepresentative (grossFormRootMap (grossFormWeylInput f hj heven u)) =
      grossWeightedClass (1/2) (show (0:ℝ) ≤ 1/2 from by norm_num) (show (1/2:ℝ) ≤ 1 from by norm_num) f
        (fiberRootRepresentative (grossFormRootMap u)) := by
  rw [grossFormWeyl_root_map]
  change (physicalNumberGraphBochnerUnitary (1/2) (by norm_num)).symm
    (physicalNumberGraphBochnerUnitary (1/2) (by norm_num)
      (grossWeightedClass (1/2) (show (0:ℝ) ≤ 1/2 from by norm_num) (show (1/2:ℝ) ≤ 1 from by norm_num) f
        (fiberRootRepresentative (grossFormRootMap u)))) = _
  exact (physicalNumberGraphBochnerUnitary (1/2) (by norm_num)).symm_apply_apply _

lemma grossFormWeyl_root_sequence (fs : ℕ → OneBoson) (f : OneBoson)
    (hjs : ∀ n (j : Fin 3), MemLp (fun k => (k j : ℂ)*fs n k) 2 (volume : Measure GW.Space))
    (hes : ∀ n, ∀ᵐ k ∂(volume : Measure GW.Space), ‖fs n (-k)‖^2 = ‖fs n k‖^2)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (he : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2)
    (hf : Tendsto fs atTop (𝓝 f)) (M : ℝ) (hM : ∀ n, ‖fs n‖ ≤ M)
    (u : FreeFormDomain) :
    Tendsto (fun n => ‖grossFormRootMap (grossFormWeylInput (fs n) (hjs n) (hes n) u)-
      grossFormRootMap (grossFormWeylInput f hj he u)‖) atTop (𝓝 0) := by
  have h := grossWeightedClass_sequence (1/2) (show (0:ℝ) ≤ 1/2 from by norm_num) (show (1/2:ℝ) ≤ 1 from by norm_num) fs f hf M hM
    (fiberRootRepresentative (grossFormRootMap u))
  have hn (n : ℕ) :
      ‖grossFormRootMap (grossFormWeylInput (fs n) (hjs n) (hes n) u)-
        grossFormRootMap (grossFormWeylInput f hj he u)‖ =
      ‖grossWeightedClass (1/2) (show (0:ℝ) ≤ 1/2 from by norm_num) (show (1/2:ℝ) ≤ 1 from by norm_num) (fs n)
        (fiberRootRepresentative (grossFormRootMap u))-
       grossWeightedClass (1/2) (show (0:ℝ) ≤ 1/2 from by norm_num) (show (1/2:ℝ) ≤ 1 from by norm_num) f
        (fiberRootRepresentative (grossFormRootMap u))‖ := by
    rw [← grossFormWeyl_root_representative (fs n) (hjs n) (hes n) u,
      ← grossFormWeyl_root_representative f hj he u]
    have hd := (physicalNumberGraphBochnerUnitary (1/2)
      (show (0:ℝ) ≤ 1/2 from by norm_num)).symm.isometry.dist_eq
      (grossFormRootMap (grossFormWeylInput (fs n) (hjs n) (hes n) u))
      (grossFormRootMap (grossFormWeylInput f hj he u))
    simpa only [dist_eq_norm,fiberRootRepresentative] using hd.symm
  simpa only [hn] using h

lemma grossFormWeyl_root_real_limit (fs : ℝ → OneBoson) (f : OneBoson)
    (hjs : ∀ Λ (j : Fin 3), MemLp (fun k => (k j : ℂ)*fs Λ k) 2 (volume : Measure GW.Space))
    (hes : ∀ Λ, ∀ᵐ k ∂(volume : Measure GW.Space), ‖fs Λ (-k)‖^2 = ‖fs Λ k‖^2)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (he : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2)
    (hf : Tendsto fs atTop (𝓝 f)) (M : ℝ) (hM : ∀ Λ, ‖fs Λ‖ ≤ M)
    (u : FreeFormDomain) :
    Tendsto (fun Λ => ‖grossFormRootMap (grossFormWeylInput (fs Λ) (hjs Λ) (hes Λ) u)-
      grossFormRootMap (grossFormWeylInput f hj he u)‖) atTop (𝓝 0) := by
  apply Filter.tendsto_iff_seq_tendsto.mpr
  intro seq hseq
  exact grossFormWeyl_root_sequence (fs ∘ seq) f (fun n => hjs (seq n))
    (fun n => hes (seq n)) hj he (hf.comp hseq) M (fun n => hM (seq n)) u

/- Source argument component: StrongQ03. -/
lemma grossFormWeyl_momentum_difference_bound (a b : OneBoson)
    (ha : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*a k) 2 (volume : Measure GW.Space))
    (hb : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*b k) 2 (volume : Measure GW.Space))
    (hea : ∀ᵐ k ∂(volume : Measure GW.Space), ‖a (-k)‖^2 = ‖a k‖^2)
    (heb : ∀ᵐ k ∂(volume : Measure GW.Space), ‖b (-k)‖^2 = ‖b k‖^2)
    (u : FreeFormDomain) (j : Fin 3) :
    ‖grossFormMomentumMap j (grossFormWeylInput a ha hea u)-
      grossFormMomentumMap j (grossFormWeylInput b hb heb u)‖ ≤
    ‖grossWeylCoefficient a (grossFormMomentumMap j u-
        grossFormFieldMap (weylMomentumCoefficient b j (hb j)) (grossFormRootMap u))-
      grossWeylCoefficient b (grossFormMomentumMap j u-
        grossFormFieldMap (weylMomentumCoefficient b j (hb j)) (grossFormRootMap u))‖+
      2*‖weylMomentumCoefficient a j (ha j)-weylMomentumCoefficient b j (hb j)‖*‖grossFormRootMap u‖ := by
  rw [grossFormWeyl_momentum_action,grossFormWeyl_momentum_action]
  change ‖grossWeylCoefficient a (grossFormMomentumMap j u-
    grossFormFieldMap (weylMomentumCoefficient a j (ha j)) (grossFormRootMap u))-
    grossWeylCoefficient b (grossFormMomentumMap j u-
    grossFormFieldMap (weylMomentumCoefficient b j (hb j)) (grossFormRootMap u))‖ ≤ _
  let eta := grossFormMomentumMap j u-
    grossFormFieldMap (weylMomentumCoefficient b j (hb j)) (grossFormRootMap u)
  let d := grossFormFieldMap (weylMomentumCoefficient a j (ha j)-
    weylMomentumCoefficient b j (hb j)) (grossFormRootMap u)
  have he : grossFormMomentumMap j u-
      grossFormFieldMap (weylMomentumCoefficient a j (ha j)) (grossFormRootMap u) = eta-d := by
    dsimp [eta,d]
    rw [grossFormFieldMap_sub]
    abel
  rw [he,map_sub]
  calc
    _ = ‖(grossWeylCoefficient a eta-grossWeylCoefficient b eta)-grossWeylCoefficient a d‖ := by
      congr 1
      abel
    _ ≤ ‖grossWeylCoefficient a eta-grossWeylCoefficient b eta‖+‖grossWeylCoefficient a d‖ := norm_sub_le _ _
    _ ≤ _ := by
      rw [LinearIsometryEquiv.norm_map]
      exact add_le_add le_rfl (grossFormFieldMap_bound _ _)

lemma grossFormWeyl_momentum_real_limit (fs : ℝ → OneBoson) (f : OneBoson)
    (hjs : ∀ Λ (j : Fin 3), MemLp (fun k => (k j : ℂ)*fs Λ k) 2 (volume : Measure GW.Space))
    (hes : ∀ Λ, ∀ᵐ k ∂(volume : Measure GW.Space), ‖fs Λ (-k)‖^2 = ‖fs Λ k‖^2)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (he : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2)
    (hstrong : ∀ V : Physical, Tendsto (fun Λ => ‖grossWeylCoefficient (fs Λ) V-grossWeylCoefficient f V‖)
      atTop (𝓝 0))
    (hm : ∀ j : Fin 3, Tendsto (fun Λ => weylMomentumCoefficient (fs Λ) j (hjs Λ j))
      atTop (𝓝 (weylMomentumCoefficient f j (hj j)))) (u : FreeFormDomain) (j : Fin 3) :
    Tendsto (fun Λ => ‖grossFormMomentumMap j (grossFormWeylInput (fs Λ) (hjs Λ) (hes Λ) u)-
      grossFormMomentumMap j (grossFormWeylInput f hj he u)‖) atTop (𝓝 0) := by
  have h₁ := hstrong (grossFormMomentumMap j u-
    grossFormFieldMap (weylMomentumCoefficient f j (hj j)) (grossFormRootMap u))
  have h₂ := ((tendsto_iff_norm_sub_tendsto_zero.mp (hm j)).const_mul 2).mul_const ‖grossFormRootMap u‖
  have ht := h₁.add h₂
  simp only [mul_zero,zero_mul,add_zero] at ht
  exact squeeze_zero (fun _ => norm_nonneg _) (fun Λ =>
    grossFormWeyl_momentum_difference_bound (fs Λ) f (hjs Λ) hj (hes Λ) he u j) ht

lemma grossFormWeyl_strong_Q (fs : ℝ → OneBoson) (f : OneBoson)
    (hjs : ∀ Λ (j : Fin 3), MemLp (fun k => (k j : ℂ)*fs Λ k) 2 (volume : Measure GW.Space))
    (hes : ∀ Λ, ∀ᵐ k ∂(volume : Measure GW.Space), ‖fs Λ (-k)‖^2 = ‖fs Λ k‖^2)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (he : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2)
    (hf : Tendsto fs atTop (𝓝 f)) (M : ℝ) (hM : ∀ Λ, ‖fs Λ‖ ≤ M)
    (hstrong : ∀ V : Physical, Tendsto (fun Λ => ‖grossWeylCoefficient (fs Λ) V-grossWeylCoefficient f V‖)
      atTop (𝓝 0))
    (hm : ∀ j : Fin 3, Tendsto (fun Λ => weylMomentumCoefficient (fs Λ) j (hjs Λ j))
      atTop (𝓝 (weylMomentumCoefficient f j (hj j)))) (u : FreeFormDomain) :
    Tendsto (fun Λ => ‖grossFormWeylInput (fs Λ) (hjs Λ) (hes Λ) u-
      grossFormWeylInput f hj he u‖) atTop (𝓝 0) := by
  have hr := (grossFormWeyl_root_real_limit fs f hjs hes hj he hf M hM u).pow 2
  have hp (j : Fin 3) := (grossFormWeyl_momentum_real_limit fs f hjs hes hj he hstrong hm u j).pow 2
  have hs := tendsto_finsetSum Finset.univ (fun j _ => hp j)
  have ht := hr.add hs
  simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0),Finset.sum_const_zero,add_zero] at ht
  have heq (Λ : ℝ) : ‖grossFormWeylInput (fs Λ) (hjs Λ) (hes Λ) u-
      grossFormWeylInput f hj he u‖^2 =
      ‖grossFormRootMap (grossFormWeylInput (fs Λ) (hjs Λ) (hes Λ) u)-
        grossFormRootMap (grossFormWeylInput f hj he u)‖^2+
      ∑ j : Fin 3, ‖grossFormMomentumMap j (grossFormWeylInput (fs Λ) (hjs Λ) (hes Λ) u)-
        grossFormMomentumMap j (grossFormWeylInput f hj he u)‖^2 := by
    rw [grossForm_norm_coordinates]
    simp only [map_sub]
  have hsq : Tendsto (fun Λ => ‖grossFormWeylInput (fs Λ) (hjs Λ) (hes Λ) u-
      grossFormWeylInput f hj he u‖^2) atTop (𝓝 0) := by
    simpa only [heq] using ht
  have hroot := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa only [Function.comp_def,Real.sqrt_zero,Real.sqrt_sq_eq_abs,abs_norm] using hroot

/- Source argument component: StrongQNegative03. -/
lemma grossFormWeyl_strong_Q_negative (fs : ℝ → OneBoson) (f : OneBoson)
    (hjs : ∀ Λ (j : Fin 3), MemLp (fun k => (k j : ℂ)*fs Λ k) 2 (volume : Measure GW.Space))
    (hes : ∀ Λ, ∀ᵐ k ∂(volume : Measure GW.Space), ‖fs Λ (-k)‖^2 = ‖fs Λ k‖^2)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (he : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2)
    (hf : Tendsto fs atTop (𝓝 f)) (M : ℝ) (hM : ∀ Λ, ‖fs Λ‖ ≤ M)
    (hstrong : ∀ V : Physical, Tendsto (fun Λ => ‖grossWeylCoefficient (-fs Λ) V-grossWeylCoefficient (-f) V‖)
      atTop (𝓝 0))
    (hm : ∀ j : Fin 3, Tendsto (fun Λ => weylMomentumCoefficient (fs Λ) j (hjs Λ j))
      atTop (𝓝 (weylMomentumCoefficient f j (hj j)))) (u : FreeFormDomain) :
    Tendsto (fun Λ => ‖grossFormWeylInput (-fs Λ)
      (fun j => grossForm_neg_momentum_memLp (fs Λ) j (hjs Λ j)) (grossForm_neg_even (fs Λ) (hes Λ)) u-
      grossFormWeylInput (-f) (fun j => grossForm_neg_momentum_memLp f j (hj j)) (grossForm_neg_even f he) u‖)
      atTop (𝓝 0) := by
  apply grossFormWeyl_strong_Q (fun Λ => -fs Λ) (-f)
    (fun Λ j => grossForm_neg_momentum_memLp (fs Λ) j (hjs Λ j))
    (fun Λ => grossForm_neg_even (fs Λ) (hes Λ))
    (fun j => grossForm_neg_momentum_memLp f j (hj j)) (grossForm_neg_even f he)
    hf.neg M (fun Λ => by simpa only [norm_neg] using hM Λ) hstrong
  intro j
  have heq : (fun Λ => weylMomentumCoefficient (-fs Λ) j
      (grossForm_neg_momentum_memLp (fs Λ) j (hjs Λ j))) =
      fun Λ => -weylMomentumCoefficient (fs Λ) j (hjs Λ j) :=
    funext fun Λ => grossFormMoment_neg (fs Λ) j (hjs Λ j)
  rw [heq,grossFormMoment_neg f j (hj j)]
  exact (hm j).neg

/- Source argument component: CutoffLimit03. -/
lemma grossFormTruncate_tendsto (f : OneBoson) :
    Tendsto (grossTruncateCoefficient f) atTop (𝓝 f) := by
  have hc (Λ : ℝ) : grossTruncateCoefficient f Λ =
      GW.Spaces.WeightedL2.cutoff (w := fun _ : GW.Space => (1:ℝ))
        (lowRegion Λ) (lowRegion_measurable Λ) f := by
    apply Lp.ext
    exact (grossTruncateCoefficient_ae f Λ).trans
      (GW.Spaces.WeightedL2.cutoff_ae (w := fun _ : GW.Space => (1:ℝ))
        (lowRegion Λ) (lowRegion_measurable Λ) f)
  have he : grossTruncateCoefficient f = fun Λ =>
      GW.Spaces.WeightedL2.cutoff (w := fun _ : GW.Space => (1:ℝ))
        (lowRegion Λ) (lowRegion_measurable Λ) f := funext hc
  rw [he]
  apply GW.Spaces.WeightedL2.cutoff_tendsto_real
  apply Eventually.of_forall
  intro k
  exact eventually_ge_atTop ‖k‖

lemma grossFormMoment_truncate (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) (Λ : ℝ) :
    weylMomentumCoefficient (grossTruncateCoefficient f Λ) j
      (grossForm_truncate_momentum_memLp f j hj Λ) =
      grossTruncateCoefficient (weylMomentumCoefficient f j hj) Λ := by
  apply Lp.ext
  filter_upwards [weylMomentumCoefficient_ae (grossTruncateCoefficient f Λ) j
      (grossForm_truncate_momentum_memLp f j hj Λ),grossTruncateCoefficient_ae f Λ,
    grossTruncateCoefficient_ae (weylMomentumCoefficient f j hj) Λ,
    weylMomentumCoefficient_ae f j hj] with k h₁ h₂ h₃ h₄
  rw [h₁,h₂,h₃]
  by_cases h : k ∈ lowRegion Λ
  · rw [indicator_of_mem h,indicator_of_mem h,h₄]
  · rw [indicator_of_notMem h,indicator_of_notMem h,mul_zero]

lemma grossFormMoment_truncate_tendsto (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) :
    Tendsto (fun Λ => weylMomentumCoefficient (grossTruncateCoefficient f Λ) j
      (grossForm_truncate_momentum_memLp f j hj Λ)) atTop
      (𝓝 (weylMomentumCoefficient f j hj)) := by
  have he : (fun Λ => weylMomentumCoefficient (grossTruncateCoefficient f Λ) j
      (grossForm_truncate_momentum_memLp f j hj Λ)) =
      grossTruncateCoefficient (weylMomentumCoefficient f j hj) :=
    funext (grossFormMoment_truncate f j hj)
  rw [he]
  exact grossFormTruncate_tendsto (weylMomentumCoefficient f j hj)

/- Source argument component: SourceStrong01. -/
def grossFormSideInput (adj : Bool) (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (he : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2) (u : FreeFormDomain) : FreeFormDomain :=
  if adj then grossFormWeylInput f hj he u else
    grossFormWeylInput (-f) (fun j => grossForm_neg_momentum_memLp f j (hj j)) (grossForm_neg_even f he) u

lemma grossFormSideInput_value (adj : Bool) (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (he : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2) (u : FreeFormDomain) :
    freeFormDomainInclusion (grossFormSideInput adj f hj he u) = grossWeylSide adj f (freeFormDomainInclusion u) := by
  cases adj
  · simpa only [grossFormSideInput,grossWeylSide,Bool.false_eq_true,if_false,grossWeylCoefficient_symm_apply] using
      grossFormWeylInput_value (-f) (fun j => grossForm_neg_momentum_memLp f j (hj j)) (grossForm_neg_even f he) u
  · exact grossFormWeylInput_value f hj he u

def grossSourceQInput (adj : Bool) (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (u : FreeFormDomain) : FreeFormDomain :=
  grossFormSideInput adj (grossDressingCoefficient α K hα hK)
    (grossForm_momentum_memLp α K hα hK) (grossForm_coefficient_even α K hα hK) u

def grossSourceFiniteQInput (adj : Bool) (α K Λ : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (u : FreeFormDomain) : FreeFormDomain :=
  grossFormSideInput adj (grossFiniteDressingCoefficient α K Λ hα hK)
    (fun j => grossForm_truncate_momentum_memLp (grossDressingCoefficient α K hα hK) j
      (grossForm_momentum_memLp α K hα hK j) Λ)
    (grossForm_truncate_even (grossDressingCoefficient α K hα hK) Λ (grossForm_coefficient_even α K hα hK)) u

lemma grossSource_strong_Q (adj : Bool) (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (u : FreeFormDomain) :
    Tendsto (fun Λ => ‖grossSourceFiniteQInput adj α K Λ hα hK u-grossSourceQInput adj α K hα hK u‖)
      atTop (𝓝 0) := by
  let f := grossDressingCoefficient α K hα hK
  let fs := fun Λ => grossFiniteDressingCoefficient α K Λ hα hK
  let hj := grossForm_momentum_memLp α K hα hK
  let hjs := fun Λ j => grossForm_truncate_momentum_memLp f j (hj j) Λ
  let he := grossForm_coefficient_even α K hα hK
  let hes := fun Λ => grossForm_truncate_even f Λ he
  have hf : Tendsto fs atTop (𝓝 f) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (grossFiniteDressingCoefficient_error_tendsto α K hα hK)
  have hM : ∀ Λ, ‖fs Λ‖ ≤ ‖f‖ := fun Λ => grossFormTruncate_norm_le f Λ
  have hm (j : Fin 3) : Tendsto (fun Λ => weylMomentumCoefficient (fs Λ) j (hjs Λ j))
      atTop (𝓝 (weylMomentumCoefficient f j (hj j))) := grossFormMoment_truncate_tendsto f j (hj j)
  cases adj
  · have hstrong (V : Physical) : Tendsto (fun Λ => ‖grossWeylCoefficient (-fs Λ) V-grossWeylCoefficient (-f) V‖)
        atTop (𝓝 0) := by
      have h := tendsto_iff_norm_sub_tendsto_zero.mp (gross_dressing_strong false α K hα hK V)
      simpa only [grossWeylSide,Bool.false_eq_true,if_false,grossWeylCoefficient_symm_apply] using h
    exact grossFormWeyl_strong_Q_negative fs f hjs hes hj he hf ‖f‖ hM hstrong hm u
  · have hstrong (V : Physical) : Tendsto (fun Λ => ‖grossWeylCoefficient (fs Λ) V-grossWeylCoefficient f V‖)
        atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.mp (gross_dressing_strong true α K hα hK V)
    exact grossFormWeyl_strong_Q fs f hjs hes hj he hf ‖f‖ hM hstrong hm u

lemma grossSource_strong_Q_both (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (u : FreeFormDomain) :
    Tendsto (fun Λ => ‖grossSourceFiniteQInput false α K Λ hα hK u-grossSourceQInput false α K hα hK u‖+
      ‖grossSourceFiniteQInput true α K Λ hα hK u-grossSourceQInput true α K hα hK u‖)
      atTop (𝓝 0) := by
  simpa only [add_zero] using (grossSource_strong_Q false α K hα hK u).add
    (grossSource_strong_Q true α K hα hK u)

/- Source argument component: Map02. -/
def grossFormWeylLinear (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2) :
    FreeFormDomain →ₗ[ℂ] FreeFormDomain where
  toFun := grossFormWeylInput f hj heven
  map_add' u v := by
    apply grossFormDomainInclusion_injective
    rw [grossFormWeylInput_value,map_add,map_add,map_add,grossFormWeylInput_value,grossFormWeylInput_value]
  map_smul' c u := by
    apply grossFormDomainInclusion_injective
    rw [grossFormWeylInput_value,map_smul,map_smul,map_smul,grossFormWeylInput_value]
    rfl

def grossFormWeylMap (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2) :
    FreeFormDomain →L[ℂ] FreeFormDomain :=
  (grossFormWeylLinear f hj heven).mkContinuous (grossFormWeylBound f hj) (grossFormWeyl_bound f hj heven)

lemma grossFormWeylMap_value (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2) (u : FreeFormDomain) :
    freeFormDomainInclusion (grossFormWeylMap f hj heven u) = grossWeylCoefficient f (freeFormDomainInclusion u) :=
  grossFormWeylInput_value f hj heven u

def grossFormWeylEquiv (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2) :
    FreeFormDomain ≃L[ℂ] FreeFormDomain where
  toFun := grossFormWeylInput f hj heven
  invFun := grossFormWeylInput (-f) (fun j => grossForm_neg_momentum_memLp f j (hj j)) (grossForm_neg_even f heven)
  left_inv := grossFormWeyl_left_inverse f hj heven
  right_inv := grossFormWeyl_right_inverse f hj heven
  map_add' := (grossFormWeylLinear f hj heven).map_add
  map_smul' := (grossFormWeylLinear f hj heven).map_smul
  continuous_toFun := (grossFormWeylMap f hj heven).continuous
  continuous_invFun := (grossFormWeylMap (-f) (fun j => grossForm_neg_momentum_memLp f j (hj j)) (grossForm_neg_even f heven)).continuous

/- Source argument component: Density02. -/
def grossFormDressedH0Set (f : OneBoson) : Set FreeFormDomain :=
  {v | ∃ u : freeHamiltonian.domain, freeFormDomainInclusion v = grossWeylCoefficient f u.val}

lemma grossFormDressedH0_dense (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2) :
    Dense (grossFormDressedH0Set f) := by
  intro w
  let v := grossFormWeylInput (-f) (fun j => grossForm_neg_momentum_memLp f j (hj j)) (grossForm_neg_even f heven) w
  obtain ⟨cs,hcs,ht⟩ := smoothFiniteFormCore_sequence v
  have hlim : Tendsto (fun m => grossFormWeylInput f hj heven (cs m)) atTop (𝓝 w) := by
    have h := ((grossFormWeylMap f hj heven).continuous.tendsto v).comp ht
    change Tendsto (fun m => grossFormWeylInput f hj heven (cs m)) atTop
      (𝓝 (grossFormWeylInput f hj heven v)) at h
    rw [grossFormWeyl_right_inverse] at h
    exact h
  apply mem_closure_of_tendsto hlim
  exact Eventually.of_forall fun m => by
    let U : freeHamiltonian.domain := ⟨freeFormDomainInclusion (cs m),smoothFiniteProductCore_le_H0 (hcs m)⟩
    exact ⟨U,grossFormWeylInput_value f hj heven (cs m)⟩

/- Source argument component: PublicDomains01. -/
lemma grossFormSide_domain_image (adj : Bool) (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (he : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2) :
    (grossWeylSide adj f) '' (freeFormOperator.domain : Set Physical) = (freeFormOperator.domain : Set Physical) := by
  cases adj
  · have hfun : (grossWeylSide false f : Physical → Physical) = grossWeylCoefficient (-f) :=
      funext (grossWeylCoefficient_symm_apply f)
    rw [hfun]
    exact grossFormWeyl_domain_image (-f) (fun j => grossForm_neg_momentum_memLp f j (hj j)) (grossForm_neg_even f he)
  · exact grossFormWeyl_domain_image f hj he

lemma main_gross_infinite_form_domain_image (adj : Bool) (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    (grossWeylSide adj (grossDressingCoefficient α K hα hK)) ''
      (freeFormOperator.domain : Set Physical) = (freeFormOperator.domain : Set Physical) :=
  grossFormSide_domain_image adj _ (grossForm_momentum_memLp α K hα hK) (grossForm_coefficient_even α K hα hK)

lemma main_gross_finite_form_domain_image (adj : Bool) (α K Λ : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    (grossWeylSide adj (grossFiniteDressingCoefficient α K Λ hα hK)) ''
      (freeFormOperator.domain : Set Physical) = (freeFormOperator.domain : Set Physical) :=
  grossFormSide_domain_image adj _ (grossFiniteSideFirst true _ Λ)
    (grossForm_truncate_even _ Λ (grossForm_coefficient_even α K hα hK))

lemma main_gross_finite_H0_domain_image (adj : Bool) (α K Λ : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    (grossWeylSide adj (grossFiniteDressingCoefficient α K Λ hα hK)) ''
      (freeHamiltonian.domain : Set Physical) = (freeHamiltonian.domain : Set Physical) := by
  let f := grossDressingCoefficient α K hα hK
  have hfun : (grossWeylSide adj (grossFiniteDressingCoefficient α K Λ hα hK) : Physical → Physical) =
      grossWeylCoefficient (grossFiniteSideCoefficient adj f Λ) :=
    funext fun U => (grossFiniteSide_value adj f Λ U).symm
  rw [hfun]
  exact grossH0Weyl_domain_image _ (grossFiniteSideFirst adj f Λ) (grossFiniteSideSecond adj f Λ)
    (grossFiniteSideEven adj f Λ (grossForm_coefficient_even α K hα hK))

lemma main_gross_dressed_H0_dense (adj : Bool) (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    Dense {v : FreeFormDomain | ∃ u : freeHamiltonian.domain,
      freeFormDomainInclusion v = grossWeylSide adj (grossDressingCoefficient α K hα hK) u.val} := by
  cases adj
  · have hfun (U : Physical) := grossWeylCoefficient_symm_apply (grossDressingCoefficient α K hα hK) U
    simp only [grossWeylSide,Bool.false_eq_true,if_false,hfun]
    exact grossFormDressedH0_dense _
      (fun j => grossForm_neg_momentum_memLp _ j (grossForm_momentum_memLp α K hα hK j))
      (grossForm_neg_even _ (grossForm_coefficient_even α K hα hK))
  · exact grossFormDressedH0_dense _ (grossForm_momentum_memLp α K hα hK) (grossForm_coefficient_even α K hα hK)

/- Source argument component: Original01. -/
lemma grossFormWeyl_momentum_original (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2)
    (u : FreeFormDomain) (j : Fin 3) :
    ∃ hp : freeFormDomainInclusion u ∈ (electronMomentumCoordinate j).domain,
      ∃ a : (generalizedField (phaseMultiplicationKernel (weylMomentumCoefficient f j (hj j)))).domain,
        a.val = freeFormDomainInclusion u ∧
      ∃ hW : grossWeylCoefficient f (freeFormDomainInclusion u) ∈ (electronMomentumCoordinate j).domain,
        electronMomentumCoordinate j ⟨grossWeylCoefficient f (freeFormDomainInclusion u),hW⟩ =
          grossWeylCoefficient f (electronMomentumCoordinate j ⟨freeFormDomainInclusion u,hp⟩-
            generalizedField (phaseMultiplicationKernel (weylMomentumCoefficient f j (hj j))) a) := by
  have hP := grossFormMomentumMap_graph j u
  have hp := (electronMomentumCoordinate j).mem_domain_of_mem_graph hP
  have hpv := (electronMomentumCoordinate j).mem_graph_snd_inj
    ((electronMomentumCoordinate j).mem_graph ⟨_,hp⟩) hP rfl
  have hF := grossFormFieldMap_graph (weylMomentumCoefficient f j (hj j)) (grossFormRootMap u)
  rw [grossFormRootMap_value] at hF
  obtain ⟨a,ha,haout⟩ := (generalizedField (phaseMultiplicationKernel (weylMomentumCoefficient f j (hj j)))).mem_graph_iff.mp hF
  dsimp only [Prod.fst,Prod.snd] at ha haout
  have hW := grossFormWeyl_momentum_graph f j (hj j) heven u
  have hw := (electronMomentumCoordinate j).mem_domain_of_mem_graph hW
  have hwv := (electronMomentumCoordinate j).mem_graph_snd_inj
    ((electronMomentumCoordinate j).mem_graph ⟨_,hw⟩) hW rfl
  refine ⟨hp,a,ha,hw,?_⟩
  calc
    _ = grossFormWeylRightMap f j (hj j) u := hwv
    _ = grossWeylCoefficient f (grossFormMomentumMap j u-
        grossFormFieldMap (weylMomentumCoefficient f j (hj j)) (grossFormRootMap u)) := rfl
    _ = _ := by rw [hpv,haout]

/- Source argument component: OriginalCovariant01. -/
lemma grossFormCovariant_original (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) (u : FreeFormDomain) :
    ∃ hp : freeFormDomainInclusion u ∈ (electronMomentumCoordinate j).domain,
      ∃ a : (generalizedField (phaseMultiplicationKernel (weylMomentumCoefficient f j hj))).domain,
        a.val = freeFormDomainInclusion u ∧
        grossFormMomentumMap j u-grossFormFieldMap (weylMomentumCoefficient f j hj) (grossFormRootMap u) =
          electronMomentumCoordinate j ⟨freeFormDomainInclusion u,hp⟩-
            generalizedField (phaseMultiplicationKernel (weylMomentumCoefficient f j hj)) a := by
  have hP := grossFormMomentumMap_graph j u
  have hp := (electronMomentumCoordinate j).mem_domain_of_mem_graph hP
  have hpv := (electronMomentumCoordinate j).mem_graph_snd_inj hP
    ((electronMomentumCoordinate j).mem_graph ⟨_,hp⟩) rfl
  have hF := grossFormFieldMap_graph (weylMomentumCoefficient f j hj) (grossFormRootMap u)
  rw [grossFormRootMap_value] at hF
  obtain ⟨a,ha,hout⟩ := (generalizedField (phaseMultiplicationKernel (weylMomentumCoefficient f j hj))).mem_graph_iff.mp hF
  dsimp only [Prod.fst,Prod.snd] at ha hout
  refine ⟨hp,a,ha,?_⟩
  rw [hpv,← hout]

lemma grossGraphWeyl_kinetic_identity (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (hjj : ∀ i j : Fin 3, MemLp (fun k => (k j : ℂ)*(weylMomentumCoefficient f i (hj i)) k)
      2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2)
    (u : FreeGraphDomain) :
    (grossWeylCoefficient f).symm
      (freeMomentumSquare ⟨grossWeylCoefficient f (freeGraphDomainInclusion u),
        grossGraphWeyl_second_momentum f hj hjj heven u⟩) =
      ∑ j : Fin 3, (grossFormMomentumMap j (grossGraphCovariantInput f hj hjj u j)-
        grossFormFieldMap (weylMomentumCoefficient f j (hj j))
          (grossFormRootMap (grossGraphCovariantInput f hj hjj u j))) := by
  have he := freeMomentumSquare.mem_graph_snd_inj
    (freeMomentumSquare.mem_graph ⟨grossWeylCoefficient f (freeGraphDomainInclusion u),
      grossGraphWeyl_second_momentum f hj hjj heven u⟩)
    (grossGraphWeyl_kinetic_graph f hj hjj heven u) rfl
  rw [he,LinearIsometryEquiv.symm_apply_apply]

/- Source argument component: SourceFinal01. -/
def grossSourceBeta (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) : ℝ :=
  ‖grossDressingCoefficient α K hα hK‖
def grossSourceA (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) : ℝ :=
  ‖grossFormRadialCoefficient (grossDressingCoefficient α K hα hK) (grossForm_momentum_memLp α K hα hK)‖
def grossSourceC (α K Λ : ℝ) (hα : 0 ≤ α) (hK : 0 < K) : ℝ :=
  ‖grossFormFiniteSecondRadial (grossDressingCoefficient α K hα hK) Λ‖

def grossSourceFiniteH0Input (adj : Bool) (α K Λ : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (u : freeHamiltonian.domain) : freeHamiltonian.domain :=
  grossGraphWeylH0Input _ (grossFiniteSideFirst adj (grossDressingCoefficient α K hα hK) Λ)
    (grossFiniteSideSecond adj (grossDressingCoefficient α K hα hK) Λ)
    (grossFiniteSideEven adj (grossDressingCoefficient α K hα hK) Λ (grossForm_coefficient_even α K hα hK))
    (commutatorSourceGraphInput u)

lemma grossSourceFiniteH0Input_value (adj : Bool) (α K Λ : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (u : freeHamiltonian.domain) : (grossSourceFiniteH0Input adj α K Λ hα hK u).val =
    grossWeylSide adj (grossFiniteDressingCoefficient α K Λ hα hK) u.val := by
  change grossWeylCoefficient (grossFiniteSideCoefficient adj (grossDressingCoefficient α K hα hK) Λ)
    (freeGraphDomainInclusion (commutatorSourceGraphInput u)) = _
  rw [commutatorSourceGraphInput_value]
  exact grossFiniteSide_value adj (grossDressingCoefficient α K hα hK) Λ u.val

lemma grossSourceGraph_norm (u : freeHamiltonian.domain) :
    ‖commutatorSourceGraphInput u‖ = ‖freeHamiltonian u+u.val‖ := by
  rw [freeGraph_norm_identity,commutatorSourceGraphInput_value]
  have he : freeGraphH0Input (commutatorSourceGraphInput u) = u := Subtype.ext rfl
  rw [he]

lemma main_gross_finite_kinetic_bound (adj : Bool) (α K Λ : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (u : freeHamiltonian.domain) :
    ‖freeMomentumSquare ⟨(grossSourceFiniteH0Input adj α K Λ hα hK u).val,
      freeHamiltonian_momentum_mem (grossSourceFiniteH0Input adj α K Λ hα hK u)⟩‖ ≤
    (1+2*grossSourceA α K hα hK+2*grossSourceC α K Λ hα hK+
      4*Real.sqrt 2*(grossSourceA α K hα hK)^2)*‖freeHamiltonian u+u.val‖ := by
  have hb := grossFiniteSide_kinetic_bound adj (grossDressingCoefficient α K hα hK)
    (grossForm_momentum_memLp α K hα hK) (grossForm_coefficient_even α K hα hK) Λ (commutatorSourceGraphInput u)
  rw [grossSourceGraph_norm] at hb
  exact hb

lemma main_gross_finite_number_bound (adj : Bool) (α K Λ : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (u : freeHamiltonian.domain) :
    ‖physicalNumberOperator ⟨(grossSourceFiniteH0Input adj α K Λ hα hK u).val,
      freeHamiltonian_number_mem (grossSourceFiniteH0Input adj α K Λ hα hK u)⟩‖ ≤
    (1+grossSourceBeta α K hα hK)^2*‖freeHamiltonian u+u.val‖ := by
  have hb := grossGraphWeyl_number_bound (grossFiniteSideCoefficient adj (grossDressingCoefficient α K hα hK) Λ)
    (commutatorSourceGraphInput u)
  rw [grossSourceGraph_norm] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact pow_le_pow_left₀ (by positivity)
    (add_le_add le_rfl (grossFiniteSide_norm adj (grossDressingCoefficient α K hα hK) Λ)) 2

lemma main_gross_finite_graph_bound (adj : Bool) (α K Λ : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (u : freeHamiltonian.domain) :
    ‖freeHamiltonian (grossSourceFiniteH0Input adj α K Λ hα hK u)+(grossSourceFiniteH0Input adj α K Λ hα hK u).val‖ ≤
    (2+2*grossSourceA α K hα hK+2*grossSourceC α K Λ hα hK+
      4*Real.sqrt 2*(grossSourceA α K hα hK)^2+(1+grossSourceBeta α K hα hK)^2)*‖freeHamiltonian u+u.val‖ := by
  have hb := grossFiniteSide_graph_bound adj (grossDressingCoefficient α K hα hK)
    (grossForm_momentum_memLp α K hα hK) (grossForm_coefficient_even α K hα hK) Λ (commutatorSourceGraphInput u)
  rw [grossSourceGraph_norm] at hb
  exact hb

/- Source argument component: PublicMomentum01. -/
lemma main_gross_infinite_momentum (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (u : FreeFormDomain) (j : Fin 3) :
    ∃ hp : freeFormDomainInclusion u ∈ (electronMomentumCoordinate j).domain,
      ∃ a : (generalizedField (phaseMultiplicationKernel
        (weylMomentumCoefficient (grossDressingCoefficient α K hα hK) j ((grossForm_momentum_memLp α K hα hK) j)))).domain,
        a.val = freeFormDomainInclusion u ∧
      ∃ hW : grossWeylCoefficient (grossDressingCoefficient α K hα hK) (freeFormDomainInclusion u) ∈ (electronMomentumCoordinate j).domain,
        electronMomentumCoordinate j ⟨grossWeylCoefficient (grossDressingCoefficient α K hα hK) (freeFormDomainInclusion u),hW⟩ =
          grossWeylCoefficient (grossDressingCoefficient α K hα hK) (electronMomentumCoordinate j ⟨freeFormDomainInclusion u,hp⟩-
            generalizedField (phaseMultiplicationKernel
              (weylMomentumCoefficient (grossDressingCoefficient α K hα hK) j ((grossForm_momentum_memLp α K hα hK) j))) a) :=
  grossFormWeyl_momentum_original (grossDressingCoefficient α K hα hK) (grossForm_momentum_memLp α K hα hK) (grossForm_coefficient_even α K hα hK) u j

lemma main_gross_finite_momentum (α K Λ : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (u : FreeFormDomain) (j : Fin 3) :
    ∃ hp : freeFormDomainInclusion u ∈ (electronMomentumCoordinate j).domain,
      ∃ a : (generalizedField (phaseMultiplicationKernel
        (weylMomentumCoefficient (grossFiniteDressingCoefficient α K Λ hα hK) j ((grossFiniteSideFirst true (grossDressingCoefficient α K hα hK) Λ) j)))).domain,
        a.val = freeFormDomainInclusion u ∧
      ∃ hW : grossWeylCoefficient (grossFiniteDressingCoefficient α K Λ hα hK) (freeFormDomainInclusion u) ∈ (electronMomentumCoordinate j).domain,
        electronMomentumCoordinate j ⟨grossWeylCoefficient (grossFiniteDressingCoefficient α K Λ hα hK) (freeFormDomainInclusion u),hW⟩ =
          grossWeylCoefficient (grossFiniteDressingCoefficient α K Λ hα hK) (electronMomentumCoordinate j ⟨freeFormDomainInclusion u,hp⟩-
            generalizedField (phaseMultiplicationKernel
              (weylMomentumCoefficient (grossFiniteDressingCoefficient α K Λ hα hK) j ((grossFiniteSideFirst true (grossDressingCoefficient α K hα hK) Λ) j))) a) :=
  grossFormWeyl_momentum_original (grossFiniteDressingCoefficient α K Λ hα hK) (grossFiniteSideFirst true (grossDressingCoefficient α K hα hK) Λ) (grossForm_truncate_even (grossDressingCoefficient α K hα hK) Λ (grossForm_coefficient_even α K hα hK)) u j

def grossSourceCovariantInput (α K Λ : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (u : freeHamiltonian.domain) (j : Fin 3) : FreeFormDomain :=
  grossGraphCovariantInput (grossFiniteDressingCoefficient α K Λ hα hK)
    (grossFiniteSideFirst true (grossDressingCoefficient α K hα hK) Λ)
    (grossFiniteSideSecond true (grossDressingCoefficient α K hα hK) Λ) (commutatorSourceGraphInput u) j

lemma main_gross_finite_kinetic (α K Λ : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (u : freeHamiltonian.domain) :
    grossWeylSide false (grossFiniteDressingCoefficient α K Λ hα hK)
      (freeMomentumSquare ⟨(grossSourceFiniteH0Input true α K Λ hα hK u).val,
        freeHamiltonian_momentum_mem (grossSourceFiniteH0Input true α K Λ hα hK u)⟩) =
      ∑ j : Fin 3, (grossFormMomentumMap j (grossSourceCovariantInput α K Λ hα hK u j)-
        grossFormFieldMap (weylMomentumCoefficient (grossFiniteDressingCoefficient α K Λ hα hK) j
          (grossFiniteSideFirst true (grossDressingCoefficient α K hα hK) Λ j))
          (grossFormRootMap (grossSourceCovariantInput α K Λ hα hK u j))) :=
  grossGraphWeyl_kinetic_identity (grossFiniteDressingCoefficient α K Λ hα hK)
    (grossFiniteSideFirst true (grossDressingCoefficient α K hα hK) Λ)
    (grossFiniteSideSecond true (grossDressingCoefficient α K hα hK) Λ)
    (grossFiniteSideEven true (grossDressingCoefficient α K hα hK) Λ (grossForm_coefficient_even α K hα hK))
    (commutatorSourceGraphInput u)

/- Source argument component: CutoffUniform01. -/
lemma grossFormWeylBound_mono (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (β a : ℝ) (hβ : ‖f‖ ≤ β) (ha : ‖grossFormRadialCoefficient f hj‖ ≤ a) :
    grossFormWeylBound f hj ≤ Real.sqrt ((1+β)^2+(1+2*a)^2) := by
  apply Real.sqrt_le_sqrt
  exact add_le_add (pow_le_pow_left₀ (by positivity) (by linarith : 1+‖f‖ ≤ 1+β) 2)
    (pow_le_pow_left₀ (by positivity) (by linarith : 1+2*‖grossFormRadialCoefficient f hj‖ ≤ 1+2*a) 2)

lemma grossFormWeylBound_neg (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) :
    grossFormWeylBound (-f) (fun j => grossForm_neg_momentum_memLp f j (hj j)) = grossFormWeylBound f hj := by
  unfold grossFormWeylBound
  rw [norm_neg,grossFormRadial_neg,norm_neg]

lemma grossFormWeylBound_truncate (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) (Λ : ℝ) :
    grossFormWeylBound (grossTruncateCoefficient f Λ)
      (fun j => grossForm_truncate_momentum_memLp f j (hj j) Λ) ≤ grossFormWeylBound f hj :=
  grossFormWeylBound_mono _ _ ‖f‖ ‖grossFormRadialCoefficient f hj‖
    (grossFormTruncate_norm_le f Λ) (grossFormRadial_truncate_norm_le f hj Λ)

lemma grossFormWeyl_truncate_bound (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2) (Λ : ℝ) (u : FreeFormDomain) :
    ‖grossFormWeylInput (grossTruncateCoefficient f Λ)
      (fun j => grossForm_truncate_momentum_memLp f j (hj j) Λ) (grossForm_truncate_even f Λ heven) u‖ ≤
      grossFormWeylBound f hj*‖u‖ :=
  (grossFormWeyl_bound _ _ _ u).trans
    (mul_le_mul_of_nonneg_right (grossFormWeylBound_truncate f hj Λ) (norm_nonneg u))

lemma grossFormWeyl_neg_bound (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2) (u : FreeFormDomain) :
    ‖grossFormWeylInput (-f) (fun j => grossForm_neg_momentum_memLp f j (hj j)) (grossForm_neg_even f heven) u‖ ≤
      grossFormWeylBound f hj*‖u‖ := by
  have h := grossFormWeyl_bound (-f) (fun j => grossForm_neg_momentum_memLp f j (hj j))
    (grossForm_neg_even f heven) u
  rwa [grossFormWeylBound_neg] at h

lemma grossFormWeyl_neg_truncate_bound (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2) (Λ : ℝ) (u : FreeFormDomain) :
    ‖grossFormWeylInput (-grossTruncateCoefficient f Λ)
      (fun j => grossForm_neg_momentum_memLp (grossTruncateCoefficient f Λ) j
        (grossForm_truncate_momentum_memLp f j (hj j) Λ))
      (grossForm_neg_even (grossTruncateCoefficient f Λ) (grossForm_truncate_even f Λ heven)) u‖ ≤
      grossFormWeylBound f hj*‖u‖ :=
  (grossFormWeyl_neg_bound _ _ (grossForm_truncate_even f Λ heven) u).trans
    (mul_le_mul_of_nonneg_right (grossFormWeylBound_truncate f hj Λ) (norm_nonneg u))

/- Source argument component: PublicUniform01. -/
def grossSourceL (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) : ℝ :=
  Real.sqrt ((1+grossSourceBeta α K hα hK)^2+(1+2*grossSourceA α K hα hK)^2)

lemma main_gross_infinite_form_bound (adj : Bool) (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (u : FreeFormDomain) : ‖grossSourceQInput adj α K hα hK u‖ ≤ grossSourceL α K hα hK*‖u‖ := by
  cases adj
  · exact grossFormWeyl_neg_bound _ (grossForm_momentum_memLp α K hα hK) (grossForm_coefficient_even α K hα hK) u
  · exact grossFormWeyl_bound _ (grossForm_momentum_memLp α K hα hK) (grossForm_coefficient_even α K hα hK) u

lemma main_gross_finite_form_bound (adj : Bool) (α K Λ : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (u : FreeFormDomain) : ‖grossSourceFiniteQInput adj α K Λ hα hK u‖ ≤ grossSourceL α K hα hK*‖u‖ := by
  cases adj
  · exact grossFormWeyl_neg_truncate_bound _ (grossForm_momentum_memLp α K hα hK)
      (grossForm_coefficient_even α K hα hK) Λ u
  · exact grossFormWeyl_truncate_bound _ (grossForm_momentum_memLp α K hα hK)
      (grossForm_coefficient_even α K hα hK) Λ u

end GW.Gross
