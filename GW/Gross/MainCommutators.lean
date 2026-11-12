module
public import GW.Fock.FockWeylCurveDerivative
public import GW.Fock.FockWeylDerivative
public import GW.Operators.BasicFourierIntegralCompat
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
public import GW.Fock.FockSmoothProductCore
public import GW.Regularity.RegMixedDomains
public import GW.Fock.FockFieldDefinition
public import GW.Fock.FockFiberFields
public import GW.Operators.ClosedGraphExtension
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal
namespace GW.Fock
open GW.Analysis

/-! Source main:commutators, manuscript 5736–5810.
The original phase kernel and maximal momentum graphs are identified explicitly.
The strong core calculation uses only the single required momentum moment;
both graph coordinates extend on the complete original free graph domain.
All final field inputs are witnesses for the existing partial operators. -/

section CoefficientScalar
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {S : ℕ → Type*} [∀ n, NormedAddCommGroup (S n)] [∀ n, InnerProductSpace ℂ (S n)]
  (R : ∀ n, S n ≃ₗᵢ[ℂ] kernelFixed (E := E) n)

lemma commutatorSectorCreation_smul (c : ℂ) (F : BosonKernel E) (n : ℕ) (u : S n) :
    sectorCreation R (c • F) n u = c • sectorCreation R F n u := by
  have hr : kernelCreationRaw (c • F) n = c • kernelCreationRaw F n := by
    unfold kernelCreationRaw amplify
    rw [ContinuousLinearMap.smul_compLpL,ContinuousLinearMap.comp_smul]
  have h (v : kernelFixed (E := E) n) : kernelCreation (c • F) n v = c • kernelCreation F n v := by
    apply Subtype.ext
    rw [kernelCreation_value]
    change _ = c • (kernelCreation F n v : KernelSector E (n+1))
    rw [kernelCreation_value,hr,ContinuousLinearMap.smul_apply,map_smul]
    exact smul_comm _ _ _
  apply (R (n+1)).injective
  change R (n+1) ((R (n+1)).symm (kernelCreation (c • F) n (R n u))) =
    R (n+1) (c • (R (n+1)).symm (kernelCreation F n (R n u)))
  rw [map_smul,LinearIsometryEquiv.apply_symm_apply,LinearIsometryEquiv.apply_symm_apply,h]

lemma commutatorSectorAnnihilation_smul (c : ℂ) (F : BosonKernel E) (n : ℕ) (v : S (n+1)) :
    sectorAnnihilation R (c • F) n v = (starRingEnd ℂ) c • sectorAnnihilation R F n v := by
  apply ext_inner_left ℂ
  intro u
  rw [← sectorCreation_pairing,commutatorSectorCreation_smul,inner_smul_left,inner_smul_right,← sectorCreation_pairing]

end CoefficientScalar

lemma commutatorOrdinaryKernel_smul (c : ℂ) (f : OneBoson) : ordinaryKernel (c • f) = c • ordinaryKernel f := by
  apply ContinuousLinearMap.ext
  intro z
  change z • (c • f) = c • (z • f)
  exact smul_comm _ _ _

lemma commutatorCreator_smul_coefficient (c : ℂ) (f : OneBoson) (u : FiberRootDomain) :
    fiberOrdinaryCreator (c • f) u = c • fiberOrdinaryCreator f u := by
  apply lp.ext
  funext n
  cases n with
  | zero => simp only [fiberOrdinaryCreator,ordinaryCreation_zero,lp.coeFn_smul,Pi.smul_apply,smul_zero]
  | succ n =>
    simp only [fiberOrdinaryCreator,lp.coeFn_smul,Pi.smul_apply,ordinaryCreation_succ]
    rw [commutatorOrdinaryKernel_smul,commutatorSectorCreation_smul]

lemma commutatorAnnihilator_smul_coefficient (c : ℂ) (f : OneBoson) (u : FiberRootDomain) :
    fiberOrdinaryAnnihilator (c • f) u = (starRingEnd ℂ) c • fiberOrdinaryAnnihilator f u := by
  apply lp.ext
  funext n
  simp only [fiberOrdinaryAnnihilator,lp.coeFn_smul,Pi.smul_apply,ordinaryAnnihilation_apply]
  rw [commutatorOrdinaryKernel_smul,commutatorSectorAnnihilation_smul]
  simp only [ordinaryAnnihilationRootInput]



open GW.Analysis

def commutatorCreatorCoefficientMap (u : FiberRootDomain) : OneBoson →L[ℂ] Carrier :=
  ({ toFun := fun f => fiberOrdinaryCreator f u
     map_add' := fun f g => fiberOrdinaryCreator_add_kernel f g u
     map_smul' := fun c f => commutatorCreator_smul_coefficient c f u } : OneBoson →ₗ[ℂ] Carrier).mkContinuous
    ‖u‖ (fun f => (fiberOrdinaryCreator_bound f u).trans_eq (mul_comm _ _))

def commutatorAnnihilatorCoefficientMap (u : FiberRootDomain) : OneBoson →L[ℝ] Carrier :=
  ({ toFun := fun f => fiberOrdinaryAnnihilator f u
     map_add' := fun f g => fiberOrdinaryAnnihilator_add_kernel f g u
     map_smul' := fun r f => by
       change fiberOrdinaryAnnihilator (r • f) u = r • fiberOrdinaryAnnihilator f u
       rw [RCLike.real_smul_eq_coe_smul (K := ℂ) r f]
       calc
         fiberOrdinaryAnnihilator ((r:ℂ) • f) u = (starRingEnd ℂ) (r:ℂ) • fiberOrdinaryAnnihilator f u :=
           commutatorAnnihilator_smul_coefficient (r:ℂ) f u
         _ = (r:ℂ) • fiberOrdinaryAnnihilator f u :=
           congrArg (fun c : ℂ => c • fiberOrdinaryAnnihilator f u) (Complex.conj_ofReal r)
         _ = r • fiberOrdinaryAnnihilator f u :=
           (RCLike.real_smul_eq_coe_smul (K := ℂ) r _).symm } : OneBoson →ₗ[ℝ] Carrier).mkContinuous
    ‖u‖ (fun f => (fiberOrdinaryAnnihilator_bound f u).trans_eq (mul_comm _ _))

set_option backward.isDefEq.respectTransparency.types false in
lemma commutatorCreator_phase_hasDerivAt (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) (u : FiberRootDomain) (x : GW.Space) :
    HasDerivAt (fun t : ℝ => fiberOrdinaryCreator (phaseAt f (x+t • momentumAxis j)) u)
      ((-Complex.I) • fiberOrdinaryCreator (phaseAt (weylMomentumCoefficient f j hj) x) u) 0 := by
  let L := (commutatorCreatorCoefficientMap u).restrictScalars ℝ
  have h := L.hasFDerivAt.comp_hasDerivAt 0 (phaseAt_axis_hasDerivAt f j hj x)
  change HasDerivAt (fun t : ℝ => fiberOrdinaryCreator (phaseAt f (x+t • momentumAxis j)) u)
    (fiberOrdinaryCreator (phaseAt (phaseAxisCoefficient f j hj) x) u) 0 at h
  rw [weylPhase_axis_coefficient,weylPhase_smul,commutatorCreator_smul_coefficient] at h
  exact h

set_option backward.isDefEq.respectTransparency.types false in
lemma commutatorAnnihilator_phase_hasDerivAt (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) (u : FiberRootDomain) (x : GW.Space) :
    HasDerivAt (fun t : ℝ => fiberOrdinaryAnnihilator (phaseAt f (x+t • momentumAxis j)) u)
      (Complex.I • fiberOrdinaryAnnihilator (phaseAt (weylMomentumCoefficient f j hj) x) u) 0 := by
  let L := commutatorAnnihilatorCoefficientMap u
  have h := L.hasFDerivAt.comp_hasDerivAt 0 (phaseAt_axis_hasDerivAt f j hj x)
  change HasDerivAt (fun t : ℝ => fiberOrdinaryAnnihilator (phaseAt f (x+t • momentumAxis j)) u)
    (fiberOrdinaryAnnihilator (phaseAt (phaseAxisCoefficient f j hj) x) u) 0 at h
  rw [weylPhase_axis_coefficient,weylPhase_smul,commutatorAnnihilator_smul_coefficient,
    map_neg,Complex.conj_I,neg_neg] at h
  exact h

lemma commutatorCreator_phase_continuous (f : OneBoson) (u : FiberRootDomain) :
    Continuous (fun x => fiberOrdinaryCreator (phaseAt f x) u) := by
  have hc : Continuous (fun x : GW.Space => (phaseAt f x,u)) := (phaseAt_continuous f).prodMk continuous_const
  have hh := fiberOrdinaryCreator_continuous.comp hc
  convert! hh using 1 <;> rfl

lemma commutatorAnnihilator_phase_continuous (f : OneBoson) (u : FiberRootDomain) :
    Continuous (fun x => fiberOrdinaryAnnihilator (phaseAt f x) u) := by
  have hc : Continuous (fun x : GW.Space => (phaseAt f x,u)) := (phaseAt_continuous f).prodMk continuous_const
  have hh := fiberOrdinaryAnnihilator_continuous.comp hc
  convert! hh using 1 <;> rfl



open GW.Analysis

def commutatorPhasePair (f h : OneBoson) (γ η : ElectronL2) (p : GW.Space × GW.Space) : ℂ :=
  ⟪η p.1 • h p.2, γ p.1 • (physicalPhase p.2 p.1 * f p.2)⟫_ℂ

lemma commutatorPhasePair_integrable (f h : OneBoson) (γ η : ElectronL2) :
    Integrable (commutatorPhasePair f h γ η) ((volume : Measure GW.Space).prod volume) := by
  have hm : Measurable (commutatorPhasePair f h γ η) := by
    unfold commutatorPhasePair
    exact (((Lp.stronglyMeasurable η).measurable.comp measurable_fst).smul
      ((Lp.stronglyMeasurable h).measurable.comp measurable_snd)).inner
      (((Lp.stronglyMeasurable γ).measurable.comp measurable_fst).smul
        ((physicalPhase_joint_continuous.comp continuous_swap).measurable.mul
          ((Lp.stronglyMeasurable f).measurable.comp measurable_snd)))
  apply ((normProduct_integrable volume η γ).mul_prod (normProduct_integrable volume h f)).mono' hm.aestronglyMeasurable
  exact Eventually.of_forall fun p => by
    calc
      ‖commutatorPhasePair f h γ η p‖ ≤ ‖η p.1 • h p.2‖ * ‖γ p.1 • (physicalPhase p.2 p.1 * f p.2)‖ := norm_inner_le_norm _ _
      _ = (‖η p.1‖*‖γ p.1‖)*(‖h p.2‖*‖f p.2‖) := by
        simp only [norm_smul,norm_mul,physicalPhase_norm,one_mul]
        ring

lemma commutatorPhasePair_section (f h : OneBoson) (γ η : ElectronL2) (x : GW.Space) :
    ⟪η x • h,γ x • phaseAt f x⟫_ℂ = ∫ k, commutatorPhasePair f h γ η (x,k) ∂volume := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul (η x) h,Lp.coeFn_smul (γ x) (phaseAt f x),phaseAt_ae f x] with k h₁ h₂ h₃
  rw [h₁,h₂]
  change ⟪η x • h k,γ x • phaseAt f x k⟫_ℂ = _
  rw [h₃]
  rfl

lemma commutatorRawPhase_pair (f h : OneBoson) (γ η : ElectronL2) :
    ⟪tensorEmbedding volume h η,phaseMultiplicationKernel f γ⟫_ℂ =
      ∫ x, ⟪η x • h,γ x • phaseAt f x⟫_ℂ ∂volume := by
  calc
    _ = ⟪kernelProductIdentification (tensorEmbedding volume h η),
      kernelProductIdentification (phaseMultiplicationKernel f γ)⟫_ℂ :=
        (kernelProductIdentification.inner_map_map _ _).symm
    _ = ⟪productFunction volume volume η h,kernelProductClass (phaseKernelRep f)
      (phaseKernelRep_measurable f) (phaseKernelRep_bound f) γ⟫_ℂ := by
        rw [fiberKernel_tensor_product]
        congr 1
        exact multiplicationKernel_product _ _ _ _ _
    _ = ∫ p, commutatorPhasePair f h γ η p ∂((volume : Measure GW.Space).prod volume) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [productFunction_ae volume volume η h,
        kernelProductClass_ae (phaseKernelRep f) (phaseKernelRep_measurable f) (phaseKernelRep_bound f) γ] with p h₁ h₂
      rw [h₁,h₂]
      change ⟪η p.1 • h p.2,(physicalPhase p.2 p.1*f p.2)*γ p.1⟫_ℂ = _
      unfold commutatorPhasePair
      congr 1
      exact mul_comm _ _
    _ = ∫ x, ∫ k, commutatorPhasePair f h γ η (x,k) ∂volume ∂volume :=
      integral_prod _ (commutatorPhasePair_integrable f h γ η)
    _ = _ := integral_congr_ae (Eventually.of_forall fun x => (commutatorPhasePair_section f h γ η x).symm)

lemma commutatorPhase_norm_bound (f : OneBoson) :
    ∀ᵐ x ∂(volume : Measure GW.Space), ‖phaseAt f x‖ ≤ ‖f‖ :=
  Eventually.of_forall fun x => (phaseAt_norm f x).le

lemma commutatorPhase_kernel (f : OneBoson) :
    fiberKernel (phaseAt f) (phaseAt_continuous f).aestronglyMeasurable
      (commutatorPhase_norm_bound f) = phaseMultiplicationKernel f := by
  apply ContinuousLinearMap.ext
  intro γ
  apply sub_eq_zero.mp
  apply fiberTensor_total volume
  intro h η
  rw [inner_sub_right,fiberKernel_pair_tensor,commutatorRawPhase_pair,sub_self]



open GW.Analysis

lemma commutatorFourier_coordinate (u : Physical) (n : ℕ) :
    freeFourierRepresentation u n = bochnerCoordinate volume Sector n (physicalFourierUnitary u) := by
  change physicalFourierUnitary (electronBosonUnitary.symm u n) = _
  rw [bochnerUnitary_symm_coordinate]
  exact smoothProduct_fourier_postcomp (lp.evalCLM ℂ Sector 2 n) u

lemma commutatorPhysicalMultiplier_graph (m : GW.Space → ℝ) (u v : Physical) :
    (u,v) ∈ (physicalSectorMultiplier (fun _ => m)).graph ↔
      ∀ n, (fun q => (m q : ℂ) • freeFourierRepresentation u n q) =ᵐ[volume]
        freeFourierRepresentation v n := by
  change (u,v) ∈ (representationTransport freeFourierRepresentation
    (fourierSectorMultiplier (fun _ => m))).graph ↔ _
  rw [representationTransport_graph]
  change (freeFourierRepresentation u,freeFourierRepresentation v) ∈
    (operatorSum ElectronSector (fun _ => realMultiplier m volume)).graph ↔ _
  rw [operatorSum_graph_iff]
  exact forall_congr' fun n => realMultiplier_graph_ae volume m _ _

lemma commutatorCoordinate_multiplier_ae (m : GW.Space → ℝ) (U V : Physical) :
    (fun q => (m q : ℂ) • U q) =ᵐ[volume] V ↔
      ∀ n, (fun q => (m q : ℂ) • bochnerCoordinate volume Sector n U q) =ᵐ[volume]
        bochnerCoordinate volume Sector n V := by
  constructor
  · intro h n
    filter_upwards [h,bochnerCoordinate_ae volume Sector U,bochnerCoordinate_ae volume Sector V] with q hq hU hV
    rw [hU n,hV n]
    exact congrArg (fun z : Carrier => z n) hq
  · intro h
    have hh := ae_all_iff.mpr h
    filter_upwards [hh,bochnerCoordinate_ae volume Sector U,bochnerCoordinate_ae volume Sector V] with q hq hU hV
    apply lp.ext
    funext n
    change (m q : ℂ) • U q n = V q n
    rw [← hU n,← hV n]
    exact hq n

lemma commutatorMomentum_graph (j : Fin 3) (u v : Physical) :
    (u,v) ∈ (electronMomentumCoordinate j).graph ↔
      (u,v) ∈ (momentumOperator (H := Carrier) j).graph := by
  unfold electronMomentumCoordinate momentumOperator fourierMultiplier
  rw [commutatorPhysicalMultiplier_graph,GW.Operators.unitaryTransport_graph_iff,
    realMultiplier_graph_ae,commutatorCoordinate_multiplier_ae]
  simp_rw [commutatorFourier_coordinate]

lemma commutatorMomentum_operator (j : Fin 3) :
    electronMomentumCoordinate j = momentumOperator (H := Carrier) j := by
  apply LinearPMap.ext
  · ext u
    rw [LinearPMap.mem_domain_iff,LinearPMap.mem_domain_iff]
    exact exists_congr fun v => commutatorMomentum_graph j u v
  · intro u hu hv
    exact (momentumOperator (H := Carrier) j).mem_graph_snd_inj
      ((commutatorMomentum_graph j u _).mp ((electronMomentumCoordinate j).mem_graph ⟨u,hu⟩))
      ((momentumOperator (H := Carrier) j).mem_graph ⟨u,hv⟩) rfl



open GW.Analysis

def commutatorCreatorCoreFunction (f : OneBoson) (φ : SmoothScalarTest) (u : FiberRootDomain) (x : GW.Space) : Carrier :=
  φ.value x • fiberOrdinaryCreator (phaseAt f x) u

lemma commutatorCreatorCore_continuous (f : OneBoson) (φ : SmoothScalarTest) (u : FiberRootDomain) :
    Continuous (commutatorCreatorCoreFunction f φ u) :=
  φ.smooth.continuous.smul (commutatorCreator_phase_continuous f u)

lemma commutatorCreatorCore_compact (f : OneBoson) (φ : SmoothScalarTest) (u : FiberRootDomain) :
    HasCompactSupport (commutatorCreatorCoreFunction f φ u) := φ.compact.smul_right

def commutatorCreatorCoreDerivative (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (φ : SmoothScalarTest) (u : FiberRootDomain) (x : GW.Space) : Carrier :=
  smoothTestAxisDerivative φ.value j x • fiberOrdinaryCreator (phaseAt f x) u +
    φ.value x • ((-Complex.I) • fiberOrdinaryCreator (phaseAt (weylMomentumCoefficient f j hj) x) u)

lemma commutatorCreatorCore_hasStrongPartial (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (φ : SmoothScalarTest) (u : FiberRootDomain) :
    HasStrongPartial (commutatorCreatorCoreFunction f φ u)
      (commutatorCreatorCoreDerivative f j hj φ u) j :=
  weylDerivative_strongPartial_smul
    (smoothTest_hasStrongPartial φ.value j (φ.smooth.of_le (by norm_num)))
    (commutatorCreator_phase_hasDerivAt f j hj u)

lemma commutatorCreatorCoreDerivative_continuous (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (φ : SmoothScalarTest) (u : FiberRootDomain) :
    Continuous (commutatorCreatorCoreDerivative f j hj φ u) :=
  ((smoothTestAxisDerivative_continuous φ.value j (φ.smooth.of_le (by norm_num))).smul
    (commutatorCreator_phase_continuous f u)).add
    (φ.smooth.continuous.smul ((commutatorCreator_phase_continuous (weylMomentumCoefficient f j hj) u).const_smul (-Complex.I)))

lemma commutatorCreatorCore_momentum_graph (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (φ : SmoothScalarTest) (u : FiberRootDomain) :
    (compactFunctionL2 (commutatorCreatorCoreFunction f φ u)
        (commutatorCreatorCore_continuous f φ u) (commutatorCreatorCore_compact f φ u),
      (-Complex.I) • compactFunctionL2 (commutatorCreatorCoreDerivative f j hj φ u)
        (commutatorCreatorCoreDerivative_continuous f j hj φ u)
        (strongPartial_hasCompactSupport (commutatorCreatorCore_compact f φ u)
          (commutatorCreatorCore_hasStrongPartial f j hj φ u))) ∈
      (momentumOperator (H := Carrier) j).graph :=
  weylDerivative_compact_momentum_graph
    (commutatorCreatorCore_continuous f φ u) (commutatorCreatorCore_compact f φ u)
    (commutatorCreatorCore_hasStrongPartial f j hj φ u)
    (commutatorCreatorCoreDerivative_continuous f j hj φ u)

def commutatorAnnihilatorCoreFunction (f : OneBoson) (φ : SmoothScalarTest) (u : FiberRootDomain) (x : GW.Space) : Carrier :=
  φ.value x • fiberOrdinaryAnnihilator (phaseAt f x) u

lemma commutatorAnnihilatorCore_continuous (f : OneBoson) (φ : SmoothScalarTest) (u : FiberRootDomain) :
    Continuous (commutatorAnnihilatorCoreFunction f φ u) :=
  φ.smooth.continuous.smul (commutatorAnnihilator_phase_continuous f u)

lemma commutatorAnnihilatorCore_compact (f : OneBoson) (φ : SmoothScalarTest) (u : FiberRootDomain) :
    HasCompactSupport (commutatorAnnihilatorCoreFunction f φ u) := φ.compact.smul_right

def commutatorAnnihilatorCoreDerivative (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (φ : SmoothScalarTest) (u : FiberRootDomain) (x : GW.Space) : Carrier :=
  smoothTestAxisDerivative φ.value j x • fiberOrdinaryAnnihilator (phaseAt f x) u +
    φ.value x • (Complex.I • fiberOrdinaryAnnihilator (phaseAt (weylMomentumCoefficient f j hj) x) u)

lemma commutatorAnnihilatorCore_hasStrongPartial (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (φ : SmoothScalarTest) (u : FiberRootDomain) :
    HasStrongPartial (commutatorAnnihilatorCoreFunction f φ u)
      (commutatorAnnihilatorCoreDerivative f j hj φ u) j :=
  weylDerivative_strongPartial_smul
    (smoothTest_hasStrongPartial φ.value j (φ.smooth.of_le (by norm_num)))
    (commutatorAnnihilator_phase_hasDerivAt f j hj u)

lemma commutatorAnnihilatorCoreDerivative_continuous (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (φ : SmoothScalarTest) (u : FiberRootDomain) :
    Continuous (commutatorAnnihilatorCoreDerivative f j hj φ u) :=
  ((smoothTestAxisDerivative_continuous φ.value j (φ.smooth.of_le (by norm_num))).smul
    (commutatorAnnihilator_phase_continuous f u)).add
    (φ.smooth.continuous.smul ((commutatorAnnihilator_phase_continuous (weylMomentumCoefficient f j hj) u).const_smul Complex.I))

lemma commutatorAnnihilatorCore_momentum_graph (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (φ : SmoothScalarTest) (u : FiberRootDomain) :
    (compactFunctionL2 (commutatorAnnihilatorCoreFunction f φ u)
        (commutatorAnnihilatorCore_continuous f φ u) (commutatorAnnihilatorCore_compact f φ u),
      (-Complex.I) • compactFunctionL2 (commutatorAnnihilatorCoreDerivative f j hj φ u)
        (commutatorAnnihilatorCoreDerivative_continuous f j hj φ u)
        (strongPartial_hasCompactSupport (commutatorAnnihilatorCore_compact f φ u)
          (commutatorAnnihilatorCore_hasStrongPartial f j hj φ u))) ∈
      (momentumOperator (H := Carrier) j).graph :=
  weylDerivative_compact_momentum_graph
    (commutatorAnnihilatorCore_continuous f φ u) (commutatorAnnihilatorCore_compact f φ u)
    (commutatorAnnihilatorCore_hasStrongPartial f j hj φ u)
    (commutatorAnnihilatorCoreDerivative_continuous f j hj φ u)



open GW.Analysis

def commutatorPhaseCreatorMap (f : OneBoson) : FiberPhysicalRoot →L[ℂ] Physical :=
  fiberGeneralizedCreatorMap (phaseMultiplicationKernel f)

lemma commutatorPhaseCreator_tensor (f : OneBoson) (φ : SmoothScalarTest) (u : FiberRootDomain) :
    commutatorPhaseCreatorMap f (weightedSimpleTensor volume Sector (1/2) (by norm_num) φ.toL2 u) =
      compactFunctionL2 (commutatorCreatorCoreFunction f φ u)
        (commutatorCreatorCore_continuous f φ u) (commutatorCreatorCore_compact f φ u) := by
  unfold commutatorPhaseCreatorMap
  rw [← commutatorPhase_kernel]
  change fiberGeneralizedCreator (fiberKernel (phaseAt f) (phaseAt_continuous f).aestronglyMeasurable
    (commutatorPhase_norm_bound f)) _ = _
  rw [fiberCreation_identification_root]
  apply Lp.ext
  let U := weightedSimpleTensor volume Sector (1/2) (by norm_num) φ.toL2 u
  have hr := fiberRootRepresentative_simpleTensor φ.toL2 u
  filter_upwards [fiberCreatorClass_ae (phaseAt f) (phaseAt_continuous f).aestronglyMeasurable
      (commutatorPhase_norm_bound f) U,
    tensorEmbedding_ae volume φ.toL2 u,φ.toL2_ae,
    compactFunctionL2_ae (commutatorCreatorCoreFunction f φ u)
      (commutatorCreatorCore_continuous f φ u) (commutatorCreatorCore_compact f φ u)] with x h₁ h₂ h₃ h₄
  rw [h₁,h₄]
  change fiberOrdinaryCreator (phaseAt f x) (fiberRootRepresentative U x) = _
  rw [hr,h₂,fiberOrdinaryCreator_smul_vector,h₃]
  rfl

def commutatorPhaseAnnihilatorMap (f : OneBoson) : FiberPhysicalRoot →L[ℂ] Physical :=
  fiberGeneralizedAnnihilatorMap (phaseMultiplicationKernel f)

lemma commutatorPhaseAnnihilator_tensor (f : OneBoson) (φ : SmoothScalarTest) (u : FiberRootDomain) :
    commutatorPhaseAnnihilatorMap f (weightedSimpleTensor volume Sector (1/2) (by norm_num) φ.toL2 u) =
      compactFunctionL2 (commutatorAnnihilatorCoreFunction f φ u)
        (commutatorAnnihilatorCore_continuous f φ u) (commutatorAnnihilatorCore_compact f φ u) := by
  unfold commutatorPhaseAnnihilatorMap
  rw [← commutatorPhase_kernel]
  change fiberGeneralizedAnnihilatorMap (fiberKernel (phaseAt f) (phaseAt_continuous f).aestronglyMeasurable
    (commutatorPhase_norm_bound f)) _ = _
  rw [fiberAnnihilationMap_identification_root]
  apply Lp.ext
  let U := weightedSimpleTensor volume Sector (1/2) (by norm_num) φ.toL2 u
  have hr := fiberRootRepresentative_simpleTensor φ.toL2 u
  filter_upwards [fiberAnnihilatorClass_ae (phaseAt f) (phaseAt_continuous f).aestronglyMeasurable
      (commutatorPhase_norm_bound f) U,
    tensorEmbedding_ae volume φ.toL2 u,φ.toL2_ae,
    compactFunctionL2_ae (commutatorAnnihilatorCoreFunction f φ u)
      (commutatorAnnihilatorCore_continuous f φ u) (commutatorAnnihilatorCore_compact f φ u)] with x h₁ h₂ h₃ h₄
  rw [h₁,h₄]
  change fiberOrdinaryAnnihilator (phaseAt f x) (fiberRootRepresentative U x) = _
  rw [hr,h₂,fiberOrdinaryAnnihilator_smul_vector,h₃]
  rfl




set_option backward.isDefEq.respectTransparency.types false in
/-- Step 1 of the source momentum commutator proof: the original coordinate
momentum of every free graph vector is an actual shifted number-root input. -/
lemma commutator_coordinate_shiftedRoot (u : freeGraphOperator.domain) (j : Fin 3) :
    ∃ hp : u.val ∈ (electronMomentumCoordinate j).domain,
      ∃ hn : electronMomentumCoordinate j ⟨u.val,hp⟩ ∈ (physicalShiftedNumberPower (1/2)).domain,
        ‖physicalShiftedNumberPower (1/2) ⟨electronMomentumCoordinate j ⟨u.val,hp⟩,hn⟩‖ ≤
          ‖freeGraphOperator u‖ := by
  rw [physicalShiftedNumberHalf_eq_sectorMultiplier]
  unfold electronMomentumCoordinate
  have hp := (physicalSectorMultiplier_domination (fun _ q => q j) freeGraphWeight
    (fun _ => electronCoordinate_measurable j) zero_le_one (fun n q => by
      rw [abs_of_nonneg (zero_le_one.trans (freeGraphWeight_one n q)),one_mul]
      refine (electronCoordinate_abs_le q j).trans ?_
      unfold freeGraphWeight freeEnergySymbol
      nlinarith [sq_nonneg (‖q‖-1),Nat.cast_nonneg (α := ℝ) n]) u).choose
  obtain ⟨hm,hb⟩ := physicalSectorMultiplier_domination
    (fun n q => Real.sqrt ((n:ℝ)+1)*q j) freeGraphWeight
    (fun _ => measurable_const.mul (electronCoordinate_measurable j)) zero_le_one
    (fun n q => by
      rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _),one_mul]
      calc
        _ ≤ Real.sqrt ((n:ℝ)+1)*‖q‖ :=
          mul_le_mul_of_nonneg_left (electronCoordinate_abs_le q j) (Real.sqrt_nonneg _)
        _ = |‖q‖^(1:ℝ)*Real.sqrt ((n:ℝ)+1)| := by
          rw [Real.rpow_one,abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))]
          ring
        _ ≤ |freeGraphWeight n q| := radial_shiftedRoot_bound 1 zero_le_one le_rfl n q) u
  obtain ⟨hn,he⟩ := physicalSectorMultiplier_composition (fun _ q => q j)
    (fun n _ => Real.sqrt ((n:ℝ)+1)) u.val hp hm
  refine ⟨hp,hn,?_⟩
  rw [he]
  simpa only [one_mul,freeGraphOperator] using hb

lemma commutator_graph_shiftedRoot (u : freeGraphOperator.domain) :
    ∃ hn : u.val ∈ (physicalShiftedNumberPower (1/2)).domain,
      ‖physicalShiftedNumberPower (1/2) ⟨u.val,hn⟩‖ ≤ ‖freeGraphOperator u‖ := by
  rw [physicalShiftedNumberHalf_eq_sectorMultiplier]
  have hh := physicalSectorMultiplier_domination (fun n _ => Real.sqrt ((n:ℝ)+1)) freeGraphWeight
    (fun _ => measurable_const) zero_le_one (fun n q => by
      rw [abs_of_nonneg (Real.sqrt_nonneg _),
        abs_of_nonneg (zero_le_one.trans (freeGraphWeight_one n q)),one_mul]
      calc
        _ ≤ (n:ℝ)+1 := Real.sqrt_le_self_iff.mpr (Or.inr (by linarith [Nat.cast_nonneg (α := ℝ) n]))
        _ ≤ freeGraphWeight n q := by
          unfold freeGraphWeight freeEnergySymbol
          nlinarith [sq_nonneg ‖q‖]) u
  simpa only [one_mul,freeGraphOperator] using hh

def commutatorGraphRoot (u : FreeGraphDomain) : FiberPhysicalRoot :=
  ⟨(show freeGraphOperator.domain from u).val,(commutator_graph_shiftedRoot u).choose⟩

def commutatorGraphRootMap : FreeGraphDomain →L[ℂ] FiberPhysicalRoot :=
  ({ toFun := commutatorGraphRoot
     map_add' := fun u v => Subtype.ext rfl
     map_smul' := fun c u => Subtype.ext rfl } : FreeGraphDomain →ₗ[ℂ] FiberPhysicalRoot).mkContinuous
    1 (fun u => by
      rw [one_mul,← fiberPhysicalRoot_norm,freeGraphDomain_norm]
      exact (commutator_graph_shiftedRoot u).choose_spec)

lemma commutatorGraphRootMap_value (u : FreeGraphDomain) :
    (fiberPhysicalRootInput (commutatorGraphRootMap u)).val = freeGraphDomainInclusion u :=
  (freeGraphDomainInclusion_apply u).symm

def commutatorMomentumInput (u : freeGraphOperator.domain) (j : Fin 3) :
    (electronMomentumCoordinate j).domain :=
  ⟨u.val,(commutator_coordinate_shiftedRoot u j).choose⟩

def commutatorGraphMomentumRoot (j : Fin 3) (u : FreeGraphDomain) : FiberPhysicalRoot :=
  ⟨electronMomentumCoordinate j (commutatorMomentumInput u j),
    (commutator_coordinate_shiftedRoot u j).choose_spec.choose⟩

lemma commutatorGraphMomentumRoot_add (j : Fin 3) (u v : FreeGraphDomain) :
    commutatorGraphMomentumRoot j (u+v) = commutatorGraphMomentumRoot j u+commutatorGraphMomentumRoot j v := by
  apply Subtype.ext
  change electronMomentumCoordinate j (commutatorMomentumInput (u+v) j) =
    electronMomentumCoordinate j (commutatorMomentumInput u j)+electronMomentumCoordinate j (commutatorMomentumInput v j)
  have he : commutatorMomentumInput (u+v) j = commutatorMomentumInput u j+commutatorMomentumInput v j :=
    Subtype.ext rfl
  rw [he]
  exact (electronMomentumCoordinate j).toFun.map_add _ _

lemma commutatorGraphMomentumRoot_smul (j : Fin 3) (c : ℂ) (u : FreeGraphDomain) :
    commutatorGraphMomentumRoot j (c • u) = c • commutatorGraphMomentumRoot j u := by
  apply Subtype.ext
  change electronMomentumCoordinate j (commutatorMomentumInput (c • u) j) =
    c • electronMomentumCoordinate j (commutatorMomentumInput u j)
  have he : commutatorMomentumInput (c • u) j = c • commutatorMomentumInput u j := Subtype.ext rfl
  rw [he]
  exact (electronMomentumCoordinate j).toFun.map_smul _ _

def commutatorGraphMomentumRootMap (j : Fin 3) : FreeGraphDomain →L[ℂ] FiberPhysicalRoot :=
  ({ toFun := commutatorGraphMomentumRoot j
     map_add' := commutatorGraphMomentumRoot_add j
     map_smul' := commutatorGraphMomentumRoot_smul j } : FreeGraphDomain →ₗ[ℂ] FiberPhysicalRoot).mkContinuous
    1 (fun u => by
      rw [one_mul,← fiberPhysicalRoot_norm,freeGraphDomain_norm]
      exact (commutator_coordinate_shiftedRoot u j).choose_spec.choose_spec)

lemma commutatorGraphMomentumRootMap_value (j : Fin 3) (u : FreeGraphDomain) :
    (fiberPhysicalRootInput (commutatorGraphMomentumRootMap j u)).val =
      electronMomentumCoordinate j (commutatorMomentumInput u j) := rfl



open GW.Analysis

lemma commutatorPhaseCreator_tensor_ae (f : OneBoson) (γ : ElectronL2) (u : FiberRootDomain) :
    commutatorPhaseCreatorMap f (weightedSimpleTensor volume Sector (1/2) (by norm_num) γ u) =ᵐ[volume]
      (fun x => γ x • fiberOrdinaryCreator (phaseAt f x) u) := by
  unfold commutatorPhaseCreatorMap
  rw [← commutatorPhase_kernel]
  change fiberGeneralizedCreator (fiberKernel (phaseAt f) (phaseAt_continuous f).aestronglyMeasurable
    (commutatorPhase_norm_bound f)) _ =ᵐ[volume] _
  rw [fiberCreation_identification_root]
  let U := weightedSimpleTensor volume Sector (1/2) (by norm_num) γ u
  have hr := fiberRootRepresentative_simpleTensor γ u
  filter_upwards [fiberCreatorClass_ae (phaseAt f) (phaseAt_continuous f).aestronglyMeasurable
    (commutatorPhase_norm_bound f) U,tensorEmbedding_ae volume γ u] with x h₁ h₂
  rw [h₁]
  change fiberOrdinaryCreator (phaseAt f x) (fiberRootRepresentative U x) = _
  rw [hr,h₂,fiberOrdinaryCreator_smul_vector]

lemma commutatorPhaseAnnihilator_tensor_ae (f : OneBoson) (γ : ElectronL2) (u : FiberRootDomain) :
    commutatorPhaseAnnihilatorMap f (weightedSimpleTensor volume Sector (1/2) (by norm_num) γ u) =ᵐ[volume]
      (fun x => γ x • fiberOrdinaryAnnihilator (phaseAt f x) u) := by
  unfold commutatorPhaseAnnihilatorMap
  rw [← commutatorPhase_kernel]
  change fiberGeneralizedAnnihilatorMap (fiberKernel (phaseAt f) (phaseAt_continuous f).aestronglyMeasurable
    (commutatorPhase_norm_bound f)) _ =ᵐ[volume] _
  rw [fiberAnnihilationMap_identification_root]
  let U := weightedSimpleTensor volume Sector (1/2) (by norm_num) γ u
  have hr := fiberRootRepresentative_simpleTensor γ u
  filter_upwards [fiberAnnihilatorClass_ae (phaseAt f) (phaseAt_continuous f).aestronglyMeasurable
    (commutatorPhase_norm_bound f) U,tensorEmbedding_ae volume γ u] with x h₁ h₂
  rw [h₁]
  change fiberOrdinaryAnnihilator (phaseAt f x) (fiberRootRepresentative U x) = _
  rw [hr,h₂,fiberOrdinaryAnnihilator_smul_vector]

def commutatorScalarDerivative (φ : SmoothScalarTest) (j : Fin 3) : ElectronL2 :=
  compactFunctionL2 (smoothTestAxisDerivative φ.value j)
    (smoothTestAxisDerivative_continuous φ.value j (φ.smooth.of_le (by norm_num)))
    (strongPartial_hasCompactSupport φ.compact (smoothTest_hasStrongPartial φ.value j (φ.smooth.of_le (by norm_num))))

def commutatorScalarMomentum (φ : SmoothScalarTest) (j : Fin 3) : ElectronL2 :=
  (-Complex.I) • commutatorScalarDerivative φ j

lemma commutatorScalarMomentum_ae (φ : SmoothScalarTest) (j : Fin 3) :
    commutatorScalarMomentum φ j =ᵐ[volume] fun x => (-Complex.I)*smoothTestAxisDerivative φ.value j x := by
  filter_upwards [Lp.coeFn_smul (-Complex.I) (commutatorScalarDerivative φ j),
    compactFunctionL2_ae (smoothTestAxisDerivative φ.value j)
      (smoothTestAxisDerivative_continuous φ.value j (φ.smooth.of_le (by norm_num)))
      (strongPartial_hasCompactSupport φ.compact (smoothTest_hasStrongPartial φ.value j (φ.smooth.of_le (by norm_num))))] with x h₁ h₂
  change ((-Complex.I) • commutatorScalarDerivative φ j) x = _
  rw [h₁]
  change (-Complex.I)*commutatorScalarDerivative φ j x = _
  rw [show commutatorScalarDerivative φ j x = smoothTestAxisDerivative φ.value j x from h₂]

lemma commutatorStrongPartial_tensor {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {a da : GW.Space → ℂ} {j : Fin 3}
    (ha : HasStrongPartial a da j) (v : E) :
    HasStrongPartial (fun x => a x • v) (fun x => da x • v) j := by
  intro x
  have h := (ha x).smul_const v
  simpa only [zero_smul,add_zero] using h

lemma commutatorTensor_momentum_graph (φ : SmoothScalarTest) (j : Fin 3) (v : Carrier) :
    ((ContinuousLinearMap.toSpanSingleton ℂ v).compLp φ.toL2,
      (ContinuousLinearMap.toSpanSingleton ℂ v).compLp (commutatorScalarMomentum φ j)) ∈
      (electronMomentumCoordinate j).graph := by
  let a := fun x : GW.Space => φ.value x • v
  let d := fun x : GW.Space => smoothTestAxisDerivative φ.value j x • v
  have ha : Continuous a := φ.smooth.continuous.smul continuous_const
  have has : HasCompactSupport a := φ.compact.smul_right
  have hd : Continuous d := (smoothTestAxisDerivative_continuous φ.value j (φ.smooth.of_le (by norm_num))).smul continuous_const
  have had : HasStrongPartial a d j :=
    commutatorStrongPartial_tensor (smoothTest_hasStrongPartial φ.value j (φ.smooth.of_le (by norm_num))) v
  have h := weylDerivative_compact_momentum_graph ha has had hd
  have h₁ : compactFunctionL2 a ha has = (ContinuousLinearMap.toSpanSingleton ℂ v).compLp φ.toL2 := by
    apply Lp.ext
    filter_upwards [compactFunctionL2_ae a ha has,(ContinuousLinearMap.toSpanSingleton ℂ v).coeFn_compLp φ.toL2,φ.toL2_ae] with x h₁ h₂ h₃
    rw [h₁,h₂,h₃]
    rfl
  have h₂ : (-Complex.I) • compactFunctionL2 d hd (strongPartial_hasCompactSupport has had) =
      (ContinuousLinearMap.toSpanSingleton ℂ v).compLp (commutatorScalarMomentum φ j) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_smul (-Complex.I) (compactFunctionL2 d hd (strongPartial_hasCompactSupport has had)),
      compactFunctionL2_ae d hd (strongPartial_hasCompactSupport has had),
      (ContinuousLinearMap.toSpanSingleton ℂ v).coeFn_compLp (commutatorScalarMomentum φ j),
      commutatorScalarMomentum_ae φ j] with x h₁ h₂ h₃ h₄
    rw [h₁,h₃,h₄]
    change (-Complex.I) • compactFunctionL2 d hd _ x = _
    rw [h₂]
    exact (mul_smul _ _ _).symm
  rw [h₁,h₂] at h
  exact (commutatorMomentum_graph j _ _).mpr h

lemma commutatorCreator_tensor_graph (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (φ : SmoothScalarTest) (u : FiberRootDomain) :
    (commutatorPhaseCreatorMap f (weightedSimpleTensor volume Sector (1/2) (by norm_num) φ.toL2 u),
      commutatorPhaseCreatorMap f (weightedSimpleTensor volume Sector (1/2) (by norm_num) (commutatorScalarMomentum φ j) u) -
        commutatorPhaseCreatorMap (weylMomentumCoefficient f j hj) (weightedSimpleTensor volume Sector (1/2) (by norm_num) φ.toL2 u)) ∈
      (electronMomentumCoordinate j).graph := by
  have h := commutatorCreatorCore_momentum_graph f j hj φ u
  rw [← commutatorPhaseCreator_tensor] at h
  have he : (-Complex.I) • compactFunctionL2 (commutatorCreatorCoreDerivative f j hj φ u)
      (commutatorCreatorCoreDerivative_continuous f j hj φ u)
      (strongPartial_hasCompactSupport (commutatorCreatorCore_compact f φ u)
        (commutatorCreatorCore_hasStrongPartial f j hj φ u)) =
      commutatorPhaseCreatorMap f (weightedSimpleTensor volume Sector (1/2) (by norm_num) (commutatorScalarMomentum φ j) u) -
        commutatorPhaseCreatorMap (weylMomentumCoefficient f j hj) (weightedSimpleTensor volume Sector (1/2) (by norm_num) φ.toL2 u) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_smul (-Complex.I) (compactFunctionL2 (commutatorCreatorCoreDerivative f j hj φ u)
        (commutatorCreatorCoreDerivative_continuous f j hj φ u)
        (strongPartial_hasCompactSupport (commutatorCreatorCore_compact f φ u)
          (commutatorCreatorCore_hasStrongPartial f j hj φ u))),
      compactFunctionL2_ae (commutatorCreatorCoreDerivative f j hj φ u)
        (commutatorCreatorCoreDerivative_continuous f j hj φ u)
        (strongPartial_hasCompactSupport (commutatorCreatorCore_compact f φ u)
          (commutatorCreatorCore_hasStrongPartial f j hj φ u)),
      commutatorPhaseCreator_tensor_ae f (commutatorScalarMomentum φ j) u,
      commutatorPhaseCreator_tensor_ae (weylMomentumCoefficient f j hj) φ.toL2 u,
      commutatorScalarMomentum_ae φ j,φ.toL2_ae,
      Lp.coeFn_sub
        (commutatorPhaseCreatorMap f (weightedSimpleTensor volume Sector (1/2) (by norm_num) (commutatorScalarMomentum φ j) u))
        (commutatorPhaseCreatorMap (weylMomentumCoefficient f j hj) (weightedSimpleTensor volume Sector (1/2) (by norm_num) φ.toL2 u))] with x h₁ h₂ h₃ h₄ h₅ h₆ h₇
    rw [h₁,h₇]
    change (-Complex.I) • compactFunctionL2 (commutatorCreatorCoreDerivative f j hj φ u) _ _ x = _
    simp only [Pi.sub_apply,Pi.add_apply]
    rw [h₂,h₃,h₄,h₅,h₆]
    unfold commutatorCreatorCoreDerivative
    simp only [smul_add,smul_smul,sub_eq_add_neg]
    have hs : (-Complex.I)*(φ.value x*(-Complex.I)) = -φ.value x := by
      calc
        _ = (Complex.I*Complex.I)*φ.value x := by ring
        _ = _ := by rw [Complex.I_mul_I,neg_one_mul]
    rw [hs,neg_smul]
  rw [he] at h
  exact (commutatorMomentum_graph j _ _).mpr h

lemma commutatorAnnihilator_tensor_graph (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (φ : SmoothScalarTest) (u : FiberRootDomain) :
    (commutatorPhaseAnnihilatorMap f (weightedSimpleTensor volume Sector (1/2) (by norm_num) φ.toL2 u),
      commutatorPhaseAnnihilatorMap f (weightedSimpleTensor volume Sector (1/2) (by norm_num) (commutatorScalarMomentum φ j) u) +
        commutatorPhaseAnnihilatorMap (weylMomentumCoefficient f j hj) (weightedSimpleTensor volume Sector (1/2) (by norm_num) φ.toL2 u)) ∈
      (electronMomentumCoordinate j).graph := by
  have h := commutatorAnnihilatorCore_momentum_graph f j hj φ u
  rw [← commutatorPhaseAnnihilator_tensor] at h
  have he : (-Complex.I) • compactFunctionL2 (commutatorAnnihilatorCoreDerivative f j hj φ u)
      (commutatorAnnihilatorCoreDerivative_continuous f j hj φ u)
      (strongPartial_hasCompactSupport (commutatorAnnihilatorCore_compact f φ u)
        (commutatorAnnihilatorCore_hasStrongPartial f j hj φ u)) =
      commutatorPhaseAnnihilatorMap f (weightedSimpleTensor volume Sector (1/2) (by norm_num) (commutatorScalarMomentum φ j) u) +
        commutatorPhaseAnnihilatorMap (weylMomentumCoefficient f j hj) (weightedSimpleTensor volume Sector (1/2) (by norm_num) φ.toL2 u) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_smul (-Complex.I) (compactFunctionL2 (commutatorAnnihilatorCoreDerivative f j hj φ u)
        (commutatorAnnihilatorCoreDerivative_continuous f j hj φ u)
        (strongPartial_hasCompactSupport (commutatorAnnihilatorCore_compact f φ u)
          (commutatorAnnihilatorCore_hasStrongPartial f j hj φ u))),
      compactFunctionL2_ae (commutatorAnnihilatorCoreDerivative f j hj φ u)
        (commutatorAnnihilatorCoreDerivative_continuous f j hj φ u)
        (strongPartial_hasCompactSupport (commutatorAnnihilatorCore_compact f φ u)
          (commutatorAnnihilatorCore_hasStrongPartial f j hj φ u)),
      commutatorPhaseAnnihilator_tensor_ae f (commutatorScalarMomentum φ j) u,
      commutatorPhaseAnnihilator_tensor_ae (weylMomentumCoefficient f j hj) φ.toL2 u,
      commutatorScalarMomentum_ae φ j,φ.toL2_ae,
      Lp.coeFn_add
        (commutatorPhaseAnnihilatorMap f (weightedSimpleTensor volume Sector (1/2) (by norm_num) (commutatorScalarMomentum φ j) u))
        (commutatorPhaseAnnihilatorMap (weylMomentumCoefficient f j hj) (weightedSimpleTensor volume Sector (1/2) (by norm_num) φ.toL2 u))] with x h₁ h₂ h₃ h₄ h₅ h₆ h₇
    rw [h₁,h₇]
    change (-Complex.I) • compactFunctionL2 (commutatorAnnihilatorCoreDerivative f j hj φ u) _ _ x = _
    simp only [Pi.sub_apply,Pi.add_apply]
    rw [h₂,h₃,h₄,h₅,h₆]
    unfold commutatorAnnihilatorCoreDerivative
    simp only [smul_add,smul_smul,sub_eq_add_neg]
    have hs : (-Complex.I)*(φ.value x*Complex.I) = φ.value x := by
      calc
        _ = -(Complex.I*Complex.I)*φ.value x := by ring
        _ = _ := by rw [Complex.I_mul_I,neg_neg,one_mul]
    rw [hs]
  rw [he] at h
  exact (commutatorMomentum_graph j _ _).mpr h



open GW.Analysis

def commutatorFiniteRoot (v : Carrier) (hv : v ∈ finiteSectorDomain Sector) : FiberRootDomain :=
  ⟨v,(finiteSectorDomain_le Sector (fun n => ((n:ℝ)+1)^(1/2:ℝ))) hv⟩

lemma commutatorFiniteRoot_value (v : Carrier) (hv : v ∈ finiteSectorDomain Sector) :
    numberDomainInclusion Sector (1/2) (by norm_num) (commutatorFiniteRoot v hv) = v :=
  numberDomainInclusion_apply Sector (1/2) (by norm_num) (commutatorFiniteRoot v hv)

set_option backward.isDefEq.respectTransparency.types false in
lemma commutatorGraphRoot_tensor (φ : SmoothScalarTest) (v : Carrier) (hv : v ∈ finiteSectorDomain Sector) :
    commutatorGraphRootMap (smoothProductSmoothInput φ v hv) =
      weightedSimpleTensor volume Sector (1/2) (by norm_num) φ.toL2 (commutatorFiniteRoot v hv) := by
  have ht : (fiberPhysicalRootInput (weightedSimpleTensor volume Sector (1/2) (by norm_num)
      φ.toL2 (commutatorFiniteRoot v hv))).val =
      (ContinuousLinearMap.toSpanSingleton ℂ (numberDomainInclusion Sector (1/2) (by norm_num)
        (commutatorFiniteRoot v hv))).compLp φ.toL2 :=
    weightedSimpleTensor_ambient volume Sector (1/2) (by norm_num) φ.toL2 (commutatorFiniteRoot v hv)
  rw [commutatorFiniteRoot_value] at ht
  apply Subtype.ext
  exact (commutatorGraphRootMap_value _).trans
    ((smoothProductSmoothInput_ambient φ v hv).trans ht.symm)

set_option backward.isDefEq.respectTransparency.types false in
lemma commutatorGraphMomentumRoot_tensor (φ : SmoothScalarTest) (j : Fin 3) (v : Carrier)
    (hv : v ∈ finiteSectorDomain Sector) :
    commutatorGraphMomentumRootMap j (smoothProductSmoothInput φ v hv) =
      weightedSimpleTensor volume Sector (1/2) (by norm_num) (commutatorScalarMomentum φ j)
        (commutatorFiniteRoot v hv) := by
  have ht : (fiberPhysicalRootInput (weightedSimpleTensor volume Sector (1/2) (by norm_num)
      (commutatorScalarMomentum φ j) (commutatorFiniteRoot v hv))).val =
      (ContinuousLinearMap.toSpanSingleton ℂ (numberDomainInclusion Sector (1/2) (by norm_num)
        (commutatorFiniteRoot v hv))).compLp (commutatorScalarMomentum φ j) :=
    weightedSimpleTensor_ambient volume Sector (1/2) (by norm_num) (commutatorScalarMomentum φ j) (commutatorFiniteRoot v hv)
  rw [commutatorFiniteRoot_value] at ht
  have h := (electronMomentumCoordinate j).mem_graph (commutatorMomentumInput (smoothProductSmoothInput φ v hv) j)
  have hg := commutatorTensor_momentum_graph φ j v
  have ho := (electronMomentumCoordinate j).mem_graph_snd_inj h hg
    ((freeGraphDomainInclusion_apply _).symm.trans (smoothProductSmoothInput_ambient φ v hv))
  apply Subtype.ext
  exact (commutatorGraphMomentumRootMap_value _ _).trans (ho.trans ht.symm)

lemma commutatorGraphCore_span {C : Submodule ℂ FreeGraphDomain}
    (h : ∀ (φ : SmoothScalarTest) (v : Carrier) (hv : v ∈ finiteSectorDomain Sector),
      smoothProductSmoothInput φ v hv ∈ C) : smoothFiniteGraphCore ≤ C := by
  have hs : smoothFiniteProductCore ≤ C.map freeGraphDomainInclusion.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro u ⟨φ,v,hv,rfl⟩
    exact ⟨smoothProductSmoothInput φ v hv,h φ v hv,smoothProductSmoothInput_ambient φ v hv⟩
  intro u hu
  obtain ⟨v,hv,he⟩ := hs hu
  have he' : v = u := by
    apply Subtype.ext
    exact (freeGraphDomainInclusion_apply v).symm.trans (he.trans (freeGraphDomainInclusion_apply u))
  exact he' ▸ hv

def commutatorCreatorGraphMap (f : OneBoson) : FreeGraphDomain →L[ℂ] Physical :=
  (commutatorPhaseCreatorMap f).comp commutatorGraphRootMap

def commutatorCreatorRightMap (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) : FreeGraphDomain →L[ℂ] Physical :=
  (commutatorPhaseCreatorMap f).comp (commutatorGraphMomentumRootMap j) -
    (commutatorPhaseCreatorMap (weylMomentumCoefficient f j hj)).comp commutatorGraphRootMap

lemma commutatorCreator_graph_core (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (u : FreeGraphDomain) (hu : u ∈ smoothFiniteGraphCore) :
    (commutatorCreatorGraphMap f u,commutatorCreatorRightMap f j hj u) ∈
      (electronMomentumCoordinate j).graph := by
  let C := (electronMomentumCoordinate j).graph.comap
    ((commutatorCreatorGraphMap f).prod (commutatorCreatorRightMap f j hj)).toLinearMap
  have hc : smoothFiniteGraphCore ≤ C := commutatorGraphCore_span (fun φ v hv => by
    change (commutatorCreatorGraphMap f (smoothProductSmoothInput φ v hv),
      commutatorCreatorRightMap f j hj (smoothProductSmoothInput φ v hv)) ∈ (electronMomentumCoordinate j).graph
    simpa only [commutatorCreatorGraphMap,commutatorCreatorRightMap,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply,commutatorGraphRoot_tensor,commutatorGraphMomentumRoot_tensor] using
      commutatorCreator_tensor_graph f j hj φ (commutatorFiniteRoot v hv))
  exact hc hu

lemma commutatorCreator_graph_all (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) (u : FreeGraphDomain) :
    (commutatorCreatorGraphMap f u,commutatorCreatorRightMap f j hj u) ∈
      (electronMomentumCoordinate j).graph := by
  have hc : ∀ c : smoothFiniteGraphCore,
      ∃ hc : commutatorCreatorGraphMap f c ∈ (electronMomentumCoordinate j).domain,
        electronMomentumCoordinate j ⟨commutatorCreatorGraphMap f c,hc⟩ = commutatorCreatorRightMap f j hj c := by
    intro c
    have hg := commutatorCreator_graph_core f j hj c.val c.property
    have hm := (electronMomentumCoordinate j).mem_domain_of_mem_graph hg
    exact ⟨hm,(electronMomentumCoordinate j).mem_graph_snd_inj
      ((electronMomentumCoordinate j).mem_graph ⟨_,hm⟩) hg rfl⟩
  have hclosed : (electronMomentumCoordinate j).IsClosed :=
    GW.Operators.selfadjoint_closed _ (physicalSectorMultiplier_selfadjoint (fun _ => electronCoordinate_measurable j))
  obtain ⟨hm,he⟩ := GW.Operators.closed_graph_extension (ContinuousLinearMap.id ℂ FreeGraphDomain)
    (commutatorCreatorGraphMap f) (commutatorCreatorRightMap f j hj) (electronMomentumCoordinate j)
    hclosed smoothFiniteGraphCore smoothFiniteGraphCore_dense hc u
  exact (electronMomentumCoordinate j).mem_graph_iff.mpr ⟨⟨_,hm⟩,rfl,he⟩

def commutatorAnnihilatorGraphMap (f : OneBoson) : FreeGraphDomain →L[ℂ] Physical :=
  (commutatorPhaseAnnihilatorMap f).comp commutatorGraphRootMap

def commutatorAnnihilatorRightMap (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) : FreeGraphDomain →L[ℂ] Physical :=
  (commutatorPhaseAnnihilatorMap f).comp (commutatorGraphMomentumRootMap j) +
    (commutatorPhaseAnnihilatorMap (weylMomentumCoefficient f j hj)).comp commutatorGraphRootMap

lemma commutatorAnnihilator_graph_core (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (u : FreeGraphDomain) (hu : u ∈ smoothFiniteGraphCore) :
    (commutatorAnnihilatorGraphMap f u,commutatorAnnihilatorRightMap f j hj u) ∈
      (electronMomentumCoordinate j).graph := by
  let C := (electronMomentumCoordinate j).graph.comap
    ((commutatorAnnihilatorGraphMap f).prod (commutatorAnnihilatorRightMap f j hj)).toLinearMap
  have hc : smoothFiniteGraphCore ≤ C := commutatorGraphCore_span (fun φ v hv => by
    change (commutatorAnnihilatorGraphMap f (smoothProductSmoothInput φ v hv),
      commutatorAnnihilatorRightMap f j hj (smoothProductSmoothInput φ v hv)) ∈ (electronMomentumCoordinate j).graph
    simpa only [commutatorAnnihilatorGraphMap,commutatorAnnihilatorRightMap,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.add_apply,commutatorGraphRoot_tensor,commutatorGraphMomentumRoot_tensor] using
      commutatorAnnihilator_tensor_graph f j hj φ (commutatorFiniteRoot v hv))
  exact hc hu

lemma commutatorAnnihilator_graph_all (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) (u : FreeGraphDomain) :
    (commutatorAnnihilatorGraphMap f u,commutatorAnnihilatorRightMap f j hj u) ∈
      (electronMomentumCoordinate j).graph := by
  have hc : ∀ c : smoothFiniteGraphCore,
      ∃ hc : commutatorAnnihilatorGraphMap f c ∈ (electronMomentumCoordinate j).domain,
        electronMomentumCoordinate j ⟨commutatorAnnihilatorGraphMap f c,hc⟩ = commutatorAnnihilatorRightMap f j hj c := by
    intro c
    have hg := commutatorAnnihilator_graph_core f j hj c.val c.property
    have hm := (electronMomentumCoordinate j).mem_domain_of_mem_graph hg
    exact ⟨hm,(electronMomentumCoordinate j).mem_graph_snd_inj
      ((electronMomentumCoordinate j).mem_graph ⟨_,hm⟩) hg rfl⟩
  have hclosed : (electronMomentumCoordinate j).IsClosed :=
    GW.Operators.selfadjoint_closed _ (physicalSectorMultiplier_selfadjoint (fun _ => electronCoordinate_measurable j))
  obtain ⟨hm,he⟩ := GW.Operators.closed_graph_extension (ContinuousLinearMap.id ℂ FreeGraphDomain)
    (commutatorAnnihilatorGraphMap f) (commutatorAnnihilatorRightMap f j hj) (electronMomentumCoordinate j)
    hclosed smoothFiniteGraphCore smoothFiniteGraphCore_dense hc u
  exact (electronMomentumCoordinate j).mem_graph_iff.mpr ⟨⟨_,hm⟩,rfl,he⟩



open GW.Analysis

def commutatorSourceGraphInput (u : freeHamiltonian.domain) : FreeGraphDomain :=
  show freeGraphOperator.domain from ⟨u.val,freeGraphOperator_domain.symm ▸ u.property⟩

lemma commutatorSourceGraphInput_value (u : freeHamiltonian.domain) :
    freeGraphDomainInclusion (commutatorSourceGraphInput u) = u.val :=
  freeGraphDomainInclusion_apply _

lemma commutatorPhaseCreatorMap_graph (f : OneBoson) (U : FiberPhysicalRoot) :
    ((fiberPhysicalRootInput U).val,commutatorPhaseCreatorMap f U) ∈
      (generalizedCreation (phaseMultiplicationKernel f)).graph := by
  let a := generalizedCreationShiftedInput (phaseMultiplicationKernel f) (fiberPhysicalRootInput U)
  exact (generalizedCreation (phaseMultiplicationKernel f)).mem_graph_iff.mpr
    ⟨a,generalizedCreationShiftedInput_val _ _,rfl⟩

lemma commutatorPhaseAnnihilatorMap_graph (f : OneBoson) (U : FiberPhysicalRoot) :
    ((fiberPhysicalRootInput U).val,commutatorPhaseAnnihilatorMap f U) ∈
      (generalizedAnnihilation (phaseMultiplicationKernel f)).graph := by
  exact (fiberPhysicalDomainInclusion_root U) ▸ fiberGeneralizedAnnihilatorMap_graph (phaseMultiplicationKernel f) U

lemma main_momentum_creator_commutator (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (u : freeHamiltonian.domain) :
    ∃ hp : u.val ∈ (electronMomentumCoordinate j).domain,
      ∃ a : (generalizedCreation (phaseMultiplicationKernel f)).domain, a.val = u.val ∧
      ∃ ap : (generalizedCreation (phaseMultiplicationKernel f)).domain,
        ap.val = electronMomentumCoordinate j ⟨u.val,hp⟩ ∧
      ∃ b : (generalizedCreation (phaseMultiplicationKernel (weylMomentumCoefficient f j hj))).domain,
        b.val = u.val ∧
      ∃ hpa : generalizedCreation (phaseMultiplicationKernel f) a ∈ (electronMomentumCoordinate j).domain,
        electronMomentumCoordinate j ⟨generalizedCreation (phaseMultiplicationKernel f) a,hpa⟩ =
          generalizedCreation (phaseMultiplicationKernel f) ap -
            generalizedCreation (phaseMultiplicationKernel (weylMomentumCoefficient f j hj)) b := by
  let U := commutatorSourceGraphInput u
  have hU : freeGraphDomainInclusion U = u.val := commutatorSourceGraphInput_value u
  have hp := (commutatorMomentumInput (show freeGraphOperator.domain from U) j).property
  have hp' : u.val ∈ (electronMomentumCoordinate j).domain := hp
  have h₁ := commutatorPhaseCreatorMap_graph f (commutatorGraphRootMap U)
  rw [commutatorGraphRootMap_value,hU] at h₁
  obtain ⟨a,ha,haout⟩ := (generalizedCreation (phaseMultiplicationKernel f)).mem_graph_iff.mp h₁
  have h₂ := commutatorPhaseCreatorMap_graph f (commutatorGraphMomentumRootMap j U)
  rw [commutatorGraphMomentumRootMap_value] at h₂
  obtain ⟨ap,hap,hapout⟩ := (generalizedCreation (phaseMultiplicationKernel f)).mem_graph_iff.mp h₂
  have h₃ := commutatorPhaseCreatorMap_graph (weylMomentumCoefficient f j hj) (commutatorGraphRootMap U)
  rw [commutatorGraphRootMap_value,hU] at h₃
  obtain ⟨b,hb,hbout⟩ := (generalizedCreation (phaseMultiplicationKernel (weylMomentumCoefficient f j hj))).mem_graph_iff.mp h₃
  have hg := commutatorCreator_graph_all f j hj U
  change (commutatorPhaseCreatorMap f (commutatorGraphRootMap U),
    commutatorPhaseCreatorMap f (commutatorGraphMomentumRootMap j U) -
      commutatorPhaseCreatorMap (weylMomentumCoefficient f j hj) (commutatorGraphRootMap U)) ∈ _ at hg
  dsimp only [Prod.fst,Prod.snd] at ha haout hap hapout hb hbout
  rw [← haout,← hapout,← hbout] at hg
  have hpa := (electronMomentumCoordinate j).mem_domain_of_mem_graph hg
  refine ⟨hp',a,ha,ap,hap,b,hb,hpa,?_⟩
  exact (electronMomentumCoordinate j).mem_graph_snd_inj ((electronMomentumCoordinate j).mem_graph ⟨_,hpa⟩) hg rfl

lemma main_momentum_annihilator_commutator (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (u : freeHamiltonian.domain) :
    ∃ hp : u.val ∈ (electronMomentumCoordinate j).domain,
      ∃ a : (generalizedAnnihilation (phaseMultiplicationKernel f)).domain, a.val = u.val ∧
      ∃ ap : (generalizedAnnihilation (phaseMultiplicationKernel f)).domain,
        ap.val = electronMomentumCoordinate j ⟨u.val,hp⟩ ∧
      ∃ b : (generalizedAnnihilation (phaseMultiplicationKernel (weylMomentumCoefficient f j hj))).domain,
        b.val = u.val ∧
      ∃ hpa : generalizedAnnihilation (phaseMultiplicationKernel f) a ∈ (electronMomentumCoordinate j).domain,
        electronMomentumCoordinate j ⟨generalizedAnnihilation (phaseMultiplicationKernel f) a,hpa⟩ =
          generalizedAnnihilation (phaseMultiplicationKernel f) ap +
            generalizedAnnihilation (phaseMultiplicationKernel (weylMomentumCoefficient f j hj)) b := by
  let U := commutatorSourceGraphInput u
  have hU : freeGraphDomainInclusion U = u.val := commutatorSourceGraphInput_value u
  have hp := (commutatorMomentumInput (show freeGraphOperator.domain from U) j).property
  have hp' : u.val ∈ (electronMomentumCoordinate j).domain := hp
  have h₁ := commutatorPhaseAnnihilatorMap_graph f (commutatorGraphRootMap U)
  rw [commutatorGraphRootMap_value,hU] at h₁
  obtain ⟨a,ha,haout⟩ := (generalizedAnnihilation (phaseMultiplicationKernel f)).mem_graph_iff.mp h₁
  have h₂ := commutatorPhaseAnnihilatorMap_graph f (commutatorGraphMomentumRootMap j U)
  rw [commutatorGraphMomentumRootMap_value] at h₂
  obtain ⟨ap,hap,hapout⟩ := (generalizedAnnihilation (phaseMultiplicationKernel f)).mem_graph_iff.mp h₂
  have h₃ := commutatorPhaseAnnihilatorMap_graph (weylMomentumCoefficient f j hj) (commutatorGraphRootMap U)
  rw [commutatorGraphRootMap_value,hU] at h₃
  obtain ⟨b,hb,hbout⟩ := (generalizedAnnihilation (phaseMultiplicationKernel (weylMomentumCoefficient f j hj))).mem_graph_iff.mp h₃
  have hg := commutatorAnnihilator_graph_all f j hj U
  change (commutatorPhaseAnnihilatorMap f (commutatorGraphRootMap U),
    commutatorPhaseAnnihilatorMap f (commutatorGraphMomentumRootMap j U) +
      commutatorPhaseAnnihilatorMap (weylMomentumCoefficient f j hj) (commutatorGraphRootMap U)) ∈ _ at hg
  dsimp only [Prod.fst,Prod.snd] at ha haout hap hapout hb hbout
  rw [← haout,← hapout,← hbout] at hg
  have hpa := (electronMomentumCoordinate j).mem_domain_of_mem_graph hg
  refine ⟨hp',a,ha,ap,hap,b,hb,hpa,?_⟩
  exact (electronMomentumCoordinate j).mem_graph_snd_inj ((electronMomentumCoordinate j).mem_graph ⟨_,hpa⟩) hg rfl

lemma commutatorGraphRootMap_norm (u : FreeGraphDomain) : ‖commutatorGraphRootMap u‖ ≤ ‖u‖ := by
  rw [← fiberPhysicalRoot_norm,freeGraphDomain_norm]
  exact (commutator_graph_shiftedRoot u).choose_spec

lemma commutatorGraphMomentumRootMap_norm (j : Fin 3) (u : FreeGraphDomain) :
    ‖commutatorGraphMomentumRootMap j u‖ ≤ ‖u‖ := by
  rw [← fiberPhysicalRoot_norm,freeGraphDomain_norm]
  exact (commutator_coordinate_shiftedRoot u j).choose_spec.choose_spec

lemma commutatorPhaseCreatorMap_bound (f : OneBoson) (u : FiberPhysicalRoot) :
    ‖commutatorPhaseCreatorMap f u‖ ≤ ‖f‖*‖u‖ := by
  exact (fiberGeneralizedCreator_bound (phaseMultiplicationKernel f) u).trans_eq
    (congrArg (fun c : ℝ => c*‖u‖) (phaseMultiplicationKernel_norm f))

lemma commutatorPhaseAnnihilatorMap_bound (f : OneBoson) (u : FiberPhysicalRoot) :
    ‖commutatorPhaseAnnihilatorMap f u‖ ≤ ‖f‖*‖u‖ := by
  unfold commutatorPhaseAnnihilatorMap
  rw [← commutatorPhase_kernel,fiberAnnihilationMap_identification_root]
  exact fiberAnnihilatorClass_bound (phaseAt f) (phaseAt_continuous f).aestronglyMeasurable
    (commutatorPhase_norm_bound f) u

lemma commutatorCreator_right_terms_bound (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) (u : FreeGraphDomain) :
    ‖commutatorPhaseCreatorMap f (commutatorGraphMomentumRootMap j u)‖ +
      ‖commutatorPhaseCreatorMap (weylMomentumCoefficient f j hj) (commutatorGraphRootMap u)‖ ≤
        (‖f‖+‖weylMomentumCoefficient f j hj‖)*‖u‖ := by
  calc
    _ ≤ ‖f‖*‖commutatorGraphMomentumRootMap j u‖+
        ‖weylMomentumCoefficient f j hj‖*‖commutatorGraphRootMap u‖ :=
      add_le_add (commutatorPhaseCreatorMap_bound _ _) (commutatorPhaseCreatorMap_bound _ _)
    _ ≤ ‖f‖*‖u‖+‖weylMomentumCoefficient f j hj‖*‖u‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (commutatorGraphMomentumRootMap_norm j u) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (commutatorGraphRootMap_norm u) (norm_nonneg _))
    _ = _ := (add_mul _ _ _).symm

lemma commutatorAnnihilator_right_terms_bound (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) (u : FreeGraphDomain) :
    ‖commutatorPhaseAnnihilatorMap f (commutatorGraphMomentumRootMap j u)‖ +
      ‖commutatorPhaseAnnihilatorMap (weylMomentumCoefficient f j hj) (commutatorGraphRootMap u)‖ ≤
        (‖f‖+‖weylMomentumCoefficient f j hj‖)*‖u‖ := by
  calc
    _ ≤ ‖f‖*‖commutatorGraphMomentumRootMap j u‖+
        ‖weylMomentumCoefficient f j hj‖*‖commutatorGraphRootMap u‖ :=
      add_le_add (commutatorPhaseAnnihilatorMap_bound _ _) (commutatorPhaseAnnihilatorMap_bound _ _)
    _ ≤ ‖f‖*‖u‖+‖weylMomentumCoefficient f j hj‖*‖u‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (commutatorGraphMomentumRootMap_norm j u) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (commutatorGraphRootMap_norm u) (norm_nonneg _))
    _ = _ := (add_mul _ _ _).symm


end GW.Fock
