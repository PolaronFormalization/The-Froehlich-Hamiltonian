module
public import GW.Fock.FockWeylCurveDerivative
public import GW.Fock.FockFiberWeyl
public import GW.Analysis.BridgeStrongWeak
public import GW.Operators.BasicWeakDerivative
public import Mathlib.MeasureTheory.Group.Integral
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal
namespace GW.Fock
open GW.Analysis


def weylPhaseIsometry (x : GW.Space) : OneBoson →ₗᵢ[ℂ] OneBoson where
  toLinearMap := (boundedMultiplier (fun k => physicalPhase k x) (by
    unfold physicalPhase
    fun_prop) (C := 1) (Eventually.of_forall (fun k => (physicalPhase_norm k x).le))).toLinearMap
  norm_map' f := phaseAt_norm f x

lemma weylPhase_inner (f g : OneBoson) (x : GW.Space) :
    ⟪phaseAt f x,phaseAt g x⟫_ℂ = ⟪f,g⟫_ℂ :=
  (weylPhaseIsometry x).inner_map_map f g

lemma weylPhase_smul (c : ℂ) (f : OneBoson) (x : GW.Space) :
    phaseAt (c • f) x = c • phaseAt f x :=
  (weylPhaseIsometry x).map_smul c f

lemma weylPhase_axis_inner_integrable (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) :
    Integrable (fun k : GW.Space => phaseLineCoefficient (k j)*((‖f k‖^2 : ℝ):ℂ)) volume := by
  have hi := L2.integrable_inner (𝕜 := ℂ) f (phaseAxisCoefficient f j hj)
  apply hi.congr
  filter_upwards [phaseAxisCoefficient_ae f j hj] with k hk
  rw [hk]
  change ⟪f k,phaseLineCoefficient (k j) • f k⟫_ℂ = _
  rw [inner_smul_right,inner_self_eq_norm_sq_to_K]
  change phaseLineCoefficient (k j)*(‖f k‖:ℂ)^2 = phaseLineCoefficient (k j)*((‖f k‖^2:ℝ):ℂ)
  push_cast
  rfl

lemma weylPhase_axis_inner_zero (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2) :
    ⟪f,phaseAxisCoefficient f j hj⟫_ℂ = 0 := by
  let r := fun k : GW.Space => phaseLineCoefficient (k j)*((‖f k‖^2 : ℝ):ℂ)
  have he : ⟪f,phaseAxisCoefficient f j hj⟫_ℂ = ∫ k, r k ∂volume := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [phaseAxisCoefficient_ae f j hj] with k hk
    rw [hk]
    change ⟪f k,phaseLineCoefficient (k j) • f k⟫_ℂ = _
    rw [inner_smul_right,inner_self_eq_norm_sq_to_K]
    change phaseLineCoefficient (k j)*(‖f k‖:ℂ)^2 = phaseLineCoefficient (k j)*((‖f k‖^2:ℝ):ℂ)
    push_cast
    rfl
  have ho : (fun k => r (-k)) =ᵐ[(volume : Measure GW.Space)] fun k => -r k := by
    filter_upwards [heven] with k hk
    dsimp only [r]
    rw [hk]
    have hn : (-k) j = -(k j) := rfl
    rw [hn]
    unfold phaseLineCoefficient
    push_cast
    ring
  have hh : (∫ k, r k ∂volume) = -(∫ k, r k ∂volume) := by
    calc
      _ = ∫ k, r (-k) ∂volume := (integral_neg_eq_self r (volume : Measure GW.Space)).symm
      _ = ∫ k, -r k ∂volume := integral_congr_ae ho
      _ = _ := integral_neg _
  rw [he]
  linear_combination (1/2:ℂ)*hh

lemma weylPhase_modulated_axis_inner_zero (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2) (x : GW.Space) :
    ⟪phaseAt f x,phaseAt (phaseAxisCoefficient f j hj) x⟫_ℂ = 0 := by
  rw [weylPhase_inner,weylPhase_axis_inner_zero f j hj heven]



def weylMomentumCoefficient (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) : OneBoson :=
  hj.toLp (fun k => (k j : ℂ)*f k)

lemma weylMomentumCoefficient_ae (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) :
    weylMomentumCoefficient f j hj =ᵐ[volume] fun k => (k j : ℂ)*f k := MemLp.coeFn_toLp _

lemma weylPhase_axis_coefficient (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) :
    phaseAxisCoefficient f j hj = (-Complex.I) • weylMomentumCoefficient f j hj := by
  apply Lp.ext
  filter_upwards [phaseAxisCoefficient_ae f j hj,
    Lp.coeFn_smul (-Complex.I) (weylMomentumCoefficient f j hj),weylMomentumCoefficient_ae f j hj] with k hd hs hm
  rw [hd,hs,Pi.smul_apply,hm]
  unfold phaseAxisCoefficientRep phaseLineCoefficient
  simp only [smul_eq_mul,Complex.ofReal_neg]
  ring

set_option backward.isDefEq.respectTransparency.types false in
lemma weylDerivative_generator_neg_I (g : OneBoson) (u : FiberRootDomain) :
    weylCurveGenerator ((-Complex.I) • g) u = (-Complex.I) • ordinaryFieldHalfMap g u := by
  have hz : fieldOrbit g 0 u = u := by
    apply Subtype.ext
    change weylUnitary ((0:ℝ) • (Complex.I • g)) (numberDomainEmbedding (1/2) (by norm_num) u) = _
    rw [zero_smul,weylCurve_zero_action,numberDomainEmbedding_apply]
    rfl
  have hd := fieldOrbit_hasDerivAt g u 0
  change HasDerivAt (fun t : ℝ => fieldOrbitValue g t u)
    (Complex.I • ordinaryFieldHalfMap g (fieldOrbit g 0 u)) 0 at hd
  rw [hz] at hd
  have hc := HasDerivAt.scomp_of_eq 0 hd (hasDerivAt_neg (0:ℝ)) (neg_zero).symm
  have he : (fun s : ℝ => fieldOrbitValue g (-s) u) =
      fun s : ℝ => weylUnitary (s • ((-Complex.I) • g)) (numberDomainEmbedding (1/2) (by norm_num) u) := by
    funext s
    rw [fieldOrbitValue_apply]
    apply congrArg (fun h : OneBoson => weylUnitary h (numberDomainEmbedding (1/2) (by norm_num) u))
    calc
      (-s) • (Complex.I • g) = -(s • (Complex.I • g)) := neg_smul s _
      _ = s • ((-Complex.I) • g) := by rw [neg_smul,smul_neg]
  change HasDerivAt (fun s : ℝ => fieldOrbitValue g (-s) u)
    ((-1:ℝ) • (Complex.I • ordinaryFieldHalfMap g u)) 0 at hc
  rw [he] at hc
  have hm : (-1:ℝ) • (Complex.I • ordinaryFieldHalfMap g u) =
      (-Complex.I) • ordinaryFieldHalfMap g u := by
    rw [neg_one_smul,neg_smul]
  rw [hm] at hc
  exact (weylCurve_line_hasDerivAt_zero ((-Complex.I) • g) u).unique hc

set_option backward.isDefEq.respectTransparency.types false in
lemma weylPhase_hasStrongPartial (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2)
    (u : FiberRootDomain) :
    HasStrongPartial (fun x => weylUnitary (phaseAt f x) (numberDomainEmbedding (1/2) (by norm_num) u))
      (fun x => (-Complex.I) • weylUnitary (phaseAt f x)
        (ordinaryFieldHalfMap (phaseAt (weylMomentumCoefficient f j hj) x) u)) j := by
  intro x
  have hh := weylCurve_hasDerivAt (fun t : ℝ => phaseAt f (x+t • momentumAxis j)) 0
    (phaseAt (phaseAxisCoefficient f j hj) x) (phaseAt_axis_hasDerivAt f j hj x) u
  simp only [zero_smul,add_zero] at hh
  rw [weylPhase_modulated_axis_inner_zero f j hj heven x,Complex.zero_im,
    Complex.ofReal_zero,mul_zero,zero_smul,add_zero] at hh
  rw [weylPhase_axis_coefficient,weylPhase_smul,weylDerivative_generator_neg_I,map_smul] at hh
  exact hh



lemma weylDerivative_fieldHalf_joint_continuous :
    Continuous (fun p : OneBoson × FiberRootDomain => ordinaryFieldHalfMap p.1 p.2) := by
  have he : (fun p : OneBoson × FiberRootDomain => ordinaryFieldHalfMap p.1 p.2) =
      fun p => fiberOrdinaryAnnihilator p.1 p.2+fiberOrdinaryCreator p.1 p.2 :=
    funext (fun p => (fiberOrdinaryField_eq p.1 p.2).symm)
  rw [he]
  exact fiberOrdinaryAnnihilator_continuous.add fiberOrdinaryCreator_continuous

def weylPhaseOrbit (f : OneBoson) (u : FiberRootDomain) (x : GW.Space) : Carrier :=
  weylUnitary (phaseAt f x) (numberDomainEmbedding (1/2) (by norm_num) u)

def weylPhaseOrbitDerivative (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) (u : FiberRootDomain) (x : GW.Space) : Carrier :=
  (-Complex.I) • weylUnitary (phaseAt f x) (ordinaryFieldHalfMap (phaseAt (weylMomentumCoefficient f j hj) x) u)

set_option backward.isDefEq.respectTransparency.types false in
lemma weylPhaseOrbit_continuous (f : OneBoson) (u : FiberRootDomain) : Continuous (weylPhaseOrbit f u) := by
  let v : Carrier := numberDomainEmbedding (1/2) (by norm_num) u
  have hc : Continuous (fun x : GW.Space => (phaseAt f x,v)) :=
    (phaseAt_continuous f).prodMk continuous_const
  have hh := weylCurveAction_joint_continuous.comp hc
  convert! hh using 1 <;> rfl

set_option backward.isDefEq.respectTransparency.types false in
lemma weylPhaseOrbitDerivative_continuous (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) (u : FiberRootDomain) :
    Continuous (weylPhaseOrbitDerivative f j hj u) := by
  have hf := phaseAt_continuous f
  have hg := weylDerivative_fieldHalf_joint_continuous.comp
    ((phaseAt_continuous (weylMomentumCoefficient f j hj)).prodMk (continuous_const : Continuous (fun _ : GW.Space => u)))
  exact (weylCurveAction_joint_continuous.comp (hf.prodMk hg)).const_smul (-Complex.I)

lemma weylPhaseOrbitDerivative_bound (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) (u : FiberRootDomain) (x : GW.Space) :
    ‖weylPhaseOrbitDerivative f j hj u x‖ ≤ 2*‖weylMomentumCoefficient f j hj‖*‖u‖ := by
  change ‖(-Complex.I) • weylUnitary (phaseAt f x)
    (ordinaryFieldHalfMap (phaseAt (weylMomentumCoefficient f j hj) x) u)‖ ≤ _
  rw [norm_smul,norm_neg,Complex.norm_I,one_mul,LinearIsometryEquiv.norm_map]
  have hh := ordinaryFieldHalfLinear_norm (phaseAt (weylMomentumCoefficient f j hj) x) u
  rw [phaseAt_norm] at hh
  exact hh

lemma weylPhaseOrbit_contDiff (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2) (u : FiberRootDomain) :
    ContDiff ℝ 1 (weylPhaseOrbit f u) := by
  let d := fun j : Fin 3 => weylPhaseOrbitDerivative f j (hj j) u
  have hd : ∀ j x, HasDerivAt (fun t : ℝ => weylPhaseOrbit f u (x+t • momentumAxis j)) (d j x) 0 :=
    fun j => weylPhase_hasStrongPartial f j (hj j) heven u
  have hc : ∀ j, Continuous (d j) := fun j => weylPhaseOrbitDerivative_continuous f j (hj j) u
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨fun x => axisDerivativeCLM (fun j => d j x),?_,axisDerivative_hasFDerivAt hd hc⟩
  unfold axisDerivativeCLM
  apply continuous_finsetSum
  intro j _
  exact ((ContinuousLinearMap.smulRightL ℝ GW.Space Carrier
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j)).continuous).comp (hc j)



lemma weylDerivative_strongPartial_smul {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {a a' : GW.Space → ℂ} {v v' : GW.Space → E} {j : Fin 3}
    (ha : HasStrongPartial a a' j) (hv : HasStrongPartial v v' j) :
    HasStrongPartial (fun x => a x • v x) (fun x => a' x • v x+a x • v' x) j := by
  intro x
  have hh := (ha x).smul (hv x)
  simp only [zero_smul,add_zero] at hh
  convert! hh using 1
  exact add_comm _ _

lemma weylDerivative_compact_momentum_graph {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {v d : GW.Space → E} {j : Fin 3}
    (hv : Continuous v) (hvs : HasCompactSupport v) (hvd : HasStrongPartial v d j) (hd : Continuous d) :
    (compactFunctionL2 v hv hvs,
      (-Complex.I) • compactFunctionL2 d hd (strongPartial_hasCompactSupport hvs hvd)) ∈
        (momentumOperator j).graph := by
  apply (momentum_graph_iff_weak j _ _).mpr
  intro φ e
  let w := scalarSchwartzVector φ.toSchwartzMap e
  have hw : ContDiff ℝ 1 (w : GW.Space → E) := w.smooth 1
  have hws : HasCompactSupport (w : GW.Space → E) := by
    change HasCompactSupport (fun x => φ.value x • e)
    exact φ.compact.smul_right
  let D := smoothTestAxisDerivative (w : GW.Space → E) j
  have hD := smoothTestAxisDerivative_continuous (w : GW.Space → E) j hw
  have hwd := smoothTest_hasStrongPartial (w : GW.Space → E) j hw
  have hc : compactFunctionL2 w hw.continuous hws = w.toLp 2 (volume : Measure GW.Space) := by
    apply Lp.ext
    exact (compactFunctionL2_ae w hw.continuous hws).trans (w.coeFn_toLp 2 volume).symm
  have hm : (-Complex.I) • compactFunctionL2 D hD (strongPartial_hasCompactSupport hws hwd) =
      (schwartzMomentumDerivative j w).toLp 2 (volume : Measure GW.Space) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_smul (-Complex.I)
        (compactFunctionL2 D hD (strongPartial_hasCompactSupport hws hwd)),
      compactFunctionL2_ae D hD (strongPartial_hasCompactSupport hws hwd),
      (schwartzMomentumDerivative j w).coeFn_toLp 2 (volume : Measure GW.Space)] with x hs hd hm
    rw [hs,Pi.smul_apply,hd,hm]
    rfl
  have h := strongPartial_weakMomentum hv hvs hvd hd hw.continuous hws hwd hD
  rw [hc,hm] at h
  exact h



def weylPhaseProduct (f : OneBoson) (u : FiberRootDomain) (γ : SmoothScalarTest) (x : GW.Space) : Carrier :=
  γ.value x • weylPhaseOrbit f u x

def weylPhaseProductDerivative (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (u : FiberRootDomain) (γ : SmoothScalarTest) (x : GW.Space) : Carrier :=
  fderiv ℝ γ.value x (momentumAxis j) • weylPhaseOrbit f u x+
    γ.value x • weylPhaseOrbitDerivative f j hj u x

lemma weylPhaseProduct_continuous (f : OneBoson) (u : FiberRootDomain) (γ : SmoothScalarTest) :
    Continuous (weylPhaseProduct f u γ) := γ.smooth.continuous.smul (weylPhaseOrbit_continuous f u)

lemma weylPhaseProduct_compact (f : OneBoson) (u : FiberRootDomain) (γ : SmoothScalarTest) :
    HasCompactSupport (weylPhaseProduct f u γ) := γ.compact.smul_right

set_option backward.isDefEq.respectTransparency.types false in
lemma weylPhaseProduct_hasStrongPartial (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2)
    (u : FiberRootDomain) (γ : SmoothScalarTest) :
    HasStrongPartial (weylPhaseProduct f u γ) (weylPhaseProductDerivative f j hj u γ) j := by
  exact weylDerivative_strongPartial_smul
    (smoothTest_hasStrongPartial γ.value j (γ.smooth.of_le (by norm_num)))
    (weylPhase_hasStrongPartial f j hj heven u)

lemma weylPhaseProductDerivative_continuous (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (u : FiberRootDomain) (γ : SmoothScalarTest) : Continuous (weylPhaseProductDerivative f j hj u γ) := by
  exact ((smoothTestAxisDerivative_continuous γ.value j (γ.smooth.of_le (by norm_num))).smul
    (weylPhaseOrbit_continuous f u)).add
    (γ.smooth.continuous.smul (weylPhaseOrbitDerivative_continuous f j hj u))

def weylPhaseProductClass (f : OneBoson) (u : FiberRootDomain) (γ : SmoothScalarTest) : Physical :=
  compactFunctionL2 (weylPhaseProduct f u γ) (weylPhaseProduct_continuous f u γ) (weylPhaseProduct_compact f u γ)

lemma weylPhaseProductClass_ae (f : OneBoson) (u : FiberRootDomain) (γ : SmoothScalarTest) :
    weylPhaseProductClass f u γ =ᵐ[volume] fun x => γ.value x •
      weylUnitary (phaseAt f x) (numberDomainEmbedding (1/2) (by norm_num) u) :=
  compactFunctionL2_ae _ _ _

set_option backward.isDefEq.respectTransparency.types false in
lemma weylPhaseProduct_momentum_graph (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2)
    (u : FiberRootDomain) (γ : SmoothScalarTest) :
    ∃ V : Physical, (weylPhaseProductClass f u γ,V) ∈ (momentumOperator j).graph ∧
      V =ᵐ[volume] fun x => weylUnitary (phaseAt f x)
        (((-Complex.I)*fderiv ℝ γ.value x (momentumAxis j)) •
          numberDomainEmbedding (1/2) (by norm_num) u-
            γ.value x • ordinaryFieldHalfMap (phaseAt (weylMomentumCoefficient f j hj) x) u) := by
  let D := weylPhaseProductDerivative f j hj u γ
  have hD := weylPhaseProductDerivative_continuous f j hj u γ
  have hd := weylPhaseProduct_hasStrongPartial f j hj heven u γ
  have hs := strongPartial_hasCompactSupport (weylPhaseProduct_compact f u γ) hd
  let A := compactFunctionL2 D hD hs
  refine ⟨(-Complex.I) • A,weylDerivative_compact_momentum_graph
    (weylPhaseProduct_continuous f u γ) (weylPhaseProduct_compact f u γ) hd hD,?_⟩
  filter_upwards [Lp.coeFn_smul (-Complex.I) A,compactFunctionL2_ae D hD hs] with x hA hD
  rw [hA,Pi.smul_apply,hD]
  change (-Complex.I) • (fderiv ℝ γ.value x (momentumAxis j) •
      weylUnitary (phaseAt f x) (numberDomainEmbedding (1/2) (by norm_num) u)+
      γ.value x • ((-Complex.I) • weylUnitary (phaseAt f x)
        (ordinaryFieldHalfMap (phaseAt (weylMomentumCoefficient f j hj) x) u))) = _
  rw [map_sub,map_smul,map_smul,smul_add,smul_smul,smul_smul,smul_smul]
  have hh : ((-Complex.I)*γ.value x)*(-Complex.I) = -γ.value x := by
    calc
      _ = γ.value x*(Complex.I*Complex.I) := by ring
      _ = _ := by rw [Complex.I_mul_I,mul_neg_one]
  rw [hh,neg_smul,sub_eq_add_neg]



lemma weylMomentumCoefficient_modulated_ae (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) (x : GW.Space) :
    phaseAt (weylMomentumCoefficient f j hj) x =ᵐ[volume]
      fun k => (k j : ℂ)*(physicalPhase k x*f k) := by
  filter_upwards [phaseAt_ae (weylMomentumCoefficient f j hj) x,weylMomentumCoefficient_ae f j hj] with k hp hm
  rw [hp,hm]
  ring

lemma weylDerivative_field_original (g : OneBoson) (u : (numberPower Sector (1/2)).domain) :
    ordinaryFieldHalfMap g (numberHalfGraphInput u) = ordinaryField g u := by
  change ordinaryField g (ordinaryFieldHalfInput g (numberHalfGraphInput u)) = ordinaryField g u
  apply congrArg (ordinaryField g).toFun
  exact Subtype.ext (numberHalfGraphInput_embedding u)

set_option backward.isDefEq.respectTransparency.types false in
lemma weyl_phase_hasDerivAt (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2)
    (u : (numberPower Sector (1/2)).domain) (x : GW.Space) :
    HasDerivAt (fun t : ℝ => weylUnitary (phaseAt f (x+t • momentumAxis j)) u.val)
      ((-Complex.I) • weylUnitary (phaseAt f x)
        (ordinaryField (phaseAt (weylMomentumCoefficient f j hj) x) u)) 0 := by
  have hh := weylPhase_hasStrongPartial f j hj heven (numberHalfGraphInput u) x
  dsimp only at hh
  rw [numberHalfGraphInput_embedding,weylDerivative_field_original] at hh
  exact hh

lemma weyl_phase_contDiff (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2)
    (u : (numberPower Sector (1/2)).domain) :
    ContDiff ℝ 1 (fun x : GW.Space => weylUnitary (phaseAt f x) u.val) := by
  have hh := weylPhaseOrbit_contDiff f hj heven (numberHalfGraphInput u)
  change ContDiff ℝ 1 (fun x : GW.Space => weylUnitary (phaseAt f x)
    (numberDomainEmbedding (1/2) (by norm_num) (numberHalfGraphInput u))) at hh
  rw [numberHalfGraphInput_embedding] at hh
  exact hh

def weylGrossProductClass (f : OneBoson) (u : (numberPower Sector (1/2)).domain) (γ : SmoothScalarTest) : Physical :=
  weylPhaseProductClass f (numberHalfGraphInput u) γ

lemma weylGrossProductClass_ae (f : OneBoson) (u : (numberPower Sector (1/2)).domain) (γ : SmoothScalarTest) :
    weylGrossProductClass f u γ =ᵐ[volume] fun x => γ.value x • weylUnitary (phaseAt f x) u.val := by
  have hh := weylPhaseProductClass_ae f (numberHalfGraphInput u) γ
  rw [numberHalfGraphInput_embedding] at hh
  exact hh

set_option backward.isDefEq.respectTransparency.types false in
lemma weyl_gross_product_momentum_graph (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2)
    (u : (numberPower Sector (1/2)).domain) (γ : SmoothScalarTest) :
    ∃ V : Physical, (weylGrossProductClass f u γ,V) ∈ (momentumOperator j).graph ∧
      V =ᵐ[volume] fun x => weylUnitary (phaseAt f x)
        (((-Complex.I)*fderiv ℝ γ.value x (momentumAxis j)) • u.val-
            γ.value x • ordinaryField (phaseAt (weylMomentumCoefficient f j hj) x) u) := by
  have hh := weylPhaseProduct_momentum_graph f j hj heven (numberHalfGraphInput u) γ
  simp_rw [numberHalfGraphInput_embedding,weylDerivative_field_original] at hh
  exact hh

lemma weyl_gross_product_mem_momentum (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2)
    (u : (numberPower Sector (1/2)).domain) (γ : SmoothScalarTest) :
    weylGrossProductClass f u γ ∈ (momentumOperator j).domain := by
  obtain ⟨V,hV,_⟩ := weyl_gross_product_momentum_graph f j hj heven u γ
  exact LinearPMap.mem_domain_of_mem_graph hV

def weylGrossProductMomentumInput (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2)
    (u : (numberPower Sector (1/2)).domain) (γ : SmoothScalarTest) : (momentumOperator (H := Carrier) j).domain :=
  ⟨weylGrossProductClass f u γ,weyl_gross_product_mem_momentum f j hj heven u γ⟩

lemma weyl_gross_product_momentum_action (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2)
    (u : (numberPower Sector (1/2)).domain) (γ : SmoothScalarTest) :
    momentumOperator j (weylGrossProductMomentumInput f j hj heven u γ) =ᵐ[volume]
      fun x => weylUnitary (phaseAt f x)
        (((-Complex.I)*fderiv ℝ γ.value x (momentumAxis j)) • u.val-
            γ.value x • ordinaryField (phaseAt (weylMomentumCoefficient f j hj) x) u) := by
  obtain ⟨V,hV,hAE⟩ := weyl_gross_product_momentum_graph f j hj heven u γ
  have he : momentumOperator j (weylGrossProductMomentumInput f j hj heven u γ) = V :=
    (momentumOperator j).mem_graph_snd_inj
      ((momentumOperator j).mem_graph (weylGrossProductMomentumInput f j hj heven u γ)) hV rfl
  rw [he]
  exact hAE


end GW.Fock
