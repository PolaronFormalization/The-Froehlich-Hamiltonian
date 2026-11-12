module
public import GW.Fock.FockWeylLipschitz
public import GW.Fock.FockFiberFields
@[expose] public section
noncomputable section
open MeasureTheory Filter Set Asymptotics
open scoped Topology InnerProductSpace ENNReal
namespace GW.Fock

lemma weylCurve_zero_action (u : Carrier) : weylUnitary 0 u = u := by
  change weylIsometry 0 u = u
  exact congrArg (fun L : Carrier →L[ℂ] Carrier => L u) weylIsometry_zero

set_option backward.isDefEq.respectTransparency.types false in
lemma weylCurve_rotation (h : OneBoson) : Complex.I • ((-Complex.I) • h) = h := by
  rw [smul_smul]
  have he : Complex.I*(-Complex.I) = 1 := by rw [mul_neg,Complex.I_mul_I,neg_neg]
  rw [he,one_smul]

def weylCurveGenerator (h : OneBoson) : FiberRootDomain →L[ℂ] Carrier :=
  Complex.I • ordinaryFieldHalfMap ((-Complex.I) • h)

set_option backward.isDefEq.respectTransparency.types false in
lemma weylCurveGenerator_bound (h : OneBoson) (u : FiberRootDomain) :
    ‖weylCurveGenerator h u‖ ≤ 2*‖h‖*‖u‖ := by
  change ‖Complex.I • ordinaryFieldHalfMap ((-Complex.I) • h) u‖ ≤ _
  rw [norm_smul,Complex.norm_I,one_mul]
  change ‖ordinaryFieldHalfLinear ((-Complex.I) • h) u‖ ≤ 2*‖h‖*‖u‖
  have hh := ordinaryFieldHalfLinear_norm ((-Complex.I) • h) u
  simpa only [norm_smul,norm_neg,Complex.norm_I,one_mul] using hh

set_option backward.isDefEq.respectTransparency.types false in
lemma weylCurve_line_hasDerivAt_zero (h : OneBoson) (u : FiberRootDomain) :
    HasDerivAt (fun s : ℝ => weylUnitary (s • h) (numberDomainEmbedding (1/2) (by norm_num) u))
      (weylCurveGenerator h u) 0 := by
  let k := (-Complex.I) • h
  have hk : Complex.I • k = h := weylCurve_rotation h
  have hzero : fieldOrbit k 0 u = u := by
    apply Subtype.ext
    change weylUnitary ((0:ℝ) • (Complex.I • k)) (numberDomainEmbedding (1/2) (by norm_num) u) = _
    rw [zero_smul,weylCurve_zero_action,numberDomainEmbedding_apply]
    rfl
  have hd := fieldOrbit_hasDerivAt k u 0
  have hf : (fun s : ℝ => fieldOrbitValue k s u) =
      (fun s : ℝ => weylUnitary (s • h) (numberDomainEmbedding (1/2) (by norm_num) u)) := by
    funext s
    rw [fieldOrbitValue_apply,hk]
  rw [hf] at hd
  change HasDerivAt _ (Complex.I • ordinaryFieldHalfMap k (fieldOrbit k 0 u)) 0 at hd
  rw [hzero] at hd
  exact hd


def weylCurveCreator (h : OneBoson) : FiberRootDomain →L[ℂ] Carrier :=
  ({toFun := fiberOrdinaryCreator h
    map_add' := fiberOrdinaryCreator_add_vector h
    map_smul' := fiberOrdinaryCreator_smul_vector h} : FiberRootDomain →ₗ[ℂ] Carrier).mkContinuous
    ‖h‖ (fiberOrdinaryCreator_bound h)

def weylCurveAnnihilator (h : OneBoson) : FiberRootDomain →L[ℂ] Carrier :=
  ({toFun := fiberOrdinaryAnnihilator h
    map_add' := fiberOrdinaryAnnihilator_add_vector h
    map_smul' := fiberOrdinaryAnnihilator_smul_vector h} : FiberRootDomain →ₗ[ℂ] Carrier).mkContinuous
    ‖h‖ (fiberOrdinaryAnnihilator_bound h)

set_option backward.isDefEq.respectTransparency.types false in
lemma weylCurveGenerator_coherent (h g : OneBoson) :
    weylCurveGenerator h (coherentExponentialWeighted (1/2) (by norm_num) g) =
      (weylCurveCreator h-weylCurveAnnihilator h) (coherentExponentialWeighted (1/2) (by norm_num) g) := by
  let u := coherentExponentialWeighted (1/2) (by norm_num) g
  have hd₁ := weylCurve_line_hasDerivAt_zero h u
  rw [numberDomainEmbedding_apply,coherentExponentialWeighted_ambient] at hd₁
  have hd₂ := weyl_coherent_generator_hasDerivAt h g 0
  rw [zero_smul] at hd₂
  have he := hd₁.unique hd₂
  have hC : (⟨(fiberOrdinaryRootInput u).val,
      creation_mem_shiftedRoot ordinarySectorKernel (ordinaryKernel h) (fiberOrdinaryRootInput u)⟩ : (ordinaryCreation h).domain) =
      weylCoherentCreationInput 0 h g := by
    apply Subtype.ext
    change (fiberOrdinaryRootInput u).val = weylUnitary 0 (exponentialVector g)
    rw [weylCurve_zero_action]
    exact coherentExponentialWeighted_ambient (1/2) (by norm_num) g
  have hA : ordinaryAnnihilationRootInput h (fiberOrdinaryRootInputUnshifted u) =
      weylCoherentAnnihilationInput 0 h g := by
    apply Subtype.ext
    change (fiberOrdinaryRootInput u).val = weylUnitary 0 (exponentialVector g)
    rw [weylCurve_zero_action]
    exact coherentExponentialWeighted_ambient (1/2) (by norm_num) g
  change weylCurveGenerator h u = fiberOrdinaryCreator h u-fiberOrdinaryAnnihilator h u
  exact he.trans (congrArg₂ (fun c a : Carrier => c-a)
    (congrArg (ordinaryCreation h).toFun hC.symm) (congrArg (ordinaryAnnihilation h).toFun hA.symm))

lemma weylCurveGenerator_creation_sub_annihilation (h : OneBoson) (u : FiberRootDomain) :
    weylCurveGenerator h u = fiberOrdinaryCreator h u-fiberOrdinaryAnnihilator h u := by
  let L := weylCurveGenerator h
  let R := weylCurveCreator h-weylCurveAnnihilator h
  have he : Set.EqOn L R (numberHalfCore : Set FiberRootDomain) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨g,rfl⟩ := hv
      exact weylCurveGenerator_coherent h g
    | zero => simp only [map_zero]
    | add x y hx hy ihx ihy => simp only [map_add,ihx,ihy]
    | smul a x hx ih => simp only [map_smul,ih]
  exact (he.closure L.continuous R.continuous) (numberHalfCore_dense u)


lemma weylCurveGenerator_joint_continuous :
    Continuous (fun p : OneBoson × FiberRootDomain => weylCurveGenerator p.1 p.2) := by
  have he : (fun p : OneBoson × FiberRootDomain => weylCurveGenerator p.1 p.2) =
      (fun p : OneBoson × FiberRootDomain => fiberOrdinaryCreator p.1 p.2-fiberOrdinaryAnnihilator p.1 p.2) :=
    funext (fun p => weylCurveGenerator_creation_sub_annihilation p.1 p.2)
  rw [he]
  exact fiberOrdinaryCreator_continuous.sub fiberOrdinaryAnnihilator_continuous

lemma weylCurve_line_creation_sub_annihilation (h : OneBoson) (u : FiberRootDomain) :
    HasDerivAt (fun s : ℝ => weylUnitary (s • h) (numberDomainEmbedding (1/2) (by norm_num) u))
      (fiberOrdinaryCreator h u-fiberOrdinaryAnnihilator h u) 0 := by
  have hd := weylCurve_line_hasDerivAt_zero h u
  rw [weylCurveGenerator_creation_sub_annihilation] at hd
  exact hd


lemma weylCurve_phase_bound (h d : OneBoson) (s : ℝ) :
    |(⟪d,s • h⟫_ℂ).im| ≤ ‖d‖*|s| *‖h‖ := by
  calc
    _ ≤ ‖⟪d,s • h⟫_ℂ‖ := Complex.abs_im_le_norm _
    _ ≤ ‖d‖*‖s • h‖ := norm_inner_le_norm _ _
    _ = _ := by rw [norm_smul,Real.norm_eq_abs]; ring

lemma weylCurve_remainder_littleO (d : ℝ → OneBoson) (h : OneBoson) (u : FiberRootDomain)
    (hd : Tendsto d (𝓝 0) (𝓝 0))
    (hr : (fun s : ℝ => d s-s • h) =o[𝓝 0] fun s => s) :
    (fun s : ℝ => weylUnitary (d s) (numberDomainEmbedding (1/2) (by norm_num) u)-
      weylUnitary (s • h) (numberDomainEmbedding (1/2) (by norm_num) u)) =o[𝓝 0] fun s => s := by
  let A := 2*‖u‖
  let B := ‖h‖*‖numberDomainEmbedding (1/2) (by norm_num) u‖
  have h₁ := hr.norm_left.const_mul_left A
  have hdn : Tendsto (fun s => ‖d s‖) (𝓝 0) (𝓝 0) := by
    simpa only [norm_zero] using hd.norm
  have hsO : (fun s : ℝ => |s|) =O[𝓝 0] fun s => s :=
    isBigO_of_le _ (fun s => by simp only [Real.norm_eq_abs,abs_abs]; exact le_rfl)
  have h₂ : (fun s : ℝ => ‖d s‖*|s|) =o[𝓝 0] fun s => s := by
    have hh := ((isLittleO_one_iff ℝ).mpr hdn).mul_isBigO hsO
    simpa only [one_mul] using hh
  have hsum : (fun s : ℝ => A*‖d s-s • h‖+B*(‖d s‖*|s|)) =o[𝓝 0] fun s => s :=
    h₁.add (h₂.const_mul_left B)
  have hbound : (fun s : ℝ => weylUnitary (d s) (numberDomainEmbedding (1/2) (by norm_num) u)-
      weylUnitary (s • h) (numberDomainEmbedding (1/2) (by norm_num) u)) =O[𝓝 0]
      fun s => A*‖d s-s • h‖+B*(‖d s‖*|s|) := by
    apply isBigO_of_le
    intro s
    rw [Real.norm_of_nonneg (by dsimp [A,B]; positivity)]
    calc
      _ ≤ 2*‖d s-s • h‖*‖u‖+|(⟪d s,s • h⟫_ℂ).im| *‖numberDomainEmbedding (1/2) (by norm_num) u‖ :=
        weyl_difference_graph (d s) (s • h) u
      _ ≤ 2*‖d s-s • h‖*‖u‖+(‖d s‖*|s| *‖h‖)*‖numberDomainEmbedding (1/2) (by norm_num) u‖ :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right (weylCurve_phase_bound h (d s) s) (norm_nonneg _))
      _ = _ := by dsimp [A,B]; ring
  exact hbound.trans_isLittleO hsum


lemma weylCurve_delta_hasDerivAt_zero (d : ℝ → OneBoson) (h : OneBoson) (u : FiberRootDomain)
    (hd : Tendsto d (𝓝 0) (𝓝 0)) (hd0 : d 0 = 0)
    (hr : (fun s : ℝ => d s-s • h) =o[𝓝 0] fun s => s) :
    HasDerivAt (fun s : ℝ => weylUnitary (d s) (numberDomainEmbedding (1/2) (by norm_num) u))
      (weylCurveGenerator h u) 0 := by
  let p := fun s : ℝ => weylUnitary (s • h) (numberDomainEmbedding (1/2) (by norm_num) u)
  let q := fun s : ℝ => weylUnitary (d s) (numberDomainEmbedding (1/2) (by norm_num) u)
  have he0 : q 0-p 0 = 0 := by
    dsimp [p,q]
    rw [hd0,zero_smul,sub_self]
  have he := weylCurve_remainder_littleO d h u hd hr
  have heD : HasDerivAt (fun s => q s-p s) 0 0 := by
    apply hasDerivAt_iff_isLittleO.mpr
    simpa only [he0,sub_zero,smul_zero] using he
  have hp := weylCurve_line_hasDerivAt_zero h u
  have hsum := hp.add heD
  have hf : (fun s => p s+(q s-p s)) = q := funext (fun s => by abel)
  change HasDerivAt (fun s => p s+(q s-p s)) (weylCurveGenerator h u+0) 0 at hsum
  rw [hf,add_zero] at hsum
  exact hsum

lemma weylCurve_increment_hasDerivAt_zero (f : ℝ → OneBoson) (t : ℝ) (h : OneBoson)
    (hf : HasDerivAt f h t) (u : FiberRootDomain) :
    HasDerivAt (fun s : ℝ => weylUnitary (f (t+s)-f t) (numberDomainEmbedding (1/2) (by norm_num) u))
      (weylCurveGenerator h u) 0 := by
  have ht : Tendsto (fun s : ℝ => t+s) (𝓝 0) (𝓝 t) := by
    simpa only [add_zero] using (tendsto_const_nhds.add tendsto_id :
      Tendsto (fun s : ℝ => t+s) (𝓝 0) (𝓝 (t+0)))
  have hd : Tendsto (fun s : ℝ => f (t+s)-f t) (𝓝 0) (𝓝 0) := by
    have hc : Tendsto (fun _ : ℝ => f t) (𝓝 0) (𝓝 (f t)) := tendsto_const_nhds
    simpa only [Function.comp_def,sub_self] using ((hf.continuousAt.tendsto.comp ht).sub hc)
  exact weylCurve_delta_hasDerivAt_zero _ h u hd (by simp only [add_zero,sub_self])
    (hasDerivAt_iff_isLittleO_nhds_zero.mp hf)


set_option backward.isDefEq.respectTransparency.types false in
lemma weylCurve_factor (f d : OneBoson) (u : Carrier) :
    weylUnitary (f+d) u = Complex.exp (Complex.I*((⟪f,d⟫_ℂ).im:ℂ)) • weylUnitary f (weylUnitary d u) := by
  have hh := congrArg (fun L : Carrier →L[ℂ] Carrier => L u) (weylUnitary_mul f d)
  change weylUnitary f (weylUnitary d u) =
    Complex.exp (-Complex.I*((⟪f,d⟫_ℂ).im:ℂ)) • weylUnitary (f+d) u at hh
  rw [hh,smul_smul,← Complex.exp_add]
  have hz : Complex.I*((⟪f,d⟫_ℂ).im:ℂ)+(-Complex.I*((⟪f,d⟫_ℂ).im:ℂ)) = 0 := by ring
  rw [hz,Complex.exp_zero,one_smul]

set_option backward.isDefEq.respectTransparency.types false in
lemma weylCurve_phase_hasDerivAt_zero (f₀ h : OneBoson) (d : ℝ → OneBoson)
    (hd : HasDerivAt d h 0) (hd0 : d 0 = 0) :
    HasDerivAt (fun s : ℝ => Complex.exp (Complex.I*((⟪f₀,d s⟫_ℂ).im:ℂ)))
      (Complex.I*((⟪f₀,h⟫_ℂ).im:ℂ)) 0 := by
  have hin := HasDerivAt.inner ℂ (hasDerivAt_const (0:ℝ) f₀) hd
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hin
  have hc := (hi.ofReal_comp.const_mul Complex.I).cexp
  simpa only [Function.comp_def,Complex.imCLM_apply,inner_zero_left,add_zero,hd0,inner_zero_right,
    Complex.zero_im,Complex.ofReal_zero,mul_zero,Complex.exp_zero,mul_one,one_mul] using hc


set_option backward.isDefEq.respectTransparency.types false in
lemma weylCurve_shifted_hasDerivAt_zero (f₀ h : OneBoson) (d : ℝ → OneBoson)
    (hd : HasDerivAt d h 0) (hd0 : d 0 = 0) (u : FiberRootDomain) :
    HasDerivAt (fun s : ℝ => weylUnitary (f₀+d s) (numberDomainEmbedding (1/2) (by norm_num) u))
      (weylUnitary f₀ (weylCurveGenerator h u+
        (Complex.I*((⟪f₀,h⟫_ℂ).im:ℂ)) • numberDomainEmbedding (1/2) (by norm_num) u)) 0 := by
  have hdt : Tendsto d (𝓝 0) (𝓝 0) := by simpa only [hd0] using hd.continuousAt.tendsto
  have hr : (fun s : ℝ => d s-s • h) =o[𝓝 0] fun s => s := by
    simpa only [hd0,sub_zero] using hd.isLittleO
  have hq := weylCurve_delta_hasDerivAt_zero d h u hdt hd0 hr
  have hp := weylCurve_phase_hasDerivAt_zero f₀ h d hd hd0
  let L : Carrier →L[ℝ] Carrier := (weylUnitary f₀ : Carrier →L[ℂ] Carrier).restrictScalars ℝ
  have hL := L.hasFDerivAt.comp_hasDerivAt 0 hq
  have hh := hp.smul hL
  change HasDerivAt (fun s : ℝ => Complex.exp (Complex.I*((⟪f₀,d s⟫_ℂ).im:ℂ)) •
    weylUnitary f₀ (weylUnitary (d s) (numberDomainEmbedding (1/2) (by norm_num) u)))
    (Complex.exp (Complex.I*((⟪f₀,d 0⟫_ℂ).im:ℂ)) • weylUnitary f₀ (weylCurveGenerator h u)+
      (Complex.I*((⟪f₀,h⟫_ℂ).im:ℂ)) • weylUnitary f₀ (weylUnitary (d 0) (numberDomainEmbedding (1/2) (by norm_num) u))) 0 at hh
  rw [hd0,inner_zero_right,Complex.zero_im,Complex.ofReal_zero,mul_zero,Complex.exp_zero,
    one_smul,weylCurve_zero_action] at hh
  have he : weylUnitary f₀ (weylCurveGenerator h u)+
      (Complex.I*((⟪f₀,h⟫_ℂ).im:ℂ)) • weylUnitary f₀ (numberDomainEmbedding (1/2) (by norm_num) u) =
      weylUnitary f₀ (weylCurveGenerator h u+
        (Complex.I*((⟪f₀,h⟫_ℂ).im:ℂ)) • numberDomainEmbedding (1/2) (by norm_num) u) := by
    rw [map_add,map_smul]
  rw [he] at hh
  have heq : (fun s : ℝ => Complex.exp (Complex.I*((⟪f₀,d s⟫_ℂ).im:ℂ)) •
      weylUnitary f₀ (weylUnitary (d s) (numberDomainEmbedding (1/2) (by norm_num) u))) =
      (fun s : ℝ => weylUnitary (f₀+d s) (numberDomainEmbedding (1/2) (by norm_num) u)) :=
    funext (fun s => (weylCurve_factor f₀ (d s) _).symm)
  rw [heq] at hh
  exact hh

lemma weylCurveAction_joint_continuous : Continuous (fun p : OneBoson × Carrier => weylUnitary p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := Metric.continuousAt_iff.mp (weylUnitary_strong_continuous p₀.2).continuousAt
    (ε/2) (by linarith)
  refine ⟨min δ (ε/2),lt_min hδ (by linarith),?_⟩
  intro p hp
  rw [Prod.dist_eq,max_lt_iff] at hp
  have hf : dist p.1 p₀.1 < δ := lt_of_lt_of_le hp.1 (min_le_left _ _)
  have hu : dist p.2 p₀.2 < ε/2 := lt_of_lt_of_le hp.2 (min_le_right _ _)
  have hm := hd hf
  have ht := dist_triangle (weylUnitary p.1 p.2) (weylUnitary p.1 p₀.2) (weylUnitary p₀.1 p₀.2)
  rw [(weylUnitary p.1).isometry.dist_eq] at ht
  linarith

set_option backward.isDefEq.respectTransparency.types false in
lemma weylCurveDerivative_continuousOn (J : Set ℝ) (f d : ℝ → OneBoson)
    (hf : ContinuousOn f J) (hd : ContinuousOn d J) (u : FiberRootDomain) :
    ContinuousOn (fun t => weylUnitary (f t) (weylCurveGenerator (d t) u+
      (Complex.I*((⟪f t,d t⟫_ℂ).im:ℂ)) • numberDomainEmbedding (1/2) (by norm_num) u)) J := by
  have hG : ContinuousOn (fun t => weylCurveGenerator (d t) u) J := by
    have hh := weylCurveGenerator_joint_continuous.comp_continuousOn
      (hd.prodMk (continuousOn_const : ContinuousOn (fun _ : ℝ => u) J))
    convert! hh using 1 <;> rfl
  have hI : ContinuousOn (fun t => ⟪f t,d t⟫_ℂ) J := by
    have hh := (continuous_inner : Continuous (fun p : OneBoson × OneBoson => ⟪p.1,p.2⟫_ℂ)).comp_continuousOn
      (hf.prodMk hd)
    convert! hh using 1 <;> rfl
  have hC := (Complex.continuous_ofReal.comp_continuousOn (Complex.continuous_im.comp_continuousOn hI)).const_mul Complex.I
  have hS := hC.smul (continuousOn_const : ContinuousOn
    (fun _ : ℝ => numberDomainEmbedding (1/2) (by norm_num) u) J)
  have hh := weylCurveAction_joint_continuous.comp_continuousOn (hf.prodMk (hG.add hS))
  convert! hh using 1 <;> rfl


set_option backward.isDefEq.respectTransparency.types false in
lemma weylCurve_hasDerivAt (f : ℝ → OneBoson) (t : ℝ) (h : OneBoson)
    (hf : HasDerivAt f h t) (u : FiberRootDomain) :
    HasDerivAt (fun s : ℝ => weylUnitary (f s) (numberDomainEmbedding (1/2) (by norm_num) u))
      (weylUnitary (f t) (weylCurveGenerator h u+
        (Complex.I*((⟪f t,h⟫_ℂ).im:ℂ)) • numberDomainEmbedding (1/2) (by norm_num) u)) t := by
  have hft : HasDerivAt f h (t+0) := by simpa only [add_zero] using hf
  have hd := (hft.comp_const_add t 0).sub_const (f t)
  have hz : f (t+0)-f t = 0 := by simp only [add_zero,sub_self]
  have hh := weylCurve_shifted_hasDerivAt_zero (f t) h (fun s => f (t+s)-f t) hd hz u
  have heq : (fun s : ℝ => weylUnitary (f t+(f (t+s)-f t)) (numberDomainEmbedding (1/2) (by norm_num) u)) =
      (fun s : ℝ => weylUnitary (f (t+s)) (numberDomainEmbedding (1/2) (by norm_num) u)) := by
    funext s
    congr 1
    congr 1
    abel
  rw [heq] at hh
  have hh' : HasDerivAt (fun s : ℝ => weylUnitary (f (t+s)) (numberDomainEmbedding (1/2) (by norm_num) u))
      (weylUnitary (f t) (weylCurveGenerator h u+
        (Complex.I*((⟪f t,h⟫_ℂ).im:ℂ)) • numberDomainEmbedding (1/2) (by norm_num) u)) (t-t) := by
    simpa only [sub_self] using hh
  have hfinal := hh'.comp_sub_const t t
  have heq' : (fun s : ℝ => weylUnitary (f (t+(s-t))) (numberDomainEmbedding (1/2) (by norm_num) u)) =
      (fun s : ℝ => weylUnitary (f s) (numberDomainEmbedding (1/2) (by norm_num) u)) := by
    funext s
    congr 1
    congr 1
    abel
  rw [heq'] at hfinal
  exact hfinal

lemma weylCurve_contDiffOn (J : Set ℝ) (hJ : IsOpen J) (f : ℝ → OneBoson)
    (hf : ContDiffOn ℝ 1 f J) (u : FiberRootDomain) :
    ContDiffOn ℝ 1 (fun t => weylUnitary (f t) (numberDomainEmbedding (1/2) (by norm_num) u)) J := by
  let F := fun t => weylUnitary (f t) (numberDomainEmbedding (1/2) (by norm_num) u)
  let D := fun t => weylUnitary (f t) (weylCurveGenerator (deriv f t) u+
    (Complex.I*((⟪f t,deriv f t⟫_ℂ).im:ℂ)) • numberDomainEmbedding (1/2) (by norm_num) u)
  have hd (t : ℝ) (ht : t ∈ J) : HasDerivAt F (D t) t :=
    weylCurve_hasDerivAt f t (deriv f t)
      (((hf.differentiableOn_one t ht).differentiableAt (hJ.mem_nhds ht)).hasDerivAt) u
  have hc : ContinuousOn D J := weylCurveDerivative_continuousOn J f (deriv f) hf.continuousOn
    (hf.continuousOn_deriv_of_isOpen hJ le_rfl) u
  apply (contDiffOn_one_iff_derivWithin hJ.uniqueDiffOn).mpr
  refine ⟨fun t ht => (hd t ht).differentiableAt.differentiableWithinAt,?_⟩
  apply hc.congr
  intro t ht
  exact (hd t ht).hasDerivWithinAt.derivWithin (hJ.uniqueDiffOn t ht)

set_option backward.isDefEq.respectTransparency.types false in
lemma weylCurveGenerator_original (h : OneBoson) (u : (numberPower Sector (1/2)).domain) :
    weylCurveGenerator h (numberHalfGraphInput u) =
      ordinaryCreation h (ordinaryCreationRootInput h u)-ordinaryAnnihilation h (ordinaryAnnihilationRootInput h u) := by
  rw [weylCurveGenerator_creation_sub_annihilation]
  have hv : (fiberOrdinaryRootInput (numberHalfGraphInput u)).val = u.val :=
    (numberDomainEmbedding_apply (1/2) (by norm_num) (numberHalfGraphInput u)).symm.trans
      (numberHalfGraphInput_embedding u)
  have hc : (⟨(fiberOrdinaryRootInput (numberHalfGraphInput u)).val,
      creation_mem_shiftedRoot ordinarySectorKernel (ordinaryKernel h) (fiberOrdinaryRootInput (numberHalfGraphInput u))⟩ :
      (ordinaryCreation h).domain) = ordinaryCreationRootInput h u := Subtype.ext hv
  have ha : ordinaryAnnihilationRootInput h (fiberOrdinaryRootInputUnshifted (numberHalfGraphInput u)) =
      ordinaryAnnihilationRootInput h u := Subtype.ext hv
  exact congrArg₂ (fun c a : Carrier => c-a) (congrArg (ordinaryCreation h).toFun hc)
    (congrArg (ordinaryAnnihilation h).toFun ha)

set_option backward.isDefEq.respectTransparency.types false in
lemma weyl_curve_hasDerivAt (f : ℝ → OneBoson) (t : ℝ) (h : OneBoson)
    (hf : HasDerivAt f h t) (u : (numberPower Sector (1/2)).domain) :
    HasDerivAt (fun s : ℝ => weylUnitary (f s) u.val)
      (weylUnitary (f t) (ordinaryCreation h (ordinaryCreationRootInput h u)-
        ordinaryAnnihilation h (ordinaryAnnihilationRootInput h u)+
        (Complex.I*((⟪f t,h⟫_ℂ).im:ℂ)) • u.val)) t := by
  have hh := weylCurve_hasDerivAt f t h hf (numberHalfGraphInput u)
  rw [numberHalfGraphInput_embedding,weylCurveGenerator_original] at hh
  exact hh

lemma weyl_curve_contDiffOn (J : Set ℝ) (hJ : IsOpen J) (f : ℝ → OneBoson)
    (hf : ContDiffOn ℝ 1 f J) (u : (numberPower Sector (1/2)).domain) :
    ContDiffOn ℝ 1 (fun t => weylUnitary (f t) u.val) J ∧
      ∀ t ∈ J, HasDerivAt (fun s : ℝ => weylUnitary (f s) u.val)
        (weylUnitary (f t) (ordinaryCreation (deriv f t) (ordinaryCreationRootInput (deriv f t) u)-
          ordinaryAnnihilation (deriv f t) (ordinaryAnnihilationRootInput (deriv f t) u)+
          (Complex.I*((⟪f t,deriv f t⟫_ℂ).im:ℂ)) • u.val)) t := by
  constructor
  · have hh := weylCurve_contDiffOn J hJ f hf (numberHalfGraphInput u)
    rw [numberHalfGraphInput_embedding] at hh
    exact hh
  · intro t ht
    exact weyl_curve_hasDerivAt f t (deriv f t)
      (((hf.differentiableOn_one t ht).differentiableAt (hJ.mem_nhds ht)).hasDerivAt) u

end GW.Fock
