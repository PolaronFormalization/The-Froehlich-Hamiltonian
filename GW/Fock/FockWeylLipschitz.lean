module
public import GW.Fock.FockFieldSelfadjoint
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal Interval
namespace GW.Fock

lemma weyl_phase_error (θ : ℝ) : ‖Complex.exp (Complex.I*(θ:ℂ))-1‖ ≤ |θ| := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one,Real.norm_eq_abs,abs_mul]
  norm_num only [show |(2:ℝ)| = 2 by norm_num]
  calc
    (2:ℝ)*|Real.sin (θ/2)| ≤ 2*|θ/2| := mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
    _ = |θ| := by rw [abs_div]; norm_num <;> ring

lemma weyl_zero_apply (u : Carrier) : weylUnitary 0 u = u := by
  change weylIsometry 0 u = u
  exact congrArg (fun L : Carrier →L[ℂ] Carrier => L u) weylIsometry_zero

def fieldHalfClosureInput (f : OneBoson) (u : NumberWeightedDomain Sector (1/2) (by norm_num)) :
    (ordinaryFieldClosure f).domain :=
  ⟨numberDomainEmbedding (1/2) (by norm_num) u,(ordinaryFieldClosure_extends f).1 (ordinaryFieldHalfInput f u).property⟩

lemma fieldHalfClosureInput_action (f : OneBoson) (u : NumberWeightedDomain Sector (1/2) (by norm_num)) :
    ordinaryFieldClosure f (fieldHalfClosureInput f u) = ordinaryFieldHalfMap f u := by
  change ordinaryFieldClosure f (fieldHalfClosureInput f u) = ordinaryField f (ordinaryFieldHalfInput f u)
  exact ((ordinaryFieldClosure_extends f).2 rfl).symm

set_option backward.isDefEq.respectTransparency.types false in
lemma weyl_increment_graph (h : OneBoson) (u : NumberWeightedDomain Sector (1/2) (by norm_num)) :
    ‖weylUnitary h (numberDomainEmbedding (1/2) (by norm_num) u)-numberDomainEmbedding (1/2) (by norm_num) u‖ ≤
      2*‖h‖*‖u‖ := by
  let v : (ordinaryMomentumFieldClosure h).domain := fieldHalfClosureInput (Complex.I • h) u
  let d : ℝ → Carrier := fun t => (-Complex.I) • weylUnitary (t • h) (ordinaryFieldHalfMap (Complex.I • h) u)
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => weylUnitary (s • h) (numberDomainEmbedding (1/2) (by norm_num) u)) (d t) t := by
    have hh := momentumWeylClosure_hasDerivAt h v t
    have he : ordinaryMomentumFieldClosure h (momentumWeylClosureInput h t v) =
        weylUnitary (t • h) (ordinaryFieldHalfMap (Complex.I • h) u) := by
      have ha := fieldWeylClosure_action (Complex.I • h) (-t) v
      rw [field_pi_phase,fieldHalfClosureInput_action] at ha
      exact ha
    rw [he] at hh
    exact hh
  have hc : Continuous d := by
    have hh : Continuous (fun t : ℝ => t • h) := by fun_prop
    exact ((weylUnitary_strong_continuous (ordinaryFieldHalfMap (Complex.I • h) u)).comp hh).fun_const_smul (-Complex.I)
  have hb (t : ℝ) : ‖d t‖ ≤ 2*‖h‖*‖u‖ := by
    change ‖(-Complex.I) • weylUnitary (t • h) (ordinaryFieldHalfMap (Complex.I • h) u)‖ ≤ _
    rw [norm_smul,norm_neg,Complex.norm_I,one_mul,LinearIsometryEquiv.norm_map]
    have he := ordinaryFieldHalfLinear_norm (Complex.I • h) u
    rw [norm_smul,Complex.norm_I,one_mul] at he
    exact he
  have hFTC : (∫ t in (0:ℝ)..1, d t) =
      weylUnitary h (numberDomainEmbedding (1/2) (by norm_num) u)-numberDomainEmbedding (1/2) (by norm_num) u := by
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hc.intervalIntegrable 0 1)
    simpa only [one_smul,zero_smul,weyl_zero_apply] using hh
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1) (f := d) (fun t _ => hb t)
  rw [hFTC] at hi
  norm_num only [sub_zero,abs_one,mul_one] at hi
  exact hi


lemma weyl_negative_inner_im (f g : OneBoson) : (⟪-g,f⟫_ℂ).im = (⟪f,g⟫_ℂ).im := by
  rw [inner_neg_left,Complex.neg_im]
  have hh := congrArg (fun r : ℝ => -r) (inner_im_symm (𝕜 := ℂ) g f)
  simp only [neg_neg] at hh
  convert! hh using 1 <;> rfl

set_option backward.isDefEq.respectTransparency.types false in
lemma weyl_difference_split (f g : OneBoson) (u : Carrier) :
    ‖weylUnitary f u-weylUnitary g u‖ ≤
      ‖weylUnitary (f-g) u-u‖+|(⟪f,g⟫_ℂ).im| *‖u‖ := by
  let θ := (⟪f,g⟫_ℂ).im
  let C := Complex.exp (-Complex.I*(θ:ℂ))
  have hm : weylUnitary (-g) (weylUnitary f u) = C • weylUnitary (f-g) u := by
    have hh := congrArg (fun L : Carrier →L[ℂ] Carrier => L u) (weylUnitary_mul (-g) f)
    change weylUnitary (-g) (weylUnitary f u) =
      Complex.exp (-Complex.I*((⟪-g,f⟫_ℂ).im:ℂ)) • weylUnitary (-g+f) u at hh
    have he : -g+f = f-g := by abel
    simpa only [weyl_negative_inner_im,he] using hh
  have hnorm : ‖weylUnitary f u-weylUnitary g u‖ = ‖C • weylUnitary (f-g) u-u‖ := by
    have hh := (weylUnitary g).symm.norm_map (weylUnitary f u-weylUnitary g u)
    rw [map_sub,LinearIsometryEquiv.symm_apply_apply,weylUnitary_symm,hm] at hh
    exact hh.symm
  have harg : -Complex.I*(θ:ℂ) = Complex.I*((-θ:ℝ):ℂ) := by push_cast; ring
  have hC : ‖C‖ = 1 := by dsimp [C]; rw [harg,Complex.norm_exp_I_mul_ofReal]
  have hE : ‖C-1‖ ≤ |θ| := by
    dsimp [C]
    rw [harg]
    simpa only [abs_neg] using weyl_phase_error (-θ)
  rw [hnorm]
  calc
    _ = ‖C • (weylUnitary (f-g) u-u)+(C-1) • u‖ := by congr 1; module
    _ ≤ ‖C • (weylUnitary (f-g) u-u)‖+‖(C-1) • u‖ := norm_add_le _ _
    _ = ‖weylUnitary (f-g) u-u‖+‖C-1‖*‖u‖ := by rw [norm_smul,hC,one_mul,norm_smul]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hE (norm_nonneg u))

lemma weyl_difference_graph (f g : OneBoson) (u : NumberWeightedDomain Sector (1/2) (by norm_num)) :
    ‖weylUnitary f (numberDomainEmbedding (1/2) (by norm_num) u)-
       weylUnitary g (numberDomainEmbedding (1/2) (by norm_num) u)‖ ≤
      2*‖f-g‖*‖u‖+|(⟪f,g⟫_ℂ).im| *‖numberDomainEmbedding (1/2) (by norm_num) u‖ :=
  (weyl_difference_split f g _).trans (add_le_add (weyl_increment_graph (f-g) u) le_rfl)

lemma weyl_difference_negative_graph (f g : OneBoson) (u : NumberWeightedDomain Sector (1/2) (by norm_num)) :
    ‖weylUnitary (-f) (numberDomainEmbedding (1/2) (by norm_num) u)-
       weylUnitary (-g) (numberDomainEmbedding (1/2) (by norm_num) u)‖ ≤
      2*‖f-g‖*‖u‖+|(⟪f,g⟫_ℂ).im| *‖numberDomainEmbedding (1/2) (by norm_num) u‖ := by
  have hr : -f-(-g) = -(f-g) := by abel
  have hn : ‖-f-(-g)‖ = ‖f-g‖ := by rw [hr,norm_neg]
  have hi : (⟪-f,-g⟫_ℂ).im = (⟪f,g⟫_ℂ).im := by rw [inner_neg_left,inner_neg_right,neg_neg]
  simpa only [hn,hi] using weyl_difference_graph (-f) (-g) u

set_option backward.isDefEq.respectTransparency.types false in
lemma weyl_difference_root (f g : OneBoson) (u : (numberPower Sector (1/2)).domain) :
    ‖weylUnitary f u.val-weylUnitary g u.val‖ ≤
      2*‖f-g‖*‖shiftedNumberPower Sector (1/2) (shiftedNumberInput Sector (1/2) (by norm_num) u)‖+
      |(⟪f,g⟫_ℂ).im| *‖u.val‖ := by
  have hh := weyl_difference_graph f g (numberHalfGraphInput u)
  rw [numberHalfGraphInput_embedding] at hh
  exact hh

set_option backward.isDefEq.respectTransparency.types false in
lemma weyl_difference_negative_root (f g : OneBoson) (u : (numberPower Sector (1/2)).domain) :
    ‖weylUnitary (-f) u.val-weylUnitary (-g) u.val‖ ≤
      2*‖f-g‖*‖shiftedNumberPower Sector (1/2) (shiftedNumberInput Sector (1/2) (by norm_num) u)‖+
      |(⟪f,g⟫_ℂ).im| *‖u.val‖ := by
  have hh := weyl_difference_negative_graph f g (numberHalfGraphInput u)
  rw [numberHalfGraphInput_embedding] at hh
  exact hh

def numberHalfInverse : Carrier →L[ℂ] Carrier :=
  (numberDomainEmbedding (1/2) (by norm_num)).comp
    (numberReciprocalIsometry Sector (1/2) (by norm_num)).toLinearIsometry.toContinuousLinearMap

set_option backward.isDefEq.respectTransparency.types false in
lemma numberHalfInverse_apply (u : Carrier) (n : ℕ) :
    numberHalfInverse u n = ((((n:ℝ)+1)^(-(1/2:ℝ)):ℝ):ℂ) • u n := by
  have he : numberHalfInverse u = (numberWeightedGraph Sector (1/2) (by norm_num)).embedding
      (numberGraphCopy Sector (1/2) u) := by
    change numberDomainEmbedding (1/2) (by norm_num) (numberReciprocalIsometry Sector (1/2) (by norm_num) u) = _
    exact (numberDomainEmbedding_apply (1/2) (by norm_num) _).trans
      (numberReciprocalIsometry_ambient Sector (1/2) (by norm_num) u)
  calc
    _ = (numberWeightedGraph Sector (1/2) (by norm_num)).embedding (numberGraphCopy Sector (1/2) u) n :=
      congrArg (fun v : Carrier => v n) he
    _ = _ := by
      convert! numberGraphEmbedding_apply Sector (1/2) (by norm_num) (numberGraphCopy Sector (1/2) u) n using 1 <;> rfl

lemma numberHalfNegative_domain : (shiftedNumberPower Sector (-(1/2:ℝ))).domain = ⊤ := by
  ext u
  constructor
  · intro _
    trivial
  · intro _
    change Memℓp (fun (n : ℕ) => (((((n:ℝ)+1)^(-(1/2:ℝ))):ℝ):ℂ) • u n) 2
    have he : (fun (n : ℕ) => (((((n:ℝ)+1)^(-(1/2:ℝ))):ℝ):ℂ) • u n) = fun n => numberHalfInverse u n :=
      funext (fun n => (numberHalfInverse_apply u n).symm)
    rw [he]
    exact (numberHalfInverse u).property

def numberHalfNegativeInput (u : Carrier) : (shiftedNumberPower Sector (-(1/2:ℝ))).domain :=
  ⟨u,by rw [numberHalfNegative_domain]; trivial⟩

lemma numberHalfInverse_power (u : Carrier) :
    shiftedNumberPower Sector (-(1/2:ℝ)) (numberHalfNegativeInput u) = numberHalfInverse u := by
  apply lp.ext
  funext n
  rw [numberHalfInverse_apply]
  rfl

lemma numberHalfInverse_norm (u : Carrier) : ‖numberHalfInverse u‖ ≤ ‖u‖ := by
  change ‖numberDomainEmbedding (1/2) (by norm_num) (numberReciprocalIsometry Sector (1/2) (by norm_num) u)‖ ≤ _
  exact (numberDomainEmbedding_norm (1/2) (by norm_num) _).trans_eq
    ((numberReciprocalIsometry Sector (1/2) (by norm_num)).norm_map u)

set_option backward.isDefEq.respectTransparency.types false in
lemma weyl_difference_halfInverse_norm (f g : OneBoson) :
    ‖((weylUnitary f : Carrier →L[ℂ] Carrier)-(weylUnitary g : Carrier →L[ℂ] Carrier)).comp numberHalfInverse‖ ≤
      2*‖f-g‖+|(⟪f,g⟫_ℂ).im| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  change ‖weylUnitary f (numberHalfInverse u)-weylUnitary g (numberHalfInverse u)‖ ≤ _
  have hh := weyl_difference_graph f g (numberReciprocalIsometry Sector (1/2) (by norm_num) u)
  change ‖weylUnitary f (numberHalfInverse u)-weylUnitary g (numberHalfInverse u)‖ ≤
    2*‖f-g‖*‖numberReciprocalIsometry Sector (1/2) (by norm_num) u‖+
    |(⟪f,g⟫_ℂ).im| *‖numberHalfInverse u‖ at hh
  rw [(numberReciprocalIsometry Sector (1/2) (by norm_num)).norm_map] at hh
  calc
    _ ≤ 2*‖f-g‖*‖u‖+|(⟪f,g⟫_ℂ).im| *‖numberHalfInverse u‖ := hh
    _ ≤ 2*‖f-g‖*‖u‖+|(⟪f,g⟫_ℂ).im| *‖u‖ :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (numberHalfInverse_norm u) (abs_nonneg _))
    _ = _ := by ring

end GW.Fock
