module
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace GW.Analysis

def laplaceEnvelope (c : ℝ) (n : ℕ) : ℝ := Real.exp (-(n:ℝ)) * (1+c*((n:ℝ)+1))

def laplaceScalar (c t : ℝ) : ℝ := Real.exp (-t)*(1+c*t)

lemma laplaceEnvelope_pos (c : ℝ) (hc : 0 ≤ c) (n : ℕ) :
    0 < laplaceEnvelope c n :=
  mul_pos (Real.exp_pos _) (by positivity)

lemma laplaceEnvelope_ratio (c : ℝ) (hc : 0 ≤ c) (n : ℕ) :
    ‖laplaceEnvelope c (n+1)‖ / ‖laplaceEnvelope c n‖ =
      Real.exp (-1) * (1+c/(1+c*((n:ℝ)+1))) := by
  rw [Real.norm_of_nonneg (laplaceEnvelope_pos c hc _).le,Real.norm_of_nonneg (laplaceEnvelope_pos c hc _).le]
  unfold laplaceEnvelope
  push_cast
  have he : Real.exp (-((n:ℝ)+1)) = Real.exp (-(n:ℝ))*Real.exp (-1) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  field_simp [ne_of_gt (Real.exp_pos (-(n:ℝ))),
    show (1+c*((n:ℝ)+1)) ≠ 0 from ne_of_gt (by positivity)]
  <;> ring

lemma laplaceEnvelope_summable (c : ℝ) (hc : 0 ≤ c) : Summable (laplaceEnvelope c) := by
  apply summable_of_ratio_test_tendsto_lt_one (l := Real.exp (-1)) (by rw [Real.exp_lt_one_iff]; norm_num)
    (Eventually.of_forall (fun n => (laplaceEnvelope_pos c hc n).ne'))
  simp_rw [laplaceEnvelope_ratio c hc]
  by_cases h : c = 0
  · subst c
    simpa only [zero_div,add_zero,mul_one] using (tendsto_const_nhds (x := Real.exp (-1)))
  have hp : 0 < c := lt_of_le_of_ne hc (Ne.symm h)
  have hn : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hm : Tendsto (fun n : ℕ => c*((n:ℝ)+1)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hp hn
  have hden : Tendsto (fun n : ℕ => 1+c*((n:ℝ)+1)) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 hm
  have hq := (tendsto_inv_atTop_zero.comp hden).const_mul c
  have hlimit := (hq.const_add 1).const_mul (Real.exp (-1))
  simpa only [div_eq_mul_inv,Function.comp_def,mul_zero,add_zero,mul_one] using hlimit

lemma laplaceScalar_le_envelope (c : ℝ) (hc : 0 ≤ c) (n : ℕ) (t : ℝ)
    (hn : (n:ℝ) ≤ t) (ht : t < (n:ℝ)+1) :
    laplaceScalar c t ≤ laplaceEnvelope c n := by
  unfold laplaceScalar laplaceEnvelope
  apply mul_le_mul (Real.exp_le_exp.mpr (neg_le_neg hn)) _ _ (Real.exp_nonneg _)
  · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left ht.le hc)
  · exact add_nonneg zero_le_one (mul_nonneg hc ((Nat.cast_nonneg n).trans hn))

def laplaceUnitPiece (c : ℝ) (n : ℕ) : ℝ → ℝ≥0∞ :=
  (Ico (n:ℝ) ((n:ℝ)+1)).indicator (fun _ => ENNReal.ofReal (laplaceEnvelope c n))

lemma laplaceUnitPiece_measurable (c : ℝ) (n : ℕ) : Measurable (laplaceUnitPiece c n) :=
  measurable_const.indicator measurableSet_Ico

lemma laplaceUnitPiece_lintegral (c : ℝ) (n : ℕ) :
    (∫⁻ t, laplaceUnitPiece c n t ∂(volume : Measure ℝ)) = ENNReal.ofReal (laplaceEnvelope c n) := by
  unfold laplaceUnitPiece
  rw [lintegral_indicator measurableSet_Ico,lintegral_const,Measure.restrict_apply_univ,Real.volume_Ico]
  simp

lemma laplaceScalar_integrable (c : ℝ) (hc : 0 ≤ c) :
    IntegrableOn (laplaceScalar c) (Ici (0:ℝ)) volume := by
  have hcont : Continuous (laplaceScalar c) := by unfold laplaceScalar; fun_prop
  refine ⟨hcont.aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_norm,← lintegral_indicator measurableSet_Ici]
  have hb (t : ℝ) :
      (Ici (0:ℝ)).indicator (fun t => ENNReal.ofReal ‖laplaceScalar c t‖) t ≤
        ∑' n, laplaceUnitPiece c n t := by
    by_cases ht : 0 ≤ t
    · let n : ℕ := ⌊t⌋₊
      have hn : (n:ℝ) ≤ t := Nat.floor_le ht
      have hnt : t < (n:ℝ)+1 := Nat.lt_floor_add_one t
      have hp : 0 ≤ laplaceScalar c t := by unfold laplaceScalar; positivity
      rw [indicator_of_mem ht,Real.norm_of_nonneg hp]
      calc
        _ ≤ ENNReal.ofReal (laplaceEnvelope c n) := ENNReal.ofReal_le_ofReal (laplaceScalar_le_envelope c hc n t hn hnt)
        _ = laplaceUnitPiece c n t := by
          unfold laplaceUnitPiece
          exact (indicator_of_mem (show t ∈ Ico (n:ℝ) ((n:ℝ)+1) from ⟨hn,hnt⟩) (fun _ : ℝ => ENNReal.ofReal (laplaceEnvelope c n))).symm
        _ ≤ _ := le_tsum (fun j => laplaceUnitPiece c j t) n
    · rw [indicator_of_notMem ht]
      exact zero_le
  apply (lintegral_mono hb).trans_lt
  rw [lintegral_tsum (fun n => (laplaceUnitPiece_measurable c n).aemeasurable)]
  simp_rw [laplaceUnitPiece_lintegral]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => (laplaceEnvelope_pos c hc n).le) (laplaceEnvelope_summable c hc)]
  exact ENNReal.ofReal_lt_top

lemma laplaceScalar_tail_le (c : ℝ) (hc : 0 ≤ c) (T : ℝ) (N : ℕ) (hN : (N:ℝ) ≤ T) :
    (∫ t in Ici T, laplaceScalar c t ∂(volume : Measure ℝ)) ≤ ∑' n, laplaceEnvelope c (n+N) := by
  have hT : 0 ≤ T := (Nat.cast_nonneg N).trans hN
  have hi := (laplaceScalar_integrable c hc).mono_set (Ici_subset_Ici.mpr hT)
  have hs : Summable (fun n => laplaceEnvelope c (n+N)) :=
    (summable_nat_add_iff N).mpr (laplaceEnvelope_summable c hc)
  have hp : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Ici T), 0 ≤ laplaceScalar c t := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    have ht0 : 0 ≤ t := hT.trans ht
    unfold laplaceScalar
    positivity
  have hb (t : ℝ) :
      (Ici T).indicator (fun t => ENNReal.ofReal (laplaceScalar c t)) t ≤
        ∑' j, laplaceUnitPiece c (j+N) t := by
    by_cases ht : t ∈ Ici T
    · have ht0 : 0 ≤ t := hT.trans ht
      let n : ℕ := ⌊t⌋₊
      have h₀ : N ≤ n := (Nat.le_floor_iff ht0).mpr (hN.trans ht)
      have hn : (n:ℝ) ≤ t := Nat.floor_le ht0
      have hnt : t < (n:ℝ)+1 := Nat.lt_floor_add_one t
      rw [indicator_of_mem ht]
      calc
        _ ≤ ENNReal.ofReal (laplaceEnvelope c n) := ENNReal.ofReal_le_ofReal (laplaceScalar_le_envelope c hc n t hn hnt)
        _ = laplaceUnitPiece c n t := by
          unfold laplaceUnitPiece
          exact (indicator_of_mem (show t ∈ Ico (n:ℝ) ((n:ℝ)+1) from ⟨hn,hnt⟩)
            (fun _ : ℝ => ENNReal.ofReal (laplaceEnvelope c n))).symm
        _ = laplaceUnitPiece c ((n-N)+N) t := by rw [Nat.sub_add_cancel h₀]
        _ ≤ _ := le_tsum (fun j => laplaceUnitPiece c (j+N) t) (n-N)
    · rw [indicator_of_notMem ht]
      exact zero_le
  have he := lintegral_mono hb (μ := (volume : Measure ℝ))
  rw [lintegral_indicator measurableSet_Ici,← ofReal_integral_eq_lintegral_ofReal hi hp,
    lintegral_tsum (fun n => (laplaceUnitPiece_measurable c (n+N)).aemeasurable)] at he
  simp_rw [laplaceUnitPiece_lintegral] at he
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => (laplaceEnvelope_pos c hc (n+N)).le) hs] at he
  exact (ENNReal.ofReal_le_ofReal_iff (tsum_nonneg (fun n => (laplaceEnvelope_pos c hc (n+N)).le))).mp he

lemma laplaceScalar_tail (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun T : ℝ => ∫ t in Ici T, laplaceScalar c t ∂(volume : Measure ℝ)) atTop (𝓝 0) := by
  have hs := _root_.tendsto_sum_nat_add (laplaceEnvelope c)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := (Metric.tendsto_nhds.mp hs ε hε).exists
  filter_upwards [eventually_ge_atTop (N:ℝ)] with T hT
  have hnn : 0 ≤ ∫ t in Ici T, laplaceScalar c t ∂(volume : Measure ℝ) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    have ht0 : 0 ≤ t := (Nat.cast_nonneg N).trans (hT.trans ht)
    unfold laplaceScalar
    positivity
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hnn]
  exact (laplaceScalar_tail_le c hc T N hT).trans_lt
    (by rw [Real.dist_eq,sub_zero,abs_of_nonneg (tsum_nonneg (fun n => (laplaceEnvelope_pos c hc (n+N)).le))] at hN; exact hN)

section GraphOrbit
variable {X H : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

def laplaceGraphIntegrand (v : ℝ → X) (t : ℝ) : X := Real.exp (-t) • v t

def laplaceGraphIntegral (v : ℝ → X) : X := ∫ t in Ici (0:ℝ), laplaceGraphIntegrand v t

lemma laplaceGraphIntegrand_integrable (v : ℝ → X) (hv : Continuous v) (u : X)
    (c : ℝ) (hc : 0 ≤ c) (hb : ∀ t : ℝ, 0 ≤ t → ‖v t‖ ≤ (1+c*t)*‖u‖) :
    IntegrableOn (laplaceGraphIntegrand v) (Ici (0:ℝ)) volume := by
  have hi := (laplaceScalar_integrable c hc).mul_const ‖u‖
  apply Integrable.mono' hi
  · have hcont : Continuous (laplaceGraphIntegrand v) := by
      unfold laplaceGraphIntegrand
      exact (Real.continuous_exp.comp continuous_neg).smul hv
    exact hcont.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    have ht' : 0 ≤ t := ht
    change ‖Real.exp (-t) • v t‖ ≤ laplaceScalar c t * ‖u‖
    rw [norm_smul,Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (hb t ht') (Real.exp_nonneg _)).trans_eq (by unfold laplaceScalar; ring)

lemma laplaceBoundary_zero (w : ℝ → H) (a : ℝ) (hw : ∀ t, ‖w t‖ = a) :
    Tendsto (laplaceGraphIntegrand w) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h : Tendsto (fun t : ℝ => Real.exp (-t) * a) atTop (𝓝 0) := by
    simpa only [Function.comp_def,zero_mul] using
      (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).mul_const a
  apply h.congr'
  exact Eventually.of_forall (fun t => by
    change Real.exp (-t)*a = ‖Real.exp (-t) • w t‖
    rw [norm_smul,Real.norm_of_nonneg (Real.exp_nonneg _),hw])

lemma laplaceWeightedOrbit_hasDerivAt (J A : X →L[ℂ] H) (s : ℂ) (v : ℝ → X)
    (hv' : ∀ t, HasDerivAt (fun τ => J (v τ)) (s • A (v t)) t) (t : ℝ) :
    HasDerivAt (fun τ => J (laplaceGraphIntegrand v τ))
      (-((J-s • A) (laplaceGraphIntegrand v t))) t := by
  have hExp : HasDerivAt (fun τ : ℝ => Real.exp (-τ)) (-Real.exp (-t)) t := by
    simpa only [Function.comp_def,smul_eq_mul,neg_one_mul,mul_neg,mul_one] using
      (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_id t).neg
  have h := hExp.smul (hv' t)
  have heq : (fun τ : ℝ => Real.exp (-τ) • J (v τ)) = fun τ => J (laplaceGraphIntegrand v τ) := by
    funext τ
    change Real.exp (-τ) • J (v τ) = J (Real.exp (-τ) • v τ)
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),map_smul]
  have he : Real.exp (-t) • (s • A (v t)) + (-Real.exp (-t)) • J (v t) =
      -((J-s • A) (laplaceGraphIntegrand v t)) := by
    change _ = -(J (Real.exp (-t) • v t)-s • A (Real.exp (-t) • v t))
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),map_smul]
    let a := Real.exp (-t)
    change Complex.ofReal a • (s • A (v t)) + Complex.ofReal (-a) • J (v t) =
      -(Complex.ofReal a • J (v t)-s • (Complex.ofReal a • A (v t)))
    rw [Complex.ofReal_neg,neg_smul,neg_sub,sub_eq_add_neg,smul_comm (Complex.ofReal a) s]

  change HasDerivAt (fun τ => Real.exp (-τ) • J (v τ)) _ t at h
  rw [heq,he] at h
  exact h

lemma laplaceGraphIdentity (J A : X →L[ℂ] H) (s : ℂ) (v : ℝ → X) (u : X)
    (c : ℝ) (hc : 0 ≤ c) (hv : Continuous v)
    (hb : ∀ t : ℝ, 0 ≤ t → ‖v t‖ ≤ (1+c*t)*‖u‖)
    (hn : ∀ t, ‖J (v t)‖ = ‖J u‖) (hzero : J (v 0) = J u)
    (hv' : ∀ t, HasDerivAt (fun τ => J (v τ)) (s • A (v t)) t) :
    (J-s • A) (laplaceGraphIntegral v) = J u := by
  let F := laplaceGraphIntegrand v
  let L : X →L[ℂ] H := J-s • A
  let d : ℝ → H := fun t => (-L) (F t)
  have hi : IntegrableOn F (Ici (0:ℝ)) volume := laplaceGraphIntegrand_integrable v hv u c hc hb
  have hd : IntegrableOn d (Ici (0:ℝ)) volume := (-L).integrable_comp hi
  have hcont : Continuous d := by
    have hF : Continuous F := (Real.continuous_exp.comp continuous_neg).smul hv
    exact (-L).continuous.comp hF
  have hder (t : ℝ) : HasDerivAt (fun τ => J (F τ)) (d t) t :=
    laplaceWeightedOrbit_hasDerivAt J A s v hv' t
  have hFTC (T : ℝ) :
      (∫ t in 0..T, d t ∂(volume : Measure ℝ)) = J (F T) - J (F 0) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hder t)
      (hcont.intervalIntegrable 0 T)
  have hlimA := intervalIntegral_tendsto_integral_Ioi (μ := (volume : Measure ℝ)) 0
    (hd.mono_set Ioi_subset_Ici_self) (tendsto_id : Tendsto (fun T : ℝ => T) atTop atTop)
  have hlimB : Tendsto (fun T : ℝ => J (F T)) atTop (𝓝 0) := by
    have h := laplaceBoundary_zero (fun t => J (v t)) ‖J u‖ hn
    exact h.congr' (Eventually.of_forall (fun T => by
      change Real.exp (-T) • J (v T) = J (Real.exp (-T) • v T)
      simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),map_smul]))
  have hlimB' := (hlimB.sub_const (J (F 0))).congr' (Eventually.of_forall (fun T => (hFTC T).symm))
  have hlim : (∫ t in Ioi (0:ℝ), d t ∂(volume : Measure ℝ)) = 0 - J (F 0) :=
    tendsto_nhds_unique hlimA hlimB'
  have he : (∫ t in Ioi (0:ℝ), d t ∂(volume : Measure ℝ)) =
      ∫ t in Ici (0:ℝ), d t ∂(volume : Measure ℝ) := by rw [integral_Ici_eq_integral_Ioi]
  rw [he] at hlim
  change (∫ t in Ici (0:ℝ), (-L) (F t) ∂(volume : Measure ℝ)) = _ at hlim
  rw [(-L).integral_comp_comm hi] at hlim
  change -L (laplaceGraphIntegral v) = 0 - J (F 0) at hlim
  have h0 : J (F 0) = J u := by simpa [F,laplaceGraphIntegrand] using hzero
  rw [h0,zero_sub] at hlim
  exact neg_injective hlim

lemma laplaceGraph_resolvent_pair (J A : X →L[ℂ] H)
    (V : ℝ → H →ₗᵢ[ℂ] H) (v : ℝ → X) (u : X)
    (c : ℝ) (hc : 0 ≤ c) (hv : Continuous v)
    (hV : ∀ t, J (v t) = V t (J u)) (hV0 : ∀ w, V 0 w = w)
    (hplus : ∀ t : ℝ, 0 ≤ t → ‖v t‖ ≤ (1+c*t)*‖u‖)
    (hminus : ∀ t : ℝ, 0 ≤ t → ‖v (-t)‖ ≤ (1+c*t)*‖u‖)
    (hd : ∀ t, HasDerivAt (fun τ => J (v τ)) (Complex.I • A (v t)) t) :
    (J-Complex.I • A) (laplaceGraphIntegral v) = J u ∧
    (J+Complex.I • A) (laplaceGraphIntegral (fun t => v (-t))) = J u := by
  have hn (t : ℝ) : ‖J (v t)‖ = ‖J u‖ := by rw [hV]; exact (V t).norm_map _
  have h0 : J (v 0) = J u := (hV 0).trans (hV0 _)
  refine ⟨laplaceGraphIdentity J A Complex.I v u c hc hv hplus hn h0 hd,?_⟩
  have hdneg (t : ℝ) : HasDerivAt (fun τ => J (v (-τ))) ((-Complex.I) • A (v (-t))) t := by
    have he := (hd (-t)).scomp t (hasDerivAt_id t).neg
    simpa only [Function.comp_def,id_eq,neg_smul,one_smul] using he
  have h := laplaceGraphIdentity J A (-Complex.I) (fun t => v (-t)) u c hc
    (hv.comp continuous_neg) hminus (fun t => hn (-t)) (by simpa only [neg_zero] using h0) hdneg
  simpa only [neg_smul,sub_neg_eq_add] using h

end GraphOrbit
end GW.Analysis
