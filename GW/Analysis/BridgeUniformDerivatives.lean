module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.UniformSpace.UniformApproximation
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology Interval
namespace GW.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

lemma realComponent_uIcc {J : Set ℝ} {t₀ a b : ℝ}
    (ha : a ∈ connectedComponentIn J t₀) (hb : b ∈ connectedComponentIn J t₀) :
    [[a,b]] ⊆ connectedComponentIn J t₀ := by
  have ho := (isPreconnected_connectedComponentIn (F := J) (x := t₀)).ordConnected
  exact ho.out (min_rec' (fun x => x ∈ connectedComponentIn J t₀) ha hb)
    (max_rec' (fun x => x ∈ connectedComponentIn J t₀) ha hb)

lemma locallyUniformDerivative_continuous {J : Set ℝ} (hJ : IsOpen J)
    (t₀ : ℝ) (dN : ℕ → ℝ → F) (d : ℝ → F)
    (hdN : ∀ n, ContinuousOn (dN n) J)
    (hlim : ∀ a b : ℝ, [[a,b]] ⊆ connectedComponentIn J t₀ →
      TendstoUniformlyOn dN d atTop [[a,b]]) :
    ContinuousOn d (connectedComponentIn J t₀) := by
  intro t ht
  have hC : IsOpen (connectedComponentIn J t₀) := hJ.connectedComponentIn
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hC t ht
  have hI : [[t-r/2,t+r/2]] ⊆ connectedComponentIn J t₀ := by
    intro x hx
    apply hball
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    rw [uIcc_of_le (by linarith)] at hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have h := (hlim _ _ hI).continuousOn
    (Eventually.of_forall (fun n => (hdN n).mono (hI.trans (connectedComponentIn_subset J t₀)))).frequently
  have hn : [[t-r/2,t+r/2]] ∈ 𝓝 t := by
    rw [uIcc_of_le (by linarith)]
    exact Icc_mem_nhds (by linarith) (by linarith)
  exact ((h t (mem_of_mem_nhds hn)).continuousAt hn).continuousWithinAt

def integratedDerivative (t₀ : ℝ) (c₀ : F) (d : ℝ → F) (t : ℝ) : F :=
  c₀ + ∫ x in t₀..t, d x

lemma integratedDerivative_base (t₀ : ℝ) (c₀ : F) (d : ℝ → F) :
    integratedDerivative t₀ c₀ d t₀ = c₀ := by simp [integratedDerivative]

lemma integratedDerivative_increment {C : Set ℝ} {t₀ s t : ℝ} {d : ℝ → F} (c₀ : F)
    (hd : ContinuousOn d C) (hs : [[t₀,s]] ⊆ C) (ht : [[s,t]] ⊆ C) :
    integratedDerivative t₀ c₀ d t - integratedDerivative t₀ c₀ d s = ∫ x in s..t, d x := by
  have hs' : IntervalIntegrable d volume t₀ s := (hd.mono hs).intervalIntegrable
  have ht' : IntervalIntegrable d volume s t := (hd.mono ht).intervalIntegrable
  have h := intervalIntegral.integral_add_adjacent_intervals hs' ht' 
  simp only [integratedDerivative,← h]
  abel

lemma uniformDerivative_integral_error {C : Set ℝ} {t₀ t : ℝ}
    {cN dN d : ℝ → F} {c₀ : F} {δ : ℝ}
    (hI : [[t₀,t]] ⊆ C)
    (hdN : ContinuousOn dN C) (hd : ContinuousOn d C)
    (hder : ∀ x ∈ C, HasDerivAt cN (dN x) x)
    (hb : ∀ x ∈ [[t₀,t]], ‖dN x - d x‖ ≤ δ) :
    ‖cN t - integratedDerivative t₀ c₀ d t‖ ≤ ‖cN t₀ - c₀‖ + δ * |t-t₀| := by
  have h₁ : IntervalIntegrable dN volume t₀ t := (hdN.mono hI).intervalIntegrable
  have h₂ : IntervalIntegrable d volume t₀ t := (hd.mono hI).intervalIntegrable
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hder x (hI hx)) h₁
  have he : cN t - integratedDerivative t₀ c₀ d t =
      (cN t₀ - c₀) + ∫ x in t₀..t, (dN x - d x) := by
    rw [integratedDerivative,intervalIntegral.integral_sub h₁ h₂,hf]
    abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add_right
    (intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => hb x (uIoc_subset_uIcc hx))) _)

lemma integratedDerivative_hasDerivAt {C : Set ℝ} (hC : IsOpen C)
    {t₀ t : ℝ} {c₀ : F} {d : ℝ → F}
    (hseg : ∀ a ∈ C, ∀ b ∈ C, [[a,b]] ⊆ C) (h₀ : t₀ ∈ C) (ht : t ∈ C)
    (hd : ContinuousOn d C) :
    HasDerivAt (integratedDerivative t₀ c₀ d) (d t) t := by
  rw [hasDerivAt_iff_tendsto_slope,Metric.tendsto_nhds]
  intro ε hε
  have hc : ContinuousAt d t := (hd t ht).continuousAt (hC.mem_nhds ht)
  obtain ⟨r,hr,hrd⟩ := Metric.continuousAt_iff.mp hc (ε/2) (by positivity)
  have hball : Metric.ball t r ∈ 𝓝 t := Metric.ball_mem_nhds t hr
  filter_upwards [mem_nhdsWithin_of_mem_nhds hball,
    mem_nhdsWithin_of_mem_nhds (hC.mem_nhds ht), self_mem_nhdsWithin] with y hy hyC hyne
  have hy' : |y-t| < r := by simpa only [Metric.mem_ball,Real.dist_eq] using hy
  have hn : y - t ≠ 0 := sub_ne_zero.mpr hyne
  have hs := hseg t ht y hyC
  have hi : IntervalIntegrable d volume t y := (hd.mono hs).intervalIntegrable
  have hb (x : ℝ) (hx : x ∈ [[t,y]]) : ‖d x - d t‖ ≤ ε/2 := by
    apply le_of_lt
    rw [← dist_eq_norm]
    apply hrd
    rw [Real.dist_eq,abs_lt]
    rw [uIcc,mem_Icc] at hx
    have hn' := abs_lt.mp hy'
    have hl : t-r < min t y := lt_min (by linarith) (by linarith [hn'.1])
    have hu : max t y < t+r := max_lt (by linarith) (by linarith [hn'.2])
    exact ⟨by linarith [hl.trans_le hx.1],by linarith [hx.2.trans_lt hu]⟩
  have hconst : IntervalIntegrable (fun _ : ℝ => d t) volume t y := intervalIntegrable_const
  have he : slope (integratedDerivative t₀ c₀ d) t y - d t =
      (y-t)⁻¹ • ∫ x in t..y, (d x - d t) := by
    rw [slope,vsub_eq_sub,integratedDerivative_increment c₀ hd (hseg t₀ h₀ t ht) hs,
      intervalIntegral.integral_sub hi hconst,intervalIntegral.integral_const,smul_sub,smul_smul,
      inv_mul_cancel₀ hn,one_smul]
  rw [dist_eq_norm,he,norm_smul,Real.norm_eq_abs,abs_inv]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun x hx => hb x (uIoc_subset_uIcc hx))
  calc
    _ ≤ |y-t|⁻¹ * ((ε/2) * |y-t|) :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr (abs_nonneg _))
    _ = ε/2 := by field_simp [abs_ne_zero.mpr hn]
    _ < ε := by linarith

lemma uniformDerivativeLimit_on_interval {J : Set ℝ} (hJ : IsOpen J) {t₀ : ℝ} (h₀ : t₀ ∈ J)
    {cN dN : ℕ → ℝ → F} {d : ℝ → F} {c₀ : F}
    (hder : ∀ n t, t ∈ J → HasDerivAt (cN n) (dN n t) t)
    (hdN : ∀ n, ContinuousOn (dN n) J)
    (hc₀ : Tendsto (fun n => cN n t₀) atTop (𝓝 c₀))
    (hlim : ∀ a b : ℝ, [[a,b]] ⊆ connectedComponentIn J t₀ →
      TendstoUniformlyOn dN d atTop [[a,b]])
    (a b : ℝ) (hab : [[a,b]] ⊆ connectedComponentIn J t₀) :
    TendstoUniformlyOn cN (integratedDerivative t₀ c₀ d) atTop [[a,b]] := by
  let C := connectedComponentIn J t₀
  have ht₀ : t₀ ∈ C := mem_connectedComponentIn h₀
  have ha : a ∈ C := hab left_mem_uIcc
  have hb : b ∈ C := hab right_mem_uIcc
  let A := min t₀ (min a b)
  let B := max t₀ (max a b)
  have hA : A ∈ C := min_rec' (fun x => x ∈ C) ht₀ (min_rec' (fun x => x ∈ C) ha hb)
  have hB : B ∈ C := max_rec' (fun x => x ∈ C) ht₀ (max_rec' (fun x => x ∈ C) ha hb)
  have hAB : A ≤ B := (min_le_left _ _).trans (le_max_left _ _)
  have hI : [[A,B]] ⊆ C := realComponent_uIcc hA hB
  have hd := locallyUniformDerivative_continuous hJ t₀ dN d hdN hlim
  refine Metric.tendstoUniformlyOn_iff.mpr (fun ε hε => ?_)
  let δ := ε/(2*(B-A+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  filter_upwards [(Metric.tendsto_nhds.mp hc₀) (ε/2) (by positivity),
    (Metric.tendstoUniformlyOn_iff.mp (hlim A B hI)) δ hδ] with n h₁ h₂ t ht
  have htAB : t ∈ Icc A B := by
    rw [uIcc,mem_Icc] at ht
    exact ⟨(min_le_right _ _).trans ht.1,ht.2.trans (le_max_right _ _)⟩
  have ht₀AB : t₀ ∈ Icc A B := ⟨min_le_left _ _,le_max_left _ _⟩
  have hsub : [[t₀,t]] ⊆ [[A,B]] := by
    rw [uIcc_of_le hAB,uIcc]
    exact Icc_subset_Icc (le_min ht₀AB.1 htAB.1) (max_le ht₀AB.2 htAB.2)
  have herror := uniformDerivative_integral_error (c₀ := c₀) (δ := δ) (hsub.trans hI)
    ((hdN n).mono (connectedComponentIn_subset J t₀)) hd
    (fun x hx => hder n x (connectedComponentIn_subset J t₀ hx))
    (fun x hx => le_of_lt (by
      rw [← dist_eq_norm,dist_comm]
      exact h₂ x (hsub hx)))
  have hlength : |t-t₀| ≤ B-A := by
    rw [abs_le]
    exact ⟨by linarith [htAB.1,ht₀AB.2],by linarith [htAB.2,ht₀AB.1]⟩
  have hδB : δ * (B-A) ≤ ε/2 := by
    have he : δ * (B-A+1) = ε/2 := by
      dsimp [δ]
      field_simp [show B-A+1 ≠ 0 by linarith]
    nlinarith
  have hbase : ‖cN n t₀ - c₀‖ < ε/2 := by simpa only [dist_eq_norm] using h₁
  have hfinal : ‖cN n t - integratedDerivative t₀ c₀ d t‖ < ε := by
    have hp := (mul_le_mul_of_nonneg_left hlength hδ.le).trans hδB
    linarith
  rw [dist_comm,dist_eq_norm]
  exact hfinal

lemma uniformDerivativeLimit {J : Set ℝ} (hJ : IsOpen J) {t₀ : ℝ} (h₀ : t₀ ∈ J)
    {cN dN : ℕ → ℝ → F} {d : ℝ → F} {c₀ : F}
    (hder : ∀ n t, t ∈ J → HasDerivAt (cN n) (dN n t) t)
    (hdN : ∀ n, ContinuousOn (dN n) J)
    (hc₀ : Tendsto (fun n => cN n t₀) atTop (𝓝 c₀))
    (hlim : ∀ a b : ℝ, [[a,b]] ⊆ connectedComponentIn J t₀ →
      TendstoUniformlyOn dN d atTop [[a,b]]) :
    let C := connectedComponentIn J t₀
    let c := integratedDerivative t₀ c₀ d
    c t₀ = c₀ ∧
    (∀ s ∈ C, ∀ t ∈ C, c t - c s = ∫ x in s..t, d x) ∧
    (∀ t ∈ C, HasDerivAt c (d t) t) ∧
    (∀ a b : ℝ, [[a,b]] ⊆ C → TendstoUniformlyOn cN c atTop [[a,b]]) ∧
    (∀ q : ℝ → F, q t₀ = c₀ →
      (∀ s ∈ C, ∀ t ∈ C, q t - q s = ∫ x in s..t, d x) → EqOn q c C) ∧
    (∀ q : ℝ → F, (∀ t ∈ C, Tendsto (fun n => cN n t) atTop (𝓝 (q t))) → EqOn q c C) := by
  dsimp only
  let C := connectedComponentIn J t₀
  have hbase : t₀ ∈ C := mem_connectedComponentIn h₀
  have hd := locallyUniformDerivative_continuous hJ t₀ dN d hdN hlim
  have hseg (s : ℝ) (hs : s ∈ C) (t : ℝ) (ht : t ∈ C) : [[s,t]] ⊆ C :=
    realComponent_uIcc hs ht
  have hu := uniformDerivativeLimit_on_interval hJ h₀ hder hdN hc₀ hlim
  refine ⟨integratedDerivative_base t₀ c₀ d,?_,?_,hu,?_,?_⟩
  · intro s hs t ht
    exact integratedDerivative_increment c₀ hd (hseg _ hbase _ hs) (hseg _ hs _ ht)
  · intro t ht
    exact integratedDerivative_hasDerivAt hJ.connectedComponentIn hseg hbase ht hd
  · intro q hq₀ hq t ht
    have h := hq t₀ hbase t ht
    rw [hq₀] at h
    exact sub_eq_iff_eq_add.mp h |>.trans (add_comm _ _)
  · intro q hq t ht
    exact tendsto_nhds_unique (hq t ht) ((hu t t (hseg _ ht _ ht)).tendsto_at left_mem_uIcc)

end GW.Analysis
