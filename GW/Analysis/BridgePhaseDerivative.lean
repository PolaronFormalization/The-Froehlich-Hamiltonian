module
public import GW.Analysis.Fourier
public import GW.Analysis.L2Domination
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ENNReal Interval
namespace GW.Analysis

def phaseAt (f : GW.OnePhonon) (x : GW.Space) : GW.OnePhonon :=
  boundedMultiplier (fun k => physicalPhase k x) (by
    unfold physicalPhase
    fun_prop) (C := 1) (Eventually.of_forall (fun k => (physicalPhase_norm k x).le)) f

lemma phaseAt_ae (f : GW.OnePhonon) (x : GW.Space) :
    phaseAt f x =ᵐ[(volume : Measure GW.Space)] fun k => physicalPhase k x * f k :=
  (boundedMultiplier_ae _ _ _ f).symm

lemma phaseAt_norm (f : GW.OnePhonon) (x : GW.Space) : ‖phaseAt f x‖ = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [l2_norm_sq (𝕜 := ℂ),l2_norm_sq (𝕜 := ℂ)]
  apply integral_congr_ae
  filter_upwards [phaseAt_ae f x] with k hk
  rw [hk,norm_mul,physicalPhase_norm,one_mul]

lemma phaseAt_continuous (f : GW.OnePhonon) : Continuous (phaseAt f) := by
  apply continuous_iff_seqContinuous.mpr
  intro xN x hx
  let rep (x : GW.Space) (k : GW.Space) := physicalPhase k x * f k
  have hm (x : GW.Space) : AEStronglyMeasurable (rep x) (volume : Measure GW.Space) :=
    (Lp.memLp (phaseAt f x)).aestronglyMeasurable.congr (phaseAt_ae f x)
  have hl : ∀ᵐ k ∂(volume : Measure GW.Space), Tendsto (fun n => rep (xN n) k) atTop (𝓝 (rep x k)) :=
    Eventually.of_forall (fun k => (((continuous_physicalPhase k).tendsto x).comp hx).mul_const (f k))
  have hg : Measurable (fun k => ‖f k‖) := (Lp.stronglyMeasurable f).measurable.norm
  have hi := (Lp.memLp f).integrable_norm_pow (p := 2) (by norm_num)
  have hb (n : ℕ) : ∀ᵐ k ∂(volume : Measure GW.Space), ‖rep (xN n) k‖ ≤ ‖f k‖ :=
    Eventually.of_forall (fun k => by
      change ‖physicalPhase k (xN n) * f k‖ ≤ ‖f k‖
      rw [norm_mul,physicalPhase_norm,one_mul])
  obtain ⟨hs,hf,ht⟩ := dominated_l2_convergence (𝕜 := ℂ) (fun n => hm (xN n)) hl hg hi hb
  have he (y : GW.Space) (hy : MemLp (rep y) 2 (volume : Measure GW.Space)) :
      hy.toLp (rep y) = phaseAt f y := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp hy).trans (phaseAt_ae f y).symm
  have he' : (fun n => ‖(hs n).toLp (rep (xN n)) - hf.toLp (rep x)‖) =
      fun n => ‖phaseAt f (xN n) - phaseAt f x‖ := by
    funext n
    rw [he (xN n) (hs n),he x hf]
  rw [he'] at ht
  exact tendsto_iff_norm_sub_tendsto_zero.mpr ht

def scalarLinePhase (a t : ℝ) : ℂ := Complex.exp ((↑(-a*t) : ℂ)*Complex.I)

def phaseLineCoefficient (a : ℝ) : ℂ := (↑(-a) : ℂ)*Complex.I

lemma scalarLinePhase_norm (a t : ℝ) : ‖scalarLinePhase a t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

lemma scalarLinePhase_hasDerivAt (a t : ℝ) :
    HasDerivAt (scalarLinePhase a) (scalarLinePhase a t * phaseLineCoefficient a) t := by
  have h : HasDerivAt (fun r : ℝ => -a*r) (-a) t := by
    let L : ℝ →L[ℝ] ℝ := (-a) • ContinuousLinearMap.id ℝ ℝ
    have hL : L 1 = -a := by
      change -a * 1 = -a
      rw [mul_one]
    have h := L.hasDerivAt (x := t)
    rw [hL] at h
    exact h
  exact (h.ofReal_comp.mul_const Complex.I).cexp

lemma scalarLinePhase_continuous (a : ℝ) : Continuous (scalarLinePhase a) :=
  continuous_iff_continuousAt.mpr (fun t => (scalarLinePhase_hasDerivAt a t).continuousAt)

lemma phaseLineCoefficient_norm (a : ℝ) : ‖phaseLineCoefficient a‖ = |a| := by
  rw [phaseLineCoefficient,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_neg]

lemma scalarLinePhase_sub_one_bound (a : ℝ) :
    ‖scalarLinePhase a 1 - 1‖ ≤ |a| := by
  let d := fun t : ℝ => scalarLinePhase a t * phaseLineCoefficient a
  have hd : Continuous d := (scalarLinePhase_continuous a).mul continuous_const
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := scalarLinePhase a) (f' := d) (a := 0) (b := 1)
    (fun t _ => scalarLinePhase_hasDerivAt a t) (hd.intervalIntegrable 0 1)
  have h₀ : scalarLinePhase a 0 = 1 := by simp [scalarLinePhase]
  rw [h₀] at hi
  rw [← hi]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (f := d) (C := |a|) (fun t _ => by
      change ‖scalarLinePhase a t * phaseLineCoefficient a‖ ≤ _
      rw [norm_mul,scalarLinePhase_norm,phaseLineCoefficient_norm,one_mul])
  simpa only [sub_zero,abs_one,mul_one] using hb

lemma scalarLinePhase_increment_bound (a h : ℝ) : ‖scalarLinePhase a h - 1‖ ≤ |h| * |a| := by
  have he : scalarLinePhase a h = scalarLinePhase (a*h) 1 := by
    unfold scalarLinePhase
    congr 2
    ring
  rw [he]
  exact (scalarLinePhase_sub_one_bound (a*h)).trans_eq (by rw [abs_mul,mul_comm])

def momentumAxis (j : Fin 3) : GW.Space := EuclideanSpace.single j 1

lemma phaseAt_line (k x : GW.Space) (j : Fin 3) (t : ℝ) :
    physicalPhase k (x + t • momentumAxis j) = physicalPhase k x * scalarLinePhase (k j) t := by
  rw [physicalPhase_add_space]
  congr 1
  unfold physicalPhase scalarLinePhase momentumAxis
  rw [real_inner_smul_left,EuclideanSpace.inner_single_left]
  simp only [map_one,one_mul]
  congr 2
  ring

def phaseAxisCoefficientRep (f : GW.OnePhonon) (j : Fin 3) (k : GW.Space) : ℂ :=
  phaseLineCoefficient (k j) * f k

lemma phaseAxisCoefficient_memLp (f : GW.OnePhonon) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) :
    MemLp (phaseAxisCoefficientRep f j) 2 (volume : Measure GW.Space) := by
  apply (hj.const_smul (-Complex.I)).ae_eq
  apply Eventually.of_forall
  intro k
  unfold phaseAxisCoefficientRep phaseLineCoefficient
  simp only [Pi.smul_apply,smul_eq_mul,Complex.ofReal_neg]
  ring

def phaseAxisCoefficient (f : GW.OnePhonon) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) : GW.OnePhonon :=
  (phaseAxisCoefficient_memLp f j hj).toLp _

lemma phaseAxisCoefficient_ae (f : GW.OnePhonon) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) :
    phaseAxisCoefficient f j hj =ᵐ[(volume : Measure GW.Space)] phaseAxisCoefficientRep f j :=
  MemLp.coeFn_toLp _

def phaseAxisDiffRep (f : GW.OnePhonon) (j : Fin 3) (x : GW.Space) (h : ℝ) (k : GW.Space) : ℂ :=
  h⁻¹ • (physicalPhase k (x+h • momentumAxis j)*f k - physicalPhase k x*f k)

def phaseAxisDiff (f : GW.OnePhonon) (j : Fin 3) (x : GW.Space) (h : ℝ) : GW.OnePhonon :=
  h⁻¹ • (phaseAt f (x+h • momentumAxis j) - phaseAt f x)

lemma phaseAxisDiff_ae (f : GW.OnePhonon) (j : Fin 3) (x : GW.Space) (h : ℝ) :
    phaseAxisDiff f j x h =ᵐ[(volume : Measure GW.Space)] phaseAxisDiffRep f j x h := by
  let v := phaseAt f (x+h • momentumAxis j)
  let w := phaseAt f x
  filter_upwards [Lp.coeFn_smul h⁻¹ (v-w),Lp.coeFn_sub v w,phaseAt_ae f (x+h • momentumAxis j),
    phaseAt_ae f x] with k h₁ h₂ h₃ h₄
  change (h⁻¹ • (v-w)) k = _
  rw [h₁,Pi.smul_apply,h₂,Pi.sub_apply]
  change h⁻¹ • (v k-w k) = _
  rw [h₃,h₄]
  rfl

lemma phaseAxisDiffRep_bound (f : GW.OnePhonon) (j : Fin 3) (x : GW.Space) (h : ℝ) (k : GW.Space) :
    ‖phaseAxisDiffRep f j x h k‖ ≤ ‖phaseAxisCoefficientRep f j k‖ := by
  unfold phaseAxisDiffRep phaseAxisCoefficientRep
  rw [phaseAt_line,norm_smul,Real.norm_eq_abs,abs_inv,norm_mul,phaseLineCoefficient_norm]
  have he : physicalPhase k x * scalarLinePhase (k j) h * f k - physicalPhase k x * f k =
      physicalPhase k x * (scalarLinePhase (k j) h - 1) * f k := by ring
  rw [he,norm_mul,norm_mul,physicalPhase_norm,one_mul,← mul_assoc]
  by_cases hh : h = 0
  · simpa [hh] using (mul_nonneg (abs_nonneg (k j)) (norm_nonneg (f k)))
  have hb := mul_le_mul_of_nonneg_left (scalarLinePhase_increment_bound (k j) h)
    (inv_nonneg.mpr (abs_nonneg h))
  rw [← mul_assoc,inv_mul_cancel₀ (abs_ne_zero.mpr hh),one_mul] at hb
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

lemma phaseAxisRep_hasDerivAt (f : GW.OnePhonon) (j : Fin 3) (x k : GW.Space) :
    HasDerivAt (fun h : ℝ => physicalPhase k (x+h • momentumAxis j) * f k)
      (physicalPhase k x * phaseAxisCoefficientRep f j k) 0 := by
  have hz : scalarLinePhase (k j) 0 = 1 := by simp [scalarLinePhase]
  simp only [phaseAt_line,phaseAxisCoefficientRep]
  have hd := (((scalarLinePhase_hasDerivAt (k j) 0).const_mul (physicalPhase k x)).mul_const (f k))
  rw [hz,one_mul,mul_assoc] at hd
  exact hd

lemma phaseAxisDiffRep_tendsto (f : GW.OnePhonon) (j : Fin 3) (x k : GW.Space) :
    Tendsto (fun h => phaseAxisDiffRep f j x h k) (𝓝[≠] (0:ℝ))
      (𝓝 (physicalPhase k x * phaseAxisCoefficientRep f j k)) := by
  have h := (phaseAxisRep_hasDerivAt f j x k).tendsto_slope_zero
  simpa only [zero_add,zero_smul,add_zero,phaseAxisDiffRep] using h

lemma phaseAt_axis_hasDerivAt (f : GW.OnePhonon) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) (x : GW.Space) :
    HasDerivAt (fun h : ℝ => phaseAt f (x+h • momentumAxis j))
      (phaseAt (phaseAxisCoefficient f j hj) x) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simp only [zero_add,zero_smul,add_zero]
  change Tendsto (phaseAxisDiff f j x) (𝓝[≠] (0:ℝ)) (𝓝 (phaseAt (phaseAxisCoefficient f j hj) x))
  apply tendsto_iff_seq_tendsto.mpr
  intro hN hh
  let v := phaseAxisCoefficient f j hj
  let u := phaseAt v x
  let g : GW.Space → ℝ := fun k => ‖v k‖
  let rep : GW.Space → ℂ := fun k => physicalPhase k x * phaseAxisCoefficientRep f j k
  have hu : u =ᵐ[(volume : Measure GW.Space)] rep := by
    filter_upwards [phaseAt_ae v x,phaseAxisCoefficient_ae f j hj] with k h₁ h₂
    exact h₁.trans (congrArg (physicalPhase k x * ·) h₂)
  have hm (n : ℕ) : AEStronglyMeasurable (phaseAxisDiffRep f j x (hN n)) (volume : Measure GW.Space) :=
    (Lp.memLp (phaseAxisDiff f j x (hN n))).aestronglyMeasurable.congr (phaseAxisDiff_ae f j x _)
  have hl : ∀ᵐ k ∂(volume : Measure GW.Space),
      Tendsto (fun n => phaseAxisDiffRep f j x (hN n) k) atTop (𝓝 (rep k)) :=
    Eventually.of_forall (fun k => (phaseAxisDiffRep_tendsto f j x k).comp hh)
  have hg : Measurable g := (Lp.stronglyMeasurable v).measurable.norm
  have hgi : Integrable (fun k => g k^2) (volume : Measure GW.Space) :=
    (Lp.memLp v).integrable_norm_pow (p := 2) (by norm_num)
  have hb (n : ℕ) : ∀ᵐ k ∂(volume : Measure GW.Space),
      ‖phaseAxisDiffRep f j x (hN n) k‖ ≤ g k := by
    filter_upwards [phaseAxisCoefficient_ae f j hj] with k hk
    exact (phaseAxisDiffRep_bound f j x (hN n) k).trans_eq (congrArg norm hk.symm)
  obtain ⟨hs,hf,ht⟩ := dominated_l2_convergence (𝕜 := ℂ) hm hl hg hgi hb
  have he (n : ℕ) : (hs n).toLp (phaseAxisDiffRep f j x (hN n)) = phaseAxisDiff f j x (hN n) := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp (hs n)).trans (phaseAxisDiff_ae f j x _).symm
  have he' : hf.toLp rep = u := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp hf).trans hu.symm
  simp_rw [he,he'] at ht
  exact tendsto_iff_norm_sub_tendsto_zero.mpr ht

lemma phaseAt_axisDerivative_continuous (f : GW.OnePhonon) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) :
    Continuous (phaseAt (phaseAxisCoefficient f j hj)) :=
  phaseAt_continuous _

section AxisAssembly
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

lemma momentumAxis_norm (j : Fin 3) : ‖momentumAxis j‖ = 1 := by
  change ‖PiLp.single (β := fun _ : Fin 3 => ℝ) 2 j (1:ℝ)‖ = 1
  rw [PiLp.norm_single]
  exact norm_one

lemma momentumAxis_expansion (h : GW.Space) :
    h (0:Fin 3) • momentumAxis 0 + h 1 • momentumAxis 1 + h 2 • momentumAxis 2 = h := by
  ext j
  fin_cases j <;> simp [momentumAxis,EuclideanSpace.single,PiLp.single_apply]

def axisDerivativeCLM (d : Fin 3 → F) : GW.Space →L[ℝ] F :=
  ∑ j : Fin 3, (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j).smulRight (d j)

lemma axisDerivativeCLM_apply (d : Fin 3 → F) (h : GW.Space) :
    axisDerivativeCLM d h = ∑ j : Fin 3, h j • d j := by
  simp only [axisDerivativeCLM,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smulRight_apply]
  rfl

lemma axisDerivative_at_param {f : GW.Space → F} {d : Fin 3 → GW.Space → F}
    (hd : ∀ j x, HasDerivAt (fun t : ℝ => f (x+t • momentumAxis j)) (d j x) 0)
    (j : Fin 3) (x : GW.Space) (a : ℝ) :
    HasDerivAt (fun t : ℝ => f (x+t • momentumAxis j)) (d j (x+a • momentumAxis j)) a := by
  have h := hd j (x+a • momentumAxis j)
  have ht := (hasDerivAt_id a).sub_const a
  have ht' : HasDerivAt (fun t : ℝ => t-a) 1 a := ht
  have hh : HasDerivAt (fun t : ℝ => f ((x+a • momentumAxis j)+(t-a) • momentumAxis j))
      (d j (x+a • momentumAxis j)) a := by
    have he : a-a = (0:ℝ) := sub_self _
    have h' : HasDerivAt (fun t : ℝ => f ((x+a • momentumAxis j)+t • momentumAxis j))
        (d j (x+a • momentumAxis j)) (a-a) := he.symm ▸ h
    have hp := HasDerivAt.scomp (h := fun t : ℝ => t-a) a h' ht'
    rw [one_smul] at hp
    exact hp
  have he : (fun t : ℝ => f ((x+a • momentumAxis j)+(t-a) • momentumAxis j)) =
      fun t : ℝ => f (x+t • momentumAxis j) := by
    funext t
    rw [add_assoc,← add_smul]
    congr 2
    ring
  rwa [he] at hh

lemma axis_segment_remainder {f : GW.Space → F} {d : Fin 3 → GW.Space → F}
    (hd : ∀ j x, HasDerivAt (fun t : ℝ => f (x+t • momentumAxis j)) (d j x) 0)
    (hc : ∀ j, Continuous (d j)) (j : Fin 3) (x y : GW.Space) (a : ℝ) :
    f (y+a • momentumAxis j) - f y - a • d j x =
      ∫ t in 0..a, (d j (y+t • momentumAxis j) - d j x) := by
  have hcont : Continuous (fun t : ℝ => d j (y+t • momentumAxis j)) :=
    (hc j).comp (by fun_prop)
  have hi : IntervalIntegrable (fun t : ℝ => d j (y+t • momentumAxis j)) volume 0 a :=
    hcont.intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => axisDerivative_at_param hd j y t) hi
  simp only [zero_smul,add_zero] at h
  rw [intervalIntegral.integral_sub hi intervalIntegrable_const,h,intervalIntegral.integral_const,sub_zero]

lemma abs_le_of_mem_uIcc_zero {t a : ℝ} (ht : t ∈ Set.uIcc 0 a) : |t| ≤ |a| := by
  by_cases h : 0 ≤ a
  · rw [Set.uIcc_of_le h] at ht
    rw [abs_of_nonneg ht.1,abs_of_nonneg h]
    exact ht.2
  · have ha := le_of_not_ge h
    rw [Set.uIcc_of_ge ha] at ht
    rw [abs_of_nonpos ht.2,abs_of_nonpos ha]
    exact neg_le_neg ht.1

lemma axis_segment_bound {f : GW.Space → F} {d : Fin 3 → GW.Space → F}
    (hd : ∀ j x, HasDerivAt (fun t : ℝ => f (x+t • momentumAxis j)) (d j x) 0)
    (hc : ∀ j, Continuous (d j)) (j : Fin 3) (x y : GW.Space) (a δ ε : ℝ)
    (hy : ‖y-x‖ + |a| < δ)
    (hnear : ∀ z, ‖z-x‖ < δ → ‖d j z - d j x‖ ≤ ε) :
    ‖f (y+a • momentumAxis j) - f y - a • d j x‖ ≤ ε * |a| := by
  rw [axis_segment_remainder hd hc]
  have hbound : ‖∫ t in 0..a, (d j (y+t • momentumAxis j) - d j x)‖ ≤ ε * |a-0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    apply hnear
    have he : y + t • momentumAxis j - x = (y-x) + t • momentumAxis j := by abel
    rw [he]
    refine (norm_add_le _ _).trans_lt ?_
    rw [norm_smul,Real.norm_eq_abs,momentumAxis_norm,mul_one]
    exact (add_le_add_right (abs_le_of_mem_uIcc_zero (Set.uIoc_subset_uIcc ht)) _).trans_lt hy
  simpa only [sub_zero] using hbound

lemma axisDerivative_hasFDerivAt {f : GW.Space → F} {d : Fin 3 → GW.Space → F}
    (hd : ∀ j x, HasDerivAt (fun t : ℝ => f (x+t • momentumAxis j)) (d j x) 0)
    (hc : ∀ j, Continuous (d j)) (x : GW.Space) :
    HasFDerivAt f (axisDerivativeCLM (fun j => d j x)) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero,Asymptotics.isLittleO_iff]
  intro ε hε
  have hnear : ∀ᶠ z in 𝓝 x, ∀ j : Fin 3, ‖d j z-d j x‖ ≤ ε/3 := by
    apply Filter.eventually_all.mpr
    intro j
    filter_upwards [((hc j).continuousAt (x := x)).eventually (Metric.ball_mem_nhds (d j x) (by positivity : 0 < ε/3))]
      with z hz
    rw [← dist_eq_norm]
    exact (show dist (d j z) (d j x) < ε/3 from hz).le
  obtain ⟨δ,hδ,hδnear⟩ := Metric.mem_nhds_iff.mp hnear
  filter_upwards [Metric.ball_mem_nhds (0 : GW.Space) (by positivity : 0 < δ/3)] with h hh
  have hsmall : ‖h‖ < δ/3 := by simpa only [Metric.mem_ball,dist_zero_right] using hh
  let y₁ := x + h (0:Fin 3) • momentumAxis 0
  let y₂ := y₁ + h (1:Fin 3) • momentumAxis 1
  let y₃ := y₂ + h (2:Fin 3) • momentumAxis 2
  have hy₃ : y₃ = x+h := by
    change ((x + h (0:Fin 3) • momentumAxis 0) + h 1 • momentumAxis 1) + h 2 • momentumAxis 2 = x+h
    calc
      _ = x + (h (0:Fin 3) • momentumAxis 0 + h 1 • momentumAxis 1 + h 2 • momentumAxis 2) := by abel
      _ = _ := congrArg (x + ·) (momentumAxis_expansion h)
  have hcoord (j : Fin 3) : |h j| ≤ ‖h‖ := PiLp.norm_apply_le h j
  have hy₁ : ‖y₁-x‖ ≤ ‖h‖ := by
    have he : y₁-x = h (0:Fin 3) • momentumAxis 0 := by dsimp [y₁]; abel
    rw [he,norm_smul,Real.norm_eq_abs,momentumAxis_norm,mul_one]
    exact hcoord 0
  have hy₂ : ‖y₂-x‖ ≤ 2*‖h‖ := by
    have he : y₂-x = (y₁-x) + h (1:Fin 3) • momentumAxis 1 := by dsimp [y₂]; abel
    rw [he]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul,Real.norm_eq_abs,momentumAxis_norm,mul_one]
    linarith [hcoord 1]
  have hb (j : Fin 3) (z : GW.Space) (hz : ‖z-x‖ < δ) : ‖d j z-d j x‖ ≤ ε/3 :=
    hδnear (show z ∈ Metric.ball x δ from by rwa [Metric.mem_ball,dist_eq_norm]) j
  have h₀ := axis_segment_bound hd hc 0 x x (h 0) δ (ε/3) (by
    rw [sub_self,norm_zero,zero_add]
    linarith [hcoord 0]) (hb 0)
  have h₁ := axis_segment_bound hd hc 1 x y₁ (h 1) δ (ε/3) (by linarith [hcoord 1]) (hb 1)
  have h₂ := axis_segment_bound hd hc 2 x y₂ (h 2) δ (ε/3) (by linarith [hcoord 2]) (hb 2)
  change ‖f (x+h)-f x-axisDerivativeCLM (fun j => d j x) h‖ ≤ ε*‖h‖
  rw [axisDerivativeCLM_apply,Fin.sum_univ_three,← hy₃]
  let e₀ := f y₁ - f x - h (0:Fin 3) • d 0 x
  let e₁ := f y₂ - f y₁ - h (1:Fin 3) • d 1 x
  let e₂ := f y₃ - f y₂ - h (2:Fin 3) • d 2 x
  have he : f y₃ - f x - (h (0:Fin 3) • d 0 x + h 1 • d 1 x + h 2 • d 2 x) = e₀+e₁+e₂ := by
    dsimp [e₀,e₁,e₂]
    abel
  rw [he]
  have hnorm₀ : ‖e₀‖ ≤ (ε/3) * |h (0:Fin 3)| := h₀
  have hnorm₁ : ‖e₁‖ ≤ (ε/3) * |h (1:Fin 3)| := h₁
  have hnorm₂ : ‖e₂‖ ≤ (ε/3) * |h (2:Fin 3)| := h₂
  calc
    _ ≤ ‖e₀‖+‖e₁‖+‖e₂‖ := (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ ≤ (ε/3)*‖h‖ + (ε/3)*‖h‖ + (ε/3)*‖h‖ :=
      add_le_add (add_le_add (hnorm₀.trans (mul_le_mul_of_nonneg_left (hcoord 0) (by positivity)))
        (hnorm₁.trans (mul_le_mul_of_nonneg_left (hcoord 1) (by positivity))))
        (hnorm₂.trans (mul_le_mul_of_nonneg_left (hcoord 2) (by positivity)))
    _ = _ := by ring

end AxisAssembly
section BoundedPhase
def phaseSupportBound (f : GW.OnePhonon) (L : ℝ) : Prop :=
  ∀ᵐ k ∂(volume : Measure GW.Space), L < ‖k‖ → f k = 0

lemma phaseCoordinate_memLp_of_support (f : GW.OnePhonon) (L : ℝ) (hf : phaseSupportBound f L) (j : Fin 3) :
    MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space) := by
  apply (Lp.memLp f).of_le_mul (c := L)
  · have hm : Measurable (fun k : GW.Space => (k j : ℂ)*f k) := by
      apply Measurable.mul _ (Lp.stronglyMeasurable f).measurable
      exact Complex.continuous_ofReal.measurable.comp (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) j).measurable
    exact hm.aestronglyMeasurable
  · filter_upwards [hf] with k hk
    by_cases h : L < ‖k‖
    · simp [hk h]
    · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right ((PiLp.norm_apply_le k j).trans (le_of_not_gt h)) (norm_nonneg _)

def boundedPhaseCoordinate (f : GW.OnePhonon) (L : ℝ) (hf : phaseSupportBound f L) (j : Fin 3) : GW.OnePhonon :=
  phaseAxisCoefficient f j (phaseCoordinate_memLp_of_support f L hf j)

lemma boundedPhaseCoordinate_support (f : GW.OnePhonon) (L : ℝ) (hf : phaseSupportBound f L) (j : Fin 3) :
    phaseSupportBound (boundedPhaseCoordinate f L hf j) L := by
  filter_upwards [hf,phaseAxisCoefficient_ae f j (phaseCoordinate_memLp_of_support f L hf j)] with k hk hq
  intro h
  rw [show boundedPhaseCoordinate f L hf j k = _ from hq,phaseAxisCoefficientRep,hk h,mul_zero]

lemma boundedPhaseCoordinate_norm (f : GW.OnePhonon) (L : ℝ) (hf : phaseSupportBound f L) (j : Fin 3) :
    ‖boundedPhaseCoordinate f L hf j‖ ≤ L * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hf,phaseAxisCoefficient_ae f j (phaseCoordinate_memLp_of_support f L hf j)] with k hk hq
  change ‖boundedPhaseCoordinate f L hf j k‖ ≤ _
  rw [show boundedPhaseCoordinate f L hf j k = _ from hq]
  by_cases h : L < ‖k‖
  · simp [phaseAxisCoefficientRep,hk h]
  · rw [phaseAxisCoefficientRep,norm_mul,phaseLineCoefficient_norm]
    exact mul_le_mul_of_nonneg_right ((PiLp.norm_apply_le k j).trans (le_of_not_gt h)) (norm_nonneg _)

lemma boundedPhase_hasFDerivAt (f : GW.OnePhonon) (L : ℝ) (hf : phaseSupportBound f L) (x : GW.Space) :
    HasFDerivAt (phaseAt f) (axisDerivativeCLM (fun j => phaseAt (boundedPhaseCoordinate f L hf j) x)) x :=
  axisDerivative_hasFDerivAt
    (fun j y => phaseAt_axis_hasDerivAt f j (phaseCoordinate_memLp_of_support f L hf j) y)
    (fun j => phaseAt_continuous (boundedPhaseCoordinate f L hf j)) x

def phaseCoordinatePartial (j : Fin 3) (u : GW.Space → GW.OnePhonon) (x : GW.Space) : GW.OnePhonon :=
  deriv (fun t : ℝ => u (x+t • momentumAxis j)) 0

def iteratedCoordinatePartial (js : List (Fin 3)) (u : GW.Space → GW.OnePhonon) : GW.Space → GW.OnePhonon :=
  match js with
  | [] => u
  | j::rest => iteratedCoordinatePartial rest (phaseCoordinatePartial j u)

def boundedPhaseWord (L : ℝ) (js : List (Fin 3))
    (f : {f : GW.OnePhonon // phaseSupportBound f L}) : {f : GW.OnePhonon // phaseSupportBound f L} :=
  match js with
  | [] => f
  | j::rest => boundedPhaseWord L rest
      ⟨boundedPhaseCoordinate f.val L f.property j,boundedPhaseCoordinate_support f.val L f.property j⟩

lemma boundedPhaseWord_norm (L : ℝ) (hL : 0 ≤ L) (js : List (Fin 3))
    (f : {f : GW.OnePhonon // phaseSupportBound f L}) :
    ‖(boundedPhaseWord L js f).val‖ ≤ L^js.length * ‖f.val‖ := by
  induction js generalizing f with
  | nil => simp [boundedPhaseWord]
  | cons j rest ih =>
    let g : {f : GW.OnePhonon // phaseSupportBound f L} :=
      ⟨boundedPhaseCoordinate f.val L f.property j,boundedPhaseCoordinate_support f.val L f.property j⟩
    calc
      _ ≤ L^rest.length * ‖g.val‖ := ih g
      _ ≤ L^rest.length * (L * ‖f.val‖) :=
        mul_le_mul_of_nonneg_left (boundedPhaseCoordinate_norm f.val L f.property j) (pow_nonneg hL _)
      _ = _ := by rw [List.length_cons,pow_succ,mul_assoc]

lemma iteratedCoordinatePartial_phase (L : ℝ) (js : List (Fin 3))
    (f : {f : GW.OnePhonon // phaseSupportBound f L}) :
    iteratedCoordinatePartial js (phaseAt f.val) = phaseAt (boundedPhaseWord L js f).val := by
  induction js generalizing f with
  | nil => rfl
  | cons j rest ih =>
    have he : phaseCoordinatePartial j (phaseAt f.val) =
        phaseAt (boundedPhaseCoordinate f.val L f.property j) := by
      funext x
      exact (phaseAt_axis_hasDerivAt f.val j (phaseCoordinate_memLp_of_support f.val L f.property j) x).deriv
    rw [iteratedCoordinatePartial,he]
    exact ih ⟨boundedPhaseCoordinate f.val L f.property j,boundedPhaseCoordinate_support f.val L f.property j⟩

lemma iteratedCoordinatePartial_phase_norm (L : ℝ) (hL : 0 ≤ L) (js : List (Fin 3))
    (f : GW.OnePhonon) (hf : phaseSupportBound f L) (x : GW.Space) :
    ‖iteratedCoordinatePartial js (phaseAt f) x‖ ≤ L^js.length * ‖f‖ := by
  have he := congrArg (fun u : GW.Space → GW.OnePhonon => u x)
    (iteratedCoordinatePartial_phase L js ⟨f,hf⟩)
  rw [he,phaseAt_norm]
  exact boundedPhaseWord_norm L hL js ⟨f,hf⟩

lemma boundedPhase_contDiff_nat (L : ℝ) (m : ℕ) (f : GW.OnePhonon) (hf : phaseSupportBound f L) :
    ContDiff ℝ m (phaseAt f) := by
  induction m generalizing f with
  | zero => exact contDiff_zero.mpr (phaseAt_continuous f)
  | succ m ih =>
    apply (contDiff_succ_iff_hasFDerivAt (n := m)).mpr
    refine ⟨fun x => axisDerivativeCLM (fun j => phaseAt (boundedPhaseCoordinate f L hf j) x),?_,
      boundedPhase_hasFDerivAt f L hf⟩
    change ContDiff ℝ m (fun x => ∑ j : Fin 3, (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j).smulRight
      (phaseAt (boundedPhaseCoordinate f L hf j) x))
    apply ContDiff.sum
    intro j _
    exact contDiff_const.smulRight (ih (boundedPhaseCoordinate f L hf j)
      (boundedPhaseCoordinate_support f L hf j))

lemma boundedPhase_contDiff (L : ℝ) (f : GW.OnePhonon) (hf : phaseSupportBound f L) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (phaseAt f) :=
  contDiff_iff_forall_nat_le.mpr (fun m _ => boundedPhase_contDiff_nat L m f hf)

end BoundedPhase
end GW.Analysis
