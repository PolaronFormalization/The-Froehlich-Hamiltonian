module
public import GW.Operators.SelfadjointCriterion
public import GW.Spaces.WeightedL2
public import GW.Analysis.L2Domination
@[expose] public section
noncomputable section
open MeasureTheory
open scoped Topology InnerProductSpace ENNReal
namespace GW.Analysis
variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] {μ : Measure X}

/-- The maximal real product on exactly the L² product domain. -/
def realMultiplier (m : X → ℝ) (μ : Measure X) : Lp H 2 μ →ₗ.[ℂ] Lp H 2 μ :=
  maximalMultiplier (fun x => (m x : ℂ)) μ

lemma realMultiplier_domain (m : X → ℝ) (u : Lp H 2 μ) :
    u ∈ (realMultiplier (H := H) m μ).domain ↔ MemLp (fun x => (m x : ℂ) • u x) 2 μ :=
  mem_multiplierDomain_iff _ u

lemma realMultiplier_ae (m : X → ℝ) (u : (realMultiplier (H := H) m μ).domain) :
    (fun x => (m x : ℂ) • (u : Lp H 2 μ) x) =ᵐ[μ] realMultiplier (H := H) m μ u :=
  multiplierValue_ae _ u

lemma realMultiplier_symmetric (m : X → ℝ) :
    (realMultiplier (H := H) m μ).IsFormalAdjoint (realMultiplier (H := H) m μ) := by
  intro u v
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [realMultiplier_ae m u,realMultiplier_ae m v] with x hu hv
  rw [← hu,← hv,inner_smul_left,inner_smul_right]
  simp only [Complex.conj_ofReal]

lemma real_resolvent_scalar_ne (m : ℝ) (z : ℂ) (hz : z.im ≠ 0) : (m : ℂ)-z ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.sub_im,Complex.ofReal_im,Complex.zero_im,zero_sub,neg_eq_zero] at hi
  exact hz hi

lemma real_resolvent_scalar_bound (m : ℝ) (z : ℂ) (hz : z.im ≠ 0) :
    ‖((m : ℂ)-z)⁻¹‖ ≤ |z.im|⁻¹ := by
  rw [norm_inv]
  apply inv_anti₀ (abs_pos.mpr hz)
  simpa only [Complex.sub_im,Complex.ofReal_im,zero_sub,abs_neg] using Complex.abs_im_le_norm ((m : ℂ)-z)

lemma real_resolvent_measurable {m : X → ℝ} (hm : Measurable m) (z : ℂ) :
    Measurable (fun x => ((m x : ℂ)-z)⁻¹) :=
  ((Complex.continuous_ofReal.measurable.comp hm).sub measurable_const).inv

def realResolvent {m : X → ℝ} (hm : Measurable m) (z : ℂ) (hz : z.im ≠ 0) :
    Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  boundedMultiplier (fun x => ((m x : ℂ)-z)⁻¹) (real_resolvent_measurable hm z)
    (Filter.Eventually.of_forall (fun x => real_resolvent_scalar_bound (m x) z hz))

lemma realResolvent_ae {m : X → ℝ} (hm : Measurable m) (z : ℂ) (hz : z.im ≠ 0) (u : Lp H 2 μ) :
    (fun x => ((m x : ℂ)-z)⁻¹ • u x) =ᵐ[μ] realResolvent hm z hz u :=
  boundedMultiplier_ae _ _ _ u

lemma realResolvent_norm {m : X → ℝ} (hm : Measurable m) (z : ℂ) (hz : z.im ≠ 0) :
    ‖realResolvent (H := H) (μ := μ) hm z hz‖ ≤ |z.im|⁻¹ :=
  boundedMultiplier_opNorm_le _ _ (inv_nonneg.mpr (abs_nonneg _)) _

lemma realResolvent_product_ae {m : X → ℝ} (hm : Measurable m) (z : ℂ) (hz : z.im ≠ 0) (f : Lp H 2 μ) :
    (fun x => (m x : ℂ) • realResolvent hm z hz f x) =ᵐ[μ]
      ((f+z • realResolvent hm z hz f : Lp H 2 μ) : X → H) := by
  filter_upwards [realResolvent_ae hm z hz f,
    Lp.coeFn_add f (z • realResolvent hm z hz f),Lp.coeFn_smul z (realResolvent hm z hz f)] with x hx ha hs
  simp only [Pi.add_apply,Pi.smul_apply] at ha hs
  have hn := real_resolvent_scalar_ne (m x) z hz
  have he : (m x : ℂ) * ((m x : ℂ)-z)⁻¹ = 1+z*((m x : ℂ)-z)⁻¹ := by
    field_simp [hn]
    ring
  rw [ha,hs,← hx]
  simp only [smul_smul,he,add_smul,one_smul]

lemma realResolvent_mem_domain {m : X → ℝ} (hm : Measurable m) (z : ℂ) (hz : z.im ≠ 0) (f : Lp H 2 μ) :
    realResolvent hm z hz f ∈ (realMultiplier (H := H) m μ).domain :=
  ⟨f+z • realResolvent hm z hz f,realResolvent_product_ae hm z hz f⟩

def realResolventInput {m : X → ℝ} (hm : Measurable m) (z : ℂ) (hz : z.im ≠ 0) (f : Lp H 2 μ) :
    (realMultiplier (H := H) m μ).domain := ⟨realResolvent hm z hz f,realResolvent_mem_domain hm z hz f⟩

lemma realResolvent_action {m : X → ℝ} (hm : Measurable m) (z : ℂ) (hz : z.im ≠ 0) (f : Lp H 2 μ) :
    realMultiplier (H := H) m μ (realResolventInput hm z hz f) = f+z • realResolvent hm z hz f := by
  apply Lp.ext
  exact (realMultiplier_ae m (realResolventInput hm z hz f)).symm.trans
    (realResolvent_product_ae hm z hz f)

lemma realResolvent_shift_right {m : X → ℝ} (hm : Measurable m) (z : ℂ) (hz : z.im ≠ 0) (f : Lp H 2 μ) :
    GW.Operators.complexShift (realMultiplier (H := H) m μ) z (realResolventInput hm z hz f) = f := by
  rw [GW.Operators.complexShift_apply,realResolvent_action]
  exact add_sub_cancel_right _ _

lemma realResolvent_shift_left {m : X → ℝ} (hm : Measurable m) (z : ℂ) (hz : z.im ≠ 0)
    (u : (realMultiplier (H := H) m μ).domain) :
    realResolvent hm z hz (GW.Operators.complexShift (realMultiplier (H := H) m μ) z u) = (u : Lp H 2 μ) := by
  apply Lp.ext
  filter_upwards [realResolvent_ae hm z hz (GW.Operators.complexShift (realMultiplier (H := H) m μ) z u),
    realMultiplier_ae m u,Lp.coeFn_sub (realMultiplier (H := H) m μ u) (z • (u : Lp H 2 μ)),
    Lp.coeFn_smul z (u : Lp H 2 μ)] with x hr hm hs hc
  change _ = _ at hr
  change (GW.Operators.complexShift (realMultiplier (H := H) m μ) z u : X → H) x = _ at hs
  simp only [Pi.sub_apply,Pi.smul_apply] at hs hc
  rw [← hr,hs,hc,← hm,← sub_smul,smul_smul,
    inv_mul_cancel₀ (real_resolvent_scalar_ne (m x) z hz),one_smul]

lemma realMultiplier_shift_surjective {m : X → ℝ} (hm : Measurable m) (z : ℂ) (hz : z.im ≠ 0) :
    Function.Surjective (GW.Operators.complexShift (realMultiplier (H := H) m μ) z) :=
  fun f => ⟨realResolventInput hm z hz f,realResolvent_shift_right hm z hz f⟩

def realCutoffSet (m : X → ℝ) (n : ℕ) : Set X := {x | |m x| ≤ (n : ℝ)}

lemma realCutoffSet_measurable {m : X → ℝ} (hm : Measurable m) (n : ℕ) :
    MeasurableSet (realCutoffSet m n) := measurableSet_le (continuous_abs.measurable.comp hm) measurable_const

def realCutoff {m : X → ℝ} (hm : Measurable m) (n : ℕ) : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  boundedMultiplier ((realCutoffSet m n).indicator (fun _ => (1 : ℂ)))
    (measurable_const.indicator (realCutoffSet_measurable hm n)) (C := 1)
    (Filter.Eventually.of_forall (fun x => by
      by_cases hx : x ∈ realCutoffSet m n <;> simp [hx]))

lemma realCutoff_ae {m : X → ℝ} (hm : Measurable m) (n : ℕ) (u : Lp H 2 μ) :
    (realCutoffSet m n).indicator (u : X → H) =ᵐ[μ] realCutoff hm n u := by
  have h := boundedMultiplier_ae ((realCutoffSet m n).indicator (fun _ => (1 : ℂ)))
    (measurable_const.indicator (realCutoffSet_measurable hm n)) (C := 1)
    (Filter.Eventually.of_forall (fun x => by
      by_cases hx : x ∈ realCutoffSet m n <;> simp [hx])) u
  convert h using 1
  · ext x
    by_cases hx : x ∈ realCutoffSet m n <;> simp [hx]
  · rfl

lemma truncated_real_bound (m : X → ℝ) (n : ℕ) :
    ∀ᵐ x ∂μ, ‖(realCutoffSet m n).indicator (fun x => (m x : ℂ)) x‖ ≤ (n : ℝ) := by
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : x ∈ realCutoffSet m n
  · have hle : |m x| ≤ (n : ℝ) := hx
    simpa only [Set.indicator_of_mem hx,Complex.norm_real,Real.norm_eq_abs] using hle
  · simp only [Set.indicator_of_notMem hx,norm_zero]
    exact Nat.cast_nonneg n

def truncatedReal {m : X → ℝ} (hm : Measurable m) (n : ℕ) : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  boundedMultiplier ((realCutoffSet m n).indicator (fun x => (m x : ℂ)))
    ((Complex.continuous_ofReal.measurable.comp hm).indicator (realCutoffSet_measurable hm n))
    (truncated_real_bound m n)

lemma truncatedReal_ae {m : X → ℝ} (hm : Measurable m) (n : ℕ) (u : Lp H 2 μ) :
    (fun x => (realCutoffSet m n).indicator (fun x => (m x : ℂ)) x • u x) =ᵐ[μ]
      truncatedReal hm n u := boundedMultiplier_ae _ _ _ u

lemma realCutoff_mem_domain {m : X → ℝ} (hm : Measurable m) (n : ℕ) (u : Lp H 2 μ) :
    realCutoff hm n u ∈ (realMultiplier (H := H) m μ).domain := by
  refine ⟨truncatedReal hm n u,?_⟩
  filter_upwards [realCutoff_ae hm n u,truncatedReal_ae hm n u] with x hx hy
  rw [← hx,← hy]
  by_cases he : x ∈ realCutoffSet m n <;> simp [he]

lemma realCutoff_tendsto {m : X → ℝ} (hm : Measurable m) (u : Lp H 2 μ) :
    Filter.Tendsto (fun n => realCutoff hm n u) Filter.atTop (𝓝 u) := by
  have he : ∀ᵐ x ∂μ, ∀ᶠ n : ℕ in Filter.atTop, x ∈ realCutoffSet m n := by
    apply Filter.Eventually.of_forall
    intro x
    obtain ⟨N,hN⟩ := exists_nat_ge |m x|
    exact (Filter.eventually_ge_atTop N).mono (fun n hn => hN.trans (Nat.cast_le.mpr hn))
  exact GW.Spaces.WeightedL2.cutoff_tendsto (w := fun _ : X => (1 : ℝ))
    (realCutoffSet m) (realCutoffSet_measurable hm) he u

lemma realMultiplier_dense {m : X → ℝ} (hm : Measurable m) :
    Dense ((realMultiplier (H := H) m μ).domain : Set (Lp H 2 μ)) := by
  intro u
  exact mem_closure_of_tendsto (realCutoff_tendsto hm u)
    (Filter.Eventually.of_forall (fun n => realCutoff_mem_domain hm n u))

lemma realCutoff_action {m : X → ℝ} (hm : Measurable m) (n : ℕ)
    (u : (realMultiplier (H := H) m μ).domain) :
    realCutoff hm n (realMultiplier (H := H) m μ u) = truncatedReal hm n (u : Lp H 2 μ) := by
  apply Lp.ext
  filter_upwards [realCutoff_ae hm n (realMultiplier (H := H) m μ u),
    truncatedReal_ae hm n (u : Lp H 2 μ),realMultiplier_ae m u] with x hc ht hu
  rw [← hc,← ht]
  by_cases hx : x ∈ realCutoffSet m n <;> simp [hx,← hu]

lemma realMultiplier_closed {m : X → ℝ} (hm : Measurable m) :
    (realMultiplier (H := H) m μ).IsClosed := by
  apply isSeqClosed_iff_isClosed.mp
  intro a p ha hp
  have he (n : ℕ) : realCutoff hm n p.2 = truncatedReal hm n p.1 := by
    have hseq (j : ℕ) : realCutoff hm n (a j).2 = truncatedReal hm n (a j).1 := by
      obtain ⟨u,hu⟩ := (realMultiplier (H := H) m μ).mem_graph_iff'.mp (ha j)
      rw [← hu]
      exact realCutoff_action hm n u
    have h1 := ((realCutoff (H := H) (μ := μ) hm n).continuous.tendsto p.2).comp ((continuous_snd.tendsto p).comp hp)
    have h2 := ((truncatedReal (H := H) (μ := μ) hm n).continuous.tendsto p.1).comp ((continuous_fst.tendsto p).comp hp)
    exact tendsto_nhds_unique h1 (h2.congr' (Filter.Eventually.of_forall (fun j => (hseq j).symm)))
  have htrunc (n : ℕ) : (realCutoffSet m n).indicator (p.2 : X → H) =ᵐ[μ]
      (fun x => (realCutoffSet m n).indicator (fun x => (m x : ℂ)) x • p.1 x) := by
    have hcoe : ((realCutoff hm n p.2 : Lp H 2 μ) : X → H) =ᵐ[μ]
        (truncatedReal hm n p.1 : X → H) := Filter.EventuallyEq.of_eq (congrArg (fun u : Lp H 2 μ => (u : X → H)) (he n))
    exact (realCutoff_ae hm n p.2).trans (hcoe.trans (truncatedReal_ae hm n p.1).symm)
  have hprod : (fun x => (m x : ℂ) • p.1 x) =ᵐ[μ] p.2 := by
    filter_upwards [ae_all_iff.mpr htrunc] with x hx
    obtain ⟨N,hN⟩ := exists_nat_ge |m x|
    have hmem : x ∈ realCutoffSet m N := hN
    simpa only [Set.indicator_of_mem hmem] using (hx N).symm
  let u : (realMultiplier (H := H) m μ).domain := ⟨p.1,⟨p.2,hprod⟩⟩
  apply (realMultiplier (H := H) m μ).mem_graph_iff.mpr
  refine ⟨u,rfl,?_⟩
  apply Lp.ext
  exact (realMultiplier_ae m u).symm.trans hprod

/-- Source notation for nonnegative real multiplication powers, defined maximally. -/
def realMultiplierPower (m : X → ℝ) (θ : ℝ) (μ : Measure X) : Lp H 2 μ →ₗ.[ℂ] Lp H 2 μ :=
  realMultiplier (fun x => (m x) ^ θ) μ

lemma realMultiplierPower_domain (m : X → ℝ) (θ : ℝ) (u : Lp H 2 μ) :
    u ∈ (realMultiplierPower m θ μ).domain ↔ MemLp (fun x => ((m x) ^ θ : ℝ) • u x) 2 μ := by
  change u ∈ (realMultiplier (H := H) (fun x => (m x) ^ θ) μ).domain ↔ _
  rw [realMultiplier_domain]
  rfl

lemma realMultiplier_one : realMultiplier (H := H) (fun _ : X => 1) μ =
    (LinearMap.id : Lp H 2 μ →ₗ[ℂ] Lp H 2 μ).toPMap ⊤ := by
  apply LinearPMap.ext
  · change (realMultiplier (H := H) (fun _ : X => 1) μ).domain = ⊤
    apply top_unique
    intro u _
    refine ⟨u,Filter.Eventually.of_forall (fun x => ?_)⟩
    simp only [Complex.ofReal_one,one_smul]
  · intro u hu ht
    change realMultiplier (H := H) (fun _ : X => 1) μ ⟨u,hu⟩ = u
    apply Lp.ext
    filter_upwards [realMultiplier_ae (fun _ : X => 1) ⟨u,hu⟩] with x hx
    simpa only [Complex.ofReal_one,one_smul] using hx.symm

lemma realMultiplierPower_zero (m : X → ℝ) : realMultiplierPower (H := H) m 0 μ =
    (LinearMap.id : Lp H 2 μ →ₗ[ℂ] Lp H 2 μ).toPMap ⊤ := by
  simp only [realMultiplierPower,Real.rpow_zero]
  exact realMultiplier_one

variable [CompleteSpace H]

lemma realMultiplier_selfadjoint {m : X → ℝ} (hm : Measurable m) :
    IsSelfAdjointOperator (realMultiplier (H := H) m μ) := by
  apply GW.Operators.selfadjoint_of_imaginary_ranges (realMultiplier (H := H) m μ)
    (realMultiplier_dense hm) (realMultiplier_symmetric m) (t := 1) (by norm_num)
  · exact realMultiplier_shift_surjective hm _ (by simp)
  · exact realMultiplier_shift_surjective hm _ (by simp)

lemma realMultiplier_resolvent {m : X → ℝ} (hm : Measurable m) (z : ℂ) (hz : z.im ≠ 0) :
    GW.Operators.resolvent (realMultiplier (H := H) m μ) (realMultiplier_selfadjoint hm) z hz =
      realResolvent hm z hz := by
  apply ContinuousLinearMap.ext
  intro f
  have he := realResolvent_shift_left hm z hz
    (GW.Operators.resolventInput (realMultiplier (H := H) m μ) (realMultiplier_selfadjoint hm) z hz f)
  rw [GW.Operators.resolventInput_action] at he
  exact he.symm

end GW.Analysis
