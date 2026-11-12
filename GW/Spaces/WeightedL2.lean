module

public import GW.Analysis.L2Domination
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! Source basic:weighted-space, with the reciprocal-coordinate carrier
fixed by §3. Carrier vectors are weighted coordinates, and the ambient
embedding multiplies by w⁻¹. No ambient-subtype norm is used as a weighted norm. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace GW.Spaces

variable {X : Type*} [MeasurableSpace X]

/-- A named copy of the complete L² coordinate space, with its original norm. -/
def WeightedL2 (H : Type*) [NormedAddCommGroup H] (_w : X → ℝ) (μ : Measure X) :=
  Lp H 2 μ

namespace WeightedL2
variable {H : Type*} [NormedAddCommGroup H] {w : X → ℝ} {μ : Measure X}
instance : NormedAddCommGroup (WeightedL2 H w μ) := inferInstanceAs (NormedAddCommGroup (Lp H 2 μ))
instance [NormedSpace ℂ H] : NormedSpace ℂ (WeightedL2 H w μ) :=
  inferInstanceAs (NormedSpace ℂ (Lp H 2 μ))
instance [InnerProductSpace ℂ H] : InnerProductSpace ℂ (WeightedL2 H w μ) :=
  inferInstanceAs (InnerProductSpace ℂ (Lp H 2 μ))
instance [CompleteSpace H] : CompleteSpace (WeightedL2 H w μ) :=
  inferInstanceAs (CompleteSpace (Lp H 2 μ))

variable [InnerProductSpace ℂ H]

/-- Coordinates in the named copy agree isometrically with the original L² space. -/
def coordinates : WeightedL2 H w μ ≃ₗᵢ[ℂ] Lp H 2 μ :=
  LinearIsometryEquiv.refl ℂ (Lp H 2 μ)

lemma reciprocal_bound (hw1 : ∀ x, 1 ≤ w x) :
    ∀ᵐ x ∂μ, ‖(((w x)⁻¹ : ℝ) : ℂ)‖ ≤ 1 := by
  apply Eventually.of_forall
  intro x
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (zero_lt_one.trans_le (hw1 x)))]
  exact inv_le_one_of_one_le₀ (hw1 x)

/-- The source ambient embedding, not an identity on ambient subtype vectors. -/
def embed (hw : Measurable w) (hw1 : ∀ x, 1 ≤ w x) :
    WeightedL2 H w μ →L[ℂ] Lp H 2 μ :=
  (GW.Analysis.boundedMultiplier (fun x => (((w x)⁻¹ : ℝ) : ℂ))
    (Complex.continuous_ofReal.measurable.comp hw.inv) (reciprocal_bound hw1)).comp
    coordinates.toLinearIsometry.toContinuousLinearMap

lemma embed_ae (hw : Measurable w) (hw1 : ∀ x, 1 ≤ w x) (f : WeightedL2 H w μ) :
    (fun x => (((w x)⁻¹ : ℝ) : ℂ) • coordinates f x) =ᵐ[μ] embed hw hw1 f :=
  GW.Analysis.boundedMultiplier_ae _
    (Complex.continuous_ofReal.measurable.comp hw.inv) (reciprocal_bound hw1) (coordinates f)

lemma embed_norm_le (hw : Measurable w) (hw1 : ∀ x, 1 ≤ w x) (f : WeightedL2 H w μ) :
    ‖embed hw hw1 f‖ ≤ ‖f‖ := by
  calc
    ‖embed hw hw1 f‖ ≤ 1 * ‖coordinates f‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [embed_ae hw hw1 f, reciprocal_bound (μ := μ) hw1] with x hx hb
      rw [← hx, norm_smul]
      exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    _ = ‖f‖ := by rw [one_mul, LinearIsometryEquiv.norm_map]

/-- Multiplication by w recovers exactly the input coordinate class. -/
lemma weighted_embed_ae (hw : Measurable w) (hw1 : ∀ x, 1 ≤ w x)
    (f : WeightedL2 H w μ) :
    (fun x => (w x : ℂ) • embed hw hw1 f x) =ᵐ[μ] coordinates f := by
  filter_upwards [embed_ae hw hw1 f] with x hx
  rw [← hx, smul_smul]
  have hne : w x ≠ 0 := ne_of_gt (zero_lt_one.trans_le (hw1 x))
  simp [hne]

/-- Every embedded vector lies in the actual maximal weighted domain. -/
lemma embed_mem_domain (hw : Measurable w) (hw1 : ∀ x, 1 ≤ w x)
    (f : WeightedL2 H w μ) :
    embed hw hw1 f ∈ GW.Analysis.multiplierDomain (fun x => (w x : ℂ)) μ :=
  ⟨coordinates f, weighted_embed_ae hw hw1 f⟩

lemma embed_injective (hw : Measurable w) (hw1 : ∀ x, 1 ≤ w x) :
    Function.Injective (embed (H := H) (μ := μ) hw hw1) := by
  intro f g h
  apply (coordinates (w := w) (μ := μ)).injective
  apply Lp.ext
  filter_upwards [weighted_embed_ae hw hw1 f, weighted_embed_ae hw hw1 g] with x hf hg
  rw [← hf, ← hg, h]

/-- The inverse coordinate of u is wu, with both domain and value witnesses. -/
lemma embed_range (hw : Measurable w) (hw1 : ∀ x, 1 ≤ w x) :
    Set.range (embed (H := H) hw hw1) =
      (GW.Analysis.multiplierDomain (E := H) (fun x => (w x : ℂ)) μ : Set (Lp H 2 μ)) := by
  ext u
  constructor
  · rintro ⟨f, rfl⟩
    exact embed_mem_domain hw hw1 f
  · intro hu
    let f := GW.Analysis.multiplierValue (fun x => (w x : ℂ)) ⟨u, hu⟩
    refine ⟨coordinates.symm f, ?_⟩
    apply Lp.ext
    filter_upwards [embed_ae hw hw1 (coordinates.symm f),
      GW.Analysis.multiplierValue_ae (fun x => (w x : ℂ)) ⟨u, hu⟩] with x hx hy
    change (((w x)⁻¹ : ℝ) : ℂ) • f x = _ at hx
    rw [← hx, ← hy, smul_smul]
    have hne : w x ≠ 0 := ne_of_gt (zero_lt_one.trans_le (hw1 x))
    simp [hne]

/-- The weighted norm identity is an exact identity in the chosen complete carrier. -/
lemma weighted_norm_embed (hw : Measurable w) (hw1 : ∀ x, 1 ≤ w x)
    (f : WeightedL2 H w μ) :
    ‖GW.Analysis.multiplierValue (fun x => (w x : ℂ))
      ⟨embed hw hw1 f, embed_mem_domain hw hw1 f⟩‖ = ‖f‖ := by
  have heq : GW.Analysis.multiplierValue (fun x => (w x : ℂ))
      ⟨embed hw hw1 f, embed_mem_domain hw hw1 f⟩ = coordinates f := by
    apply Lp.ext
    exact (GW.Analysis.multiplierValue_ae _ _).symm.trans (weighted_embed_ae hw hw1 f)
  rw [heq, LinearIsometryEquiv.norm_map]

/-- Measurable indicator multiplication on the coordinate carrier. -/
def cutoff (s : Set X) (hs : MeasurableSet s) :
    WeightedL2 H w μ →L[ℂ] WeightedL2 H w μ :=
  GW.Analysis.boundedMultiplier (s.indicator (fun _ => (1 : ℂ)))
    (measurable_const.indicator hs) (C := 1)
    (Eventually.of_forall (fun x => by
      by_cases hx : x ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]))

lemma cutoff_ae (s : Set X) (hs : MeasurableSet s) (f : WeightedL2 H w μ) :
    s.indicator (coordinates f : X → H) =ᵐ[μ] coordinates (cutoff s hs f) := by
  have h := GW.Analysis.boundedMultiplier_ae (s.indicator (fun _ => (1 : ℂ)))
    (measurable_const.indicator hs)
    (C := 1) (Eventually.of_forall (fun x => by
      by_cases hx : x ∈ s <;> simp [hx])) (coordinates f)
  change s.indicator (coordinates f : X → H) =ᵐ[μ] _
  convert h using 1
  · ext x
    by_cases hx : x ∈ s <;> simp [hx]
  · rfl

/-- DCT on the weighted coordinate, as specified in the manuscript.
Eventual pointwise inclusion includes every increasing exhausting cutoff. -/
lemma cutoff_tendsto (s : ℕ → Set X) (hs : ∀ n, MeasurableSet (s n))
    (hex : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, x ∈ s n) (f : WeightedL2 H w μ) :
    Tendsto (fun n => cutoff (s n) (hs n) f) atTop (𝓝 f) := by
  obtain ⟨hf, hg, ht⟩ := GW.Analysis.dominated_l2_convergence (𝕜 := ℂ)
    (fun n => (Lp.memLp (coordinates f)).aestronglyMeasurable.indicator (hs n))
    (hex.mono (fun x hx => tendsto_const_nhds.congr' (hx.mono (fun n hn =>
      (Set.indicator_of_mem hn _).symm))))
    (Lp.stronglyMeasurable (coordinates f)).norm.measurable
    ((memLp_two_iff_integrable_sq_norm (Lp.memLp (coordinates f)).aestronglyMeasurable).mp (Lp.memLp _))
    (fun n => Eventually.of_forall (fun x => norm_indicator_le_norm_self _ _))
  have heq (n : ℕ) : (hf n).toLp _ = coordinates (cutoff (s n) (hs n) f) := by
    apply Lp.ext
    exact (hf n).coeFn_toLp.trans (cutoff_ae _ _ f)
  have heqf : hg.toLp _ = coordinates f := Lp.toLp_coeFn _ _
  simp only [heq, heqf] at ht
  exact tendsto_iff_norm_sub_tendsto_zero.mpr ht

/-- A bounded-weight cutoff of any ambient vector lies in the weighted domain. -/
lemma cutoff_mem_domain (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) {R : ℝ} (hR : 0 ≤ R) (u : Lp H 2 μ) :
    cutoff (w := w) {x | w x ≤ R} (measurableSet_le hw measurable_const) u ∈
      GW.Analysis.multiplierDomain (fun x => (w x : ℂ)) μ := by
  apply (GW.Analysis.mem_multiplierDomain_iff _ _).mpr
  have hm : MemLp (fun x => (w x : ℂ) • ({x | w x ≤ R}.indicator (u : X → H) x)) 2 μ := by
    apply (Lp.memLp u).of_le_mul (c := R)
      ((Complex.continuous_ofReal.measurable.comp hw).aestronglyMeasurable.smul
        ((Lp.memLp u).aestronglyMeasurable.indicator (measurableSet_le hw measurable_const)))
    apply Eventually.of_forall
    intro x
    change ‖(w x : ℂ) • ({x | w x ≤ R}.indicator (u : X → H) x)‖ ≤ R * ‖u x‖
    by_cases hx : w x ≤ R
    · simp only [Set.indicator, Set.mem_ofPred_eq, ite_eq_left hx, norm_smul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (by rwa [abs_of_nonneg (hw0 x)]) (norm_nonneg _)
    · simp only [Set.indicator, Set.mem_ofPred_eq, ite_eq_right hx, smul_zero, norm_zero]
      positivity
  apply hm.ae_eq
  filter_upwards [cutoff_ae {x | w x ≤ R} (measurableSet_le hw measurable_const) u] with x hx
  change (w x : ℂ) • ({x | w x ≤ R}.indicator (coordinates (w := w) u : X → H) x) =
    (w x : ℂ) • coordinates (cutoff (w := w) {x | w x ≤ R}
      (measurableSet_le hw measurable_const) u) x
  exact congrArg (fun z : H => (w x : ℂ) • z) hx

lemma weight_cutoff_tendsto (hw : Measurable w) (f : WeightedL2 H w μ) :
    Tendsto (fun n : ℕ => cutoff {x | w x ≤ (n : ℝ)}
      (measurableSet_le hw measurable_const) f) atTop (𝓝 f) := by
  apply cutoff_tendsto
  exact Eventually.of_forall (fun x =>
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (w x)))

/-- Density in ambient L² is proved with bounded-weight cutoffs. -/
lemma embed_denseRange (hw : Measurable w) (hw1 : ∀ x, 1 ≤ w x) :
    DenseRange (embed (H := H) (μ := μ) hw hw1) := by
  intro u
  apply mem_closure_of_tendsto (weight_cutoff_tendsto hw u)
  apply Eventually.of_forall
  intro n
  rw [embed_range hw hw1]
  exact cutoff_mem_domain hw (fun x => le_trans zero_le_one (hw1 x)) (Nat.cast_nonneg n) u

/-- Full real-parameter convergence follows along every sequence tending to infinity. -/
lemma weight_cutoff_tendsto_real (hw : Measurable w) (f : WeightedL2 H w μ) :
    Tendsto (fun R : ℝ => cutoff {x | w x ≤ R}
      (measurableSet_le hw measurable_const) f) atTop (𝓝 f) := by
  apply Filter.tendsto_iff_seq_tendsto.mpr
  intro Rs hRs
  apply cutoff_tendsto
  exact Eventually.of_forall (fun x => hRs.eventually (eventually_ge_atTop (w x)))

lemma clipped_bound (hw0 : ∀ x, 0 ≤ w x) {R : ℝ} (hR : 0 ≤ R) :
    ∀ᵐ x ∂μ, ‖((min (w x) R : ℝ) : ℂ)‖ ≤ R := by
  apply Eventually.of_forall
  intro x
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_min (hw0 x) hR)]
  exact min_le_right _ _

/-- The bounded clipped-weight map used in the Fatou test. -/
def clipped (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) {R : ℝ} (hR : 0 ≤ R) :
    Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  GW.Analysis.boundedMultiplier (fun x => ((min (w x) R : ℝ) : ℂ))
    (Complex.continuous_ofReal.measurable.comp (hw.min measurable_const)) (clipped_bound hw0 hR)

lemma clipped_ae (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) {R : ℝ} (hR : 0 ≤ R)
    (u : Lp H 2 μ) :
    (fun x => ((min (w x) R : ℝ) : ℂ) • u x) =ᵐ[μ] clipped hw hw0 hR u :=
  GW.Analysis.boundedMultiplier_ae _ _ _ _

lemma clipped_embed_norm_le (hw : Measurable w) (hw1 : ∀ x, 1 ≤ w x)
    {R : ℝ} (hR : 0 ≤ R) (f : WeightedL2 H w μ) :
    ‖clipped hw (fun x => le_trans zero_le_one (hw1 x)) hR (embed hw hw1 f)‖ ≤ ‖f‖ := by
  rw [← LinearIsometryEquiv.norm_map (coordinates (w := w) (μ := μ)) f]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [clipped_ae hw (fun x => le_trans zero_le_one (hw1 x)) hR
    (embed hw hw1 f), weighted_embed_ae hw hw1 f] with x hc hwf
  rw [← hc, ← hwf, norm_smul, norm_smul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (le_min (le_trans zero_le_one (hw1 x)) hR),
    abs_of_nonneg (le_trans zero_le_one (hw1 x))]
  exact mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _)

/-- Norm continuity for each fixed bounded clipped multiplier. -/
lemma clipped_limit_bound (hw : Measurable w) (hw1 : ∀ x, 1 ≤ w x)
    (fs : ℕ → WeightedL2 H w μ) {u : Lp H 2 μ} {C : ℝ}
    (hu : Tendsto (fun n => embed hw hw1 (fs n)) atTop (𝓝 u))
    (hb : ∀ n, ‖fs n‖ ≤ C) {R : ℝ} (hR : 0 ≤ R) :
    ‖clipped hw (fun x => le_trans zero_le_one (hw1 x)) hR u‖ ≤ C := by
  apply le_of_tendsto (((clipped hw (fun x => le_trans zero_le_one (hw1 x)) hR).continuous.tendsto u).comp hu).norm
  exact Eventually.of_forall (fun n => (clipped_embed_norm_le hw hw1 hR (fs n)).trans (hb n))

/-- Monotone convergence of the squared clipped integrands gives actual membership.
This is the manuscript's Fatou step, without subsequence extraction. -/
lemma mem_domain_of_clipped_bounds (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    (u : Lp H 2 μ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n : ℕ, ‖clipped hw hw0 (Nat.cast_nonneg n) u‖ ≤ C) :
    ∃ hu : u ∈ GW.Analysis.multiplierDomain (fun x => (w x : ℂ)) μ,
      ‖GW.Analysis.multiplierValue (fun x => (w x : ℂ)) ⟨u, hu⟩‖ ≤ C := by
  let q : ℕ → X → ℝ := fun n x => ‖((min (w x) (n : ℝ) : ℝ) : ℂ) • u x‖ ^ 2
  let Q : X → ℝ := fun x => ‖(w x : ℂ) • u x‖ ^ 2
  have hqm (n : ℕ) : AEStronglyMeasurable (fun x => ((min (w x) (n : ℝ) : ℝ) : ℂ) • u x) μ :=
    (Complex.continuous_ofReal.measurable.comp (hw.min measurable_const)).aestronglyMeasurable.smul
      (Lp.memLp u).aestronglyMeasurable
  have hqLp (n : ℕ) : MemLp (fun x => ((min (w x) (n : ℝ) : ℝ) : ℂ) • u x) 2 μ :=
    (GW.Analysis.mem_multiplierDomain_iff _ u).mp
      (GW.Analysis.mem_multiplierDomain_of_bound _
        (Complex.continuous_ofReal.measurable.comp (hw.min measurable_const))
        (clipped_bound hw0 (Nat.cast_nonneg n)) u)
  have hqi (n : ℕ) : Integrable (q n) μ :=
    (memLp_two_iff_integrable_sq_norm (hqm n)).mp (hqLp n)
  have hqn (n : ℕ) : ∫ x, q n x ∂μ = ‖clipped hw hw0 (Nat.cast_nonneg n) u‖ ^ 2 := by
    rw [GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
    apply integral_congr_ae
    exact (clipped_ae hw hw0 (Nat.cast_nonneg n) u).mono (fun x hx => congrArg (fun z : H => ‖z‖ ^ 2) hx)
  have hmono : ∀ᵐ x ∂μ, Monotone (fun n => ENNReal.ofReal (q n x)) := by
    apply Eventually.of_forall
    intro x n m hnm
    apply ENNReal.ofReal_le_ofReal
    dsimp [q]
    simp only [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (le_min (hw0 x) (Nat.cast_nonneg _))]
    have hmin : min (w x) (n : ℝ) ≤ min (w x) (m : ℝ) := min_le_min_left _ (Nat.cast_le.mpr hnm)
    have hp := mul_le_mul_of_nonneg_right hmin (norm_nonneg (u x))
    exact pow_le_pow_left₀ (mul_nonneg (le_min (hw0 x) (Nat.cast_nonneg n)) (norm_nonneg _)) hp 2
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => ENNReal.ofReal (q n x)) atTop (𝓝 (ENNReal.ofReal (Q x))) := by
    apply Eventually.of_forall
    intro x
    apply tendsto_const_nhds.congr'
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (w x))] with n hn
    simp [q, Q, min_eq_left hn]
  have ht := lintegral_tendsto_of_tendsto_of_monotone
    (fun n => (hqi n).aemeasurable.ennreal_ofReal) hmono hlim
  have he : (∫⁻ x, ENNReal.ofReal (Q x) ∂μ) ≤ ENNReal.ofReal (C ^ 2) := by
    apply le_of_tendsto ht
    apply Eventually.of_forall
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hqi n)
      (Eventually.of_forall (fun x => sq_nonneg _)), hqn]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hb n) 2)
  have hQm : AEStronglyMeasurable (fun x => (w x : ℂ) • u x) μ :=
    (Complex.continuous_ofReal.measurable.comp hw).aestronglyMeasurable.smul
      (Lp.memLp u).aestronglyMeasurable
  have hQi : Integrable Q μ := ⟨hQm.norm.pow 2,
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun x => sq_nonneg _))).mpr
      (he.trans_lt (ENNReal.ofReal_lt_top))⟩
  have hu := (GW.Analysis.mem_multiplierDomain_iff (fun x => (w x : ℂ)) u).mpr
    ((memLp_two_iff_integrable_sq_norm hQm).mpr hQi)
  refine ⟨hu, ?_⟩
  have hnorm : ‖GW.Analysis.multiplierValue (fun x => (w x : ℂ)) ⟨u, hu⟩‖ ^ 2 = ∫ x, Q x ∂μ := by
    rw [GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
    apply integral_congr_ae
    exact (GW.Analysis.multiplierValue_ae (fun x => (w x : ℂ)) ⟨u, hu⟩).symm.mono
      (fun x hx => congrArg (fun z : H => ‖z‖ ^ 2) hx)
  rw [← ofReal_integral_eq_lintegral_ofReal hQi
    (Eventually.of_forall (fun x => sq_nonneg _))] at he
  have hsq : (∫ x, Q x ∂μ) ≤ C ^ 2 := (ENNReal.ofReal_le_ofReal_iff (sq_nonneg C)).mp he
  nlinarith [norm_nonneg (GW.Analysis.multiplierValue (fun x => (w x : ℂ)) ⟨u, hu⟩)]

/-- The source Fatou domain test in reciprocal-coordinate form. -/
lemma fatou_domain (hw : Measurable w) (hw1 : ∀ x, 1 ≤ w x)
    (fs : ℕ → WeightedL2 H w μ) {u : Lp H 2 μ} {C : ℝ}
    (hu : Tendsto (fun n => embed hw hw1 (fs n)) atTop (𝓝 u))
    (hb : ∀ n, ‖fs n‖ ≤ C) :
    ∃ f : WeightedL2 H w μ, embed hw hw1 f = u ∧ ‖f‖ ≤ C := by
  have hC : 0 ≤ C := (norm_nonneg (fs 0)).trans (hb 0)
  obtain ⟨hud, hbound⟩ := mem_domain_of_clipped_bounds hw
    (fun x => le_trans zero_le_one (hw1 x)) u hC
    (fun n => clipped_limit_bound hw hw1 fs hu hb (Nat.cast_nonneg n))
  obtain ⟨f, hf⟩ := (show u ∈ Set.range (embed (H := H) hw hw1) from by
    rw [embed_range hw hw1]; exact hud)
  refine ⟨f, hf, ?_⟩
  have he : GW.Analysis.multiplierValue (fun x => (w x : ℂ)) ⟨u, hud⟩ = coordinates f := by
    apply Lp.ext
    have hemb := weighted_embed_ae hw hw1 f
    rw [hf] at hemb
    exact (GW.Analysis.multiplierValue_ae _ _).symm.trans hemb
  simpa only [he, LinearIsometryEquiv.norm_map] using hbound

/-- Ambient classes whose representatives vanish above some bounded weight level. -/
def boundedWeight (w : X → ℝ) (μ : Measure X) : Submodule ℂ (Lp H 2 μ) where
  carrier := {u | ∃ R : ℝ, ∀ᵐ x ∂μ, R < w x → u x = 0}
  zero_mem' := by
    refine ⟨0, ?_⟩
    filter_upwards [Lp.coeFn_zero (E := H) (p := 2) (μ := μ)] with x hx
    exact fun _ => hx
  add_mem' := by
    rintro u v ⟨R, hR⟩ ⟨S, hS⟩
    refine ⟨max R S, ?_⟩
    filter_upwards [hR, hS, Lp.coeFn_add u v] with x hx hy ha
    intro h
    simpa [Pi.add_apply, hx ((le_max_left R S).trans_lt h),
      hy ((le_max_right R S).trans_lt h)] using ha
  smul_mem' := by
    rintro c u ⟨R, hR⟩
    refine ⟨R, ?_⟩
    filter_upwards [hR, Lp.coeFn_smul c u] with x hx hs
    intro h
    simpa [Pi.smul_apply, hx h] using hs

/-- The bounded-weight subspace in the complete weighted carrier is dense. -/
lemma boundedWeight_dense (hw : Measurable w) :
    Dense ((coordinates (w := w) (μ := μ)) ⁻¹'
      (↑(boundedWeight (H := H) w μ) : Set (Lp H 2 μ))) := by
  intro f
  apply mem_closure_of_tendsto (weight_cutoff_tendsto hw f)
  apply Eventually.of_forall
  intro n
  refine ⟨(n : ℝ), ?_⟩
  filter_upwards [cutoff_ae {x | w x ≤ (n : ℝ)}
    (measurableSet_le hw measurable_const) f] with x hx
  intro hn
  rw [← hx]
  exact Set.indicator_of_notMem (not_le.mpr hn) _

/-- Coordinate cutoffs represent the same physical indicator multiplication. -/
lemma embed_cutoff_ae (hw : Measurable w) (hw1 : ∀ x, 1 ≤ w x)
    (s : Set X) (hs : MeasurableSet s) (f : WeightedL2 H w μ) :
    s.indicator (embed hw hw1 f : X → H) =ᵐ[μ] embed hw hw1 (cutoff s hs f) := by
  filter_upwards [embed_ae hw hw1 f, embed_ae hw hw1 (cutoff s hs f),
    cutoff_ae s hs f] with x hf hc hsx
  rw [← hc, ← hsx]
  by_cases hx : x ∈ s
  · simp only [Set.indicator_of_mem hx]
    exact hf.symm
  · simp only [Set.indicator_of_notMem hx, smul_zero]

/-- Arbitrary exhausting real cutoffs converge in the weighted norm, via sequences. -/
lemma cutoff_tendsto_real (s : ℝ → Set X) (hs : ∀ R, MeasurableSet (s R))
    (hex : ∀ᵐ x ∂μ, ∀ᶠ R in atTop, x ∈ s R) (f : WeightedL2 H w μ) :
    Tendsto (fun R => cutoff (s R) (hs R) f) atTop (𝓝 f) := by
  apply Filter.tendsto_iff_seq_tendsto.mpr
  intro Rs hRs
  apply cutoff_tendsto
  exact hex.mono (fun x hx => hRs.eventually hx)

omit [MeasurableSpace X] in
lemma indicator_eventually_mem {ι : Type*} {l : Filter ι} {s : ι → Set X} {x : X}
    (hx : Tendsto (fun i => (s i).indicator (fun _ => (1 : ℝ)) x) l (𝓝 1)) :
    ∀ᶠ i in l, x ∈ s i := by
  have he := hx.eventually (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  exact he.mono (fun i hi => by
    by_contra hn
    simp only [Set.indicator_of_notMem hn, lt_self_iff_false] at hi)

/-- In particular this covers the manuscript's increasing indicator cutoffs. -/
lemma cutoff_tendsto_of_indicator (s : ℕ → Set X) (hs : ∀ n, MeasurableSet (s n))
    (hl : ∀ᵐ x ∂μ, Tendsto (fun n => (s n).indicator (fun _ => (1 : ℝ)) x) atTop (𝓝 1))
    (f : WeightedL2 H w μ) :
    Tendsto (fun n => cutoff (s n) (hs n) f) atTop (𝓝 f) :=
  cutoff_tendsto s hs (hl.mono (fun _ hx => indicator_eventually_mem hx)) f

lemma cutoff_tendsto_real_of_indicator (s : ℝ → Set X) (hs : ∀ R, MeasurableSet (s R))
    (hl : ∀ᵐ x ∂μ, Tendsto (fun R => (s R).indicator (fun _ => (1 : ℝ)) x) atTop (𝓝 1))
    (f : WeightedL2 H w μ) :
    Tendsto (fun R => cutoff (s R) (hs R) f) atTop (𝓝 f) :=
  cutoff_tendsto_real s hs (hl.mono (fun _ hx => indicator_eventually_mem hx)) f

end WeightedL2
end GW.Spaces
