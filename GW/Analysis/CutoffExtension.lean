module

public import GW.Conventions
public import Mathlib.Analysis.Normed.Operator.CompleteCodomain
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Tactic

/-! Source bridge:cutoff-extension. The cofinal sequence constructs the
limit; the original uniform estimate proves convergence for all real cutoffs. -/
@[expose] public section
noncomputable section
open Filter
open scoped Topology
namespace GW.Analysis
variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]

lemma cutoff_sequence_tendsto (t₀ : ℝ) :
    Tendsto (fun n : ℕ => t₀ + (n : ℝ)) atTop atTop :=
  tendsto_atTop_add_const_left _ t₀ tendsto_natCast_atTop_atTop

/-- The uniform Cauchy estimate produces a unique bounded map with the same error. -/
lemma cutoff_extension (B : ℝ → X →L[𝕜] Y) (t₀ : ℝ) (ε : ℝ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0))
    (hB : ∀ L ≥ t₀, ∀ t ≥ L, ∀ ν ≥ L, ‖B t - B ν‖ ≤ ε L) :
    ∃! T : X →L[𝕜] Y, ∀ L ≥ t₀, ∀ t ≥ L, ‖B t - T‖ ≤ ε L := by
  have hseq := cutoff_sequence_tendsto t₀
  have hc : CauchySeq (fun n : ℕ => B (t₀ + n)) := by
    apply Metric.cauchySeq_iff.mpr
    intro δ hδ
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hε.comp hseq) δ hδ
    have hNδ : |ε (t₀ + N)| < δ := by simpa [Real.dist_eq] using hN N le_rfl
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm]
    apply (hB (t₀ + N) (le_add_of_nonneg_right (Nat.cast_nonneg N)) (t₀ + m) ?_ (t₀ + n) ?_).trans_lt
    · exact (le_abs_self (ε (t₀ + N))).trans_lt hNδ
    · linarith [show (N : ℝ) ≤ (m : ℝ) from Nat.cast_le.mpr hm]
    · linarith [show (N : ℝ) ≤ (n : ℝ) from Nat.cast_le.mpr hn]
  obtain ⟨T, hT⟩ := cauchySeq_tendsto_of_complete hc
  have hbT : ∀ L ≥ t₀, ∀ t ≥ L, ‖B t - T‖ ≤ ε L := by
    intro L hL t ht
    apply le_of_tendsto ((tendsto_const_nhds.sub hT).norm)
    filter_upwards [hseq.eventually (eventually_ge_atTop L)] with n hn
    exact hB L hL t ht (t₀ + n) hn
  refine ⟨T, hbT, ?_⟩
  intro S hS
  have hST : ‖S - T‖ = 0 := by
    apply le_antisymm ?_ (norm_nonneg _)
    have hzero : Tendsto (fun L => 2 * ε L) atTop (𝓝 0) := by
      simpa using hε.const_mul 2
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hzero
    filter_upwards [eventually_ge_atTop t₀] with L hL
    calc
      ‖S - T‖ = ‖(S - B L) + (B L - T)‖ := by congr 1; abel
      _ ≤ ‖S - B L‖ + ‖B L - T‖ := norm_add_le _ _
      _ ≤ ε L + ε L := by
        rw [norm_sub_rev S]
        exact add_le_add (hS L hL L le_rfl) (hbT L hL L le_rfl)
      _ = 2 * ε L := by ring
  exact sub_eq_zero.mp (norm_eq_zero.mp hST)

omit [CompleteSpace Y]

/-- The bound applies beyond each real threshold, not only on the defining sequence. -/
lemma cutoff_extension_tendsto {B : ℝ → X →L[𝕜] Y} {T : X →L[𝕜] Y}
    {t₀ : ℝ} {ε : ℝ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hT : ∀ L ≥ t₀, ∀ t ≥ L, ‖B t - T‖ ≤ ε L) :
    Tendsto B atTop (𝓝 T) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun t => norm_nonneg _)) ?_ hε
  filter_upwards [eventually_ge_atTop t₀] with t ht
  exact hT t ht t le_rfl

/-- Closed graphs retain both coordinates of a convergent domain sequence. -/
lemma partial_closed_limit {Z : Type*} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    (C : Y →ₗ.[𝕜] Z) (hC : C.IsClosed) {us : ℕ → Y} {u : Y} {z : Z}
    (hu : ∀ n, us n ∈ C.domain)
    (hul : Tendsto us atTop (𝓝 u))
    (hvl : Tendsto (fun n => C ⟨us n, hu n⟩) atTop (𝓝 z)) :
    ∃ h : u ∈ C.domain, C ⟨u, h⟩ = z := by
  have hm : (u, z) ∈ C.graph := hC.mem_of_tendsto (hul.prodMk_nhds hvl)
    (Eventually.of_forall (fun n => C.mem_graph ⟨us n, hu n⟩))
  obtain ⟨v, hv, hvz⟩ := C.mem_graph_iff.mp hm
  change (v : Y) = u at hv
  have hmem : u ∈ C.domain := by rw [← hv]; exact v.property
  refine ⟨hmem, ?_⟩
  have he : (⟨u, hmem⟩ : C.domain) = v := Subtype.ext hv.symm
  rw [he]
  exact hvz

/-- Application to the very cofinal sequence used in the cutoff construction. -/
lemma cutoff_limit_in_closed_domain {Z : Type*} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    {B : ℝ → X →L[𝕜] Y} {T : X →L[𝕜] Y} {t₀ : ℝ} {ε : ℝ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0))
    (hT : ∀ L ≥ t₀, ∀ t ≥ L, ‖B t - T‖ ≤ ε L)
    (C : Y →ₗ.[𝕜] Z) (hC : C.IsClosed) (x : X) {z : Z}
    (hu : ∀ n : ℕ, B (t₀ + n) x ∈ C.domain)
    (hv : Tendsto (fun n : ℕ => C ⟨B (t₀ + n) x, hu n⟩) atTop (𝓝 z)) :
    ∃ h : T x ∈ C.domain, C ⟨T x, h⟩ = z := by
  apply partial_closed_limit C hC hu ?_ hv
  exact ((ContinuousLinearMap.apply 𝕜 Y x).continuous.tendsto T).comp
    ((cutoff_extension_tendsto hε hT).comp (cutoff_sequence_tendsto t₀))

/-- Full real-parameter image convergence supplies the cofinal graph limit. -/
lemma cutoff_limit_in_closed_domain_real {Z : Type*} [NormedAddCommGroup Z]
    [NormedSpace 𝕜 Z] {B : ℝ → X →L[𝕜] Y} {T : X →L[𝕜] Y}
    {t₀ : ℝ} {ε : ℝ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hT : ∀ L ≥ t₀, ∀ t ≥ L, ‖B t - T‖ ≤ ε L)
    (C : Y →ₗ.[𝕜] Z) (hC : C.IsClosed) (x : X) {z : Z}
    (hu : ∀ t, t₀ ≤ t → B t x ∈ C.domain)
    (hv : Tendsto (fun t : ℝ => if ht : t₀ ≤ t then C ⟨B t x, hu t ht⟩ else 0)
      atTop (𝓝 z)) :
    ∃ h : T x ∈ C.domain, C ⟨T x, h⟩ = z := by
  have hn : ∀ n : ℕ, t₀ ≤ t₀ + n := fun n =>
    le_add_of_nonneg_right (Nat.cast_nonneg n)
  apply cutoff_limit_in_closed_domain hε hT C hC x (fun n => hu _ (hn n))
  have h := hv.comp (cutoff_sequence_tendsto t₀)
  simpa only [Function.comp_def, dite_eq_left (hn _)] using h

end GW.Analysis
