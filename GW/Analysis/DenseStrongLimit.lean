module
public import GW.Analysis.MixedForms
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.UniformSpace.UniformApproximation
public import Mathlib.Topology.Sequences
/-! Source basic:dense-strong-limit. Uniform Cauchy estimates from density,
bounded pointwise linear limits, compact-wise continuity and strong products. -/
@[expose] public section
noncomputable section
open Filter
open scoped Topology
namespace GW.Analysis
variable {E F G P : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma dense_strong_difference_bound (A B : E →L[ℂ] F) {M : ℝ}
    (hA : ‖A‖ ≤ M) (hB : ‖B‖ ≤ M) (u v : E) :
    ‖A u - B u‖ ≤ 2 * M * ‖u-v‖ + ‖A v - B v‖ := by
  have heq : A u - B u = (A (u-v) - B (u-v)) + (A v - B v) := by
    simp only [map_sub]
    abel
  have ha := (A.le_opNorm (u-v)).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  have hb := (B.le_opNorm (u-v)).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
  rw [heq]
  have ht := (norm_add_le (A (u-v)-B (u-v)) (A v-B v)).trans
    (add_le_add (norm_sub_le (A (u-v)) (B (u-v))) le_rfl)
  linarith

lemma uniform_cauchy_on_dense (Ts : ℕ → P → E →L[ℂ] F)
    (D : Submodule ℂ E) (hD : Dense (D : Set E)) (I : Set P) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ n, ∀ t ∈ I, ‖Ts n t‖ ≤ M)
    (hc : ∀ v : D, UniformCauchySeqOn (fun n t => Ts n t v) atTop I) (u : E) :
    UniformCauchySeqOn (fun n t => Ts n t u) atTop I := by
  apply Metric.uniformCauchySeqOn_iff.mpr
  intro ε hε
  let δ := ε / (4 * (M+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have heq : 4*(M+1)*δ = ε := by dsimp [δ]; field_simp
  obtain ⟨v, hv, huv⟩ := Metric.mem_closure_iff.mp (hD u) δ hδ
  rw [dist_eq_norm] at huv
  obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.mp (hc ⟨v,hv⟩) (ε/2) (by positivity)
  refine ⟨N, fun m hm n hn t ht => ?_⟩
  have hsmall := hN m hm n hn t ht
  rw [dist_eq_norm] at hsmall ⊢
  have hbound := dense_strong_difference_bound (Ts m t) (Ts n t) (hb m t ht) (hb n t ht) u v
  have hδmul := mul_lt_mul_of_pos_left huv (show 0 < 2*(M+1) by positivity)
  nlinarith [norm_nonneg (u-v)]

/-- Linearity and the common norm bound pass to a pointwise limit. -/
def strongLimitMap (Ts : ℕ → E →L[ℂ] F) (f : E → F)
    (hf : ∀ u, Tendsto (fun n => Ts n u) atTop (𝓝 (f u))) {M : ℝ}
    (hb : ∀ n, ‖Ts n‖ ≤ M) : E →L[ℂ] F := by
  let L : E →ₗ[ℂ] F :=
    { toFun := f
      map_add' u v := by
        apply tendsto_nhds_unique (hf (u+v))
        simpa only [map_add] using (hf u).add (hf v)
      map_smul' c u := by
        apply tendsto_nhds_unique (hf (c • u))
        simpa only [map_smul, RingHom.id_apply] using (hf u).const_smul c }
  apply L.mkContinuous M
  intro u
  apply le_of_tendsto (hf u).norm
  exact Eventually.of_forall (fun n => (Ts n |>.le_opNorm u).trans
    (mul_le_mul_of_nonneg_right (hb n) (norm_nonneg u)))

lemma strongLimitMap_apply (Ts : ℕ → E →L[ℂ] F) (f : E → F)
    (hf : ∀ u, Tendsto (fun n => Ts n u) atTop (𝓝 (f u))) {M : ℝ}
    (hb : ∀ n, ‖Ts n‖ ≤ M) (u : E) : strongLimitMap Ts f hf hb u = f u := rfl

section Complete
variable [CompleteSpace F] [TopologicalSpace P]

/-- The compact-wise uniform Cauchy limits reconstruct a single bounded linear family. -/
lemma dense_strong_limit (Ts : ℕ → P → E →L[ℂ] F)
    (D : Submodule ℂ E) (hD : Dense (D : Set E)) (M : Set P → ℝ)
    (hM : ∀ I, IsCompact I → 0 ≤ M I)
    (hb : ∀ I, IsCompact I → ∀ n, ∀ t ∈ I, ‖Ts n t‖ ≤ M I)
    (hc : ∀ I, IsCompact I → ∀ v : D, UniformCauchySeqOn (fun n t => Ts n t v) atTop I) :
    ∃ T : P → E →L[ℂ] F,
      (∀ t u, Tendsto (fun n => Ts n t u) atTop (𝓝 (T t u))) ∧
      (∀ I, IsCompact I → ∀ u, TendstoUniformlyOn (fun n t => Ts n t u)
        (fun t => T t u) atTop I) ∧
      (∀ I, IsCompact I → ∀ t ∈ I, ‖T t‖ ≤ M I) := by
  have hp (t : P) (u : E) : ∃ v : F, Tendsto (fun n => Ts n t u) atTop (𝓝 v) := by
    apply cauchySeq_tendsto_of_complete
    exact (uniform_cauchy_on_dense Ts D hD {t} (hM _ isCompact_singleton)
      (hb _ isCompact_singleton) (hc _ isCompact_singleton) u).cauchySeq (Set.mem_singleton t)
  choose f hf using hp
  let T (t : P) : E →L[ℂ] F := strongLimitMap (fun n => Ts n t) (f t) (hf t)
    (fun n => hb {t} isCompact_singleton n t (Set.mem_singleton t))
  have hT (t : P) (u : E) : Tendsto (fun n => Ts n t u) atTop (𝓝 (T t u)) := hf t u
  refine ⟨T, hT, ?_, ?_⟩
  · intro I hI u
    exact (uniform_cauchy_on_dense Ts D hD I (hM I hI) (hb I hI) (hc I hI) u).tendstoUniformlyOn_of_tendsto
      (fun t _ => hT t u)
  · intro I hI t ht
    apply (T t).opNorm_le_bound (hM I hI)
    intro u
    apply le_of_tendsto (hT t u).norm
    exact Eventually.of_forall (fun n => (Ts n t |>.le_opNorm u).trans
      (mul_le_mul_of_nonneg_right (hb I hI n t ht) (norm_nonneg u)))
/-- Source version with arbitrary finite compact bounds, including empty sets.
Nonnegativity is needed only internally and follows at every parameter present. -/
lemma dense_strong_limit_of_bound (Ts : ℕ → P → E →L[ℂ] F)
    (D : Submodule ℂ E) (hD : Dense (D : Set E)) (M : Set P → ℝ)
    (hb : ∀ I, IsCompact I → ∀ n, ∀ t ∈ I, ‖Ts n t‖ ≤ M I)
    (hc : ∀ I, IsCompact I → ∀ v : D, UniformCauchySeqOn (fun n t => Ts n t v) atTop I) :
    ∃ T : P → E →L[ℂ] F,
      (∀ t u, Tendsto (fun n => Ts n t u) atTop (𝓝 (T t u))) ∧
      (∀ I, IsCompact I → ∀ u, TendstoUniformlyOn (fun n t => Ts n t u)
        (fun t => T t u) atTop I) ∧
      (∀ I, IsCompact I → ∀ t ∈ I, ‖T t‖ ≤ M I) := by
  obtain ⟨T, hT, hU, _⟩ := dense_strong_limit Ts D hD (fun I => max 0 (M I))
    (fun _ _ => le_max_left _ _)
    (fun I hI n t ht => (hb I hI n t ht).trans (le_max_right _ _)) hc
  refine ⟨T, hT, hU, ?_⟩
  intro I hI t ht
  apply (T t).opNorm_le_bound ((norm_nonneg (Ts 0 t)).trans (hb I hI 0 t ht))
  intro u
  apply le_of_tendsto (hT t u).norm
  exact Eventually.of_forall (fun n => (Ts n t |>.le_opNorm u).trans
    (mul_le_mul_of_nonneg_right (hb I hI n t ht) (norm_nonneg u)))

end Complete

section Orbits
variable [PseudoMetricSpace P]

/-- Continuity is checked on the compact set consisting of a convergent sequence
and its limit, exactly as in the manuscript. -/
lemma strong_limit_orbit_continuous (Ts : ℕ → P → E →L[ℂ] F) (T : P → E →L[ℂ] F)
    (hlim : ∀ I, IsCompact I → ∀ u, TendstoUniformlyOn (fun n t => Ts n t u)
      (fun t => T t u) atTop I)
    (hc : ∀ n u, Continuous (fun t => Ts n t u)) (u : E) :
    Continuous (fun t => T t u) := by
  apply SeqContinuous.continuous
  intro ts t hts
  let K := insert t (Set.range ts)
  have hK : IsCompact K := hts.isCompact_insert_range
  have hcont : ContinuousOn (fun t => T t u) K :=
    (hlim K hK u).continuousOn (Eventually.of_forall (fun n => (hc n u).continuousOn)).frequently
  have ht : t ∈ K := Set.mem_insert t _
  have hseq : Tendsto ts atTop (𝓝[K] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨hts, Eventually.of_forall (fun n =>
      Set.mem_insert_of_mem t (Set.mem_range_self n))⟩
  exact (hcont t ht).tendsto.comp hseq
end Orbits

variable [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- The fixed-parameter product limit uses a bound on T_n only. -/
lemma strong_product_limit {Ts : ℕ → E →L[ℂ] F} {T : E →L[ℂ] F}
    {Ss : ℕ → G →L[ℂ] E} {S : G →L[ℂ] E} {M : ℝ}
    (hb : ∀ n, ‖Ts n‖ ≤ M)
    (hT : ∀ v, Tendsto (fun n => Ts n v) atTop (𝓝 (T v)))
    (hS : ∀ u, Tendsto (fun n => Ss n u) atTop (𝓝 (S u))) (u : G) :
    Tendsto (fun n => Ts n (Ss n u)) atTop (𝓝 (T (S u))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have he : Tendsto (fun n => ‖Ss n u - S u‖) atTop (𝓝 0) := by
    simpa using ((hS u).sub_const (S u)).norm
  have hf : Tendsto (fun n => ‖Ts n (S u) - T (S u)‖) atTop (𝓝 0) := by
    simpa using ((hT (S u)).sub_const (T (S u))).norm
  have hlim : Tendsto (fun n => M * ‖Ss n u-S u‖ + ‖Ts n (S u)-T (S u)‖) atTop (𝓝 0) := by
    simpa using (he.const_mul M).add hf
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
  have heq : Ts n (Ss n u) - T (S u) = Ts n (Ss n u-S u) + (Ts n (S u)-T (S u)) := by
    simp only [map_sub]
    abel
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add
    ((Ts n).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_right (hb n) (norm_nonneg _))) le_rfl)
end GW.Analysis
