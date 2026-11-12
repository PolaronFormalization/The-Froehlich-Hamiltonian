module
public import GW.Operators.GraphIntegration
public import GW.Analysis.CutoffExtension
public import GW.Analysis.MixedForms
/-! Source basic:closed-graph-extension. Both graph coordinates converge
before the limit is placed in the actual operator domain. -/
@[expose] public section
noncomputable section
open Filter
open scoped Topology
namespace GW.Operators
variable {X E F G : Type*}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-- The two convergent graph coordinates give membership before evaluating A. -/
lemma closed_graph_extension (J : X →L[ℂ] E) (T : E →L[ℂ] F) (L : X →L[ℂ] G)
    (A : F →ₗ.[ℂ] G) (hA : A.IsClosed) (C : Submodule ℂ X) (hC : Dense (C : Set X))
    (h : ∀ c : C, ∃ hc : T (J c) ∈ A.domain, A ⟨T (J c), hc⟩ = L c) (u : X) :
    ∃ hu : T (J u) ∈ A.domain, A ⟨T (J u), hu⟩ = L u := by
  obtain ⟨cs, hcs, hlim⟩ := mem_closure_iff_seq_limit.mp (hC u)
  have hd (n : ℕ) := (h ⟨cs n, hcs n⟩).choose
  apply GW.Analysis.partial_closed_limit A hA hd
    ((T.continuous.tendsto (J u)).comp ((J.continuous.tendsto u).comp hlim))
  have he (n : ℕ) : A ⟨T (J (cs n)), hd n⟩ = L (cs n) :=
    (h ⟨cs n, hcs n⟩).choose_spec
  simpa only [he, Function.comp_def] using (L.continuous.tendsto u).comp hlim

/-- The extension into the actual Hilbert graph is a bounded linear map. -/
def closed_graph_extension_map (J : X →L[ℂ] E) (T : E →L[ℂ] F) (L : X →L[ℂ] G)
    (A : F →ₗ.[ℂ] G) (hA : A.IsClosed) (C : Submodule ℂ X) (hC : Dense (C : Set X))
    (h : ∀ c : C, ∃ hc : T (J c) ∈ A.domain, A ⟨T (J c), hc⟩ = L c) :
    X →L[ℂ] GraphDomain A hA :=
  (((WithLp.prodContinuousLinearEquiv 2 ℂ F G).symm.toContinuousLinearMap).comp
    ((T.comp J).prod L)).codRestrict (hilbertGraph A hA).toSubmodule (fun u => by
      obtain ⟨hu, he⟩ := closed_graph_extension J T L A hA C hC h u
      exact A.mem_graph_iff.mpr ⟨⟨T (J u), hu⟩, rfl, he⟩)

lemma closed_graph_extension_norm_sq (J : X →L[ℂ] E) (T : E →L[ℂ] F) (L : X →L[ℂ] G)
    (A : F →ₗ.[ℂ] G) (hA : A.IsClosed) (C : Submodule ℂ X) (hC : Dense (C : Set X))
    (h : ∀ c : C, ∃ hc : T (J c) ∈ A.domain, A ⟨T (J c), hc⟩ = L c) (u : X) :
    ‖closed_graph_extension_map J T L A hA C hC h u‖ ^ 2 = ‖T (J u)‖ ^ 2 + ‖L u‖ ^ 2 :=
  graphDomain_norm_sq A hA _

lemma closed_graph_extension_bound (J : X →L[ℂ] E) (T : E →L[ℂ] F) (L : X →L[ℂ] G)
    (A : F →ₗ.[ℂ] G) (hA : A.IsClosed) (C : Submodule ℂ X) (hC : Dense (C : Set X))
    (h : ∀ c : C, ∃ hc : T (J c) ∈ A.domain, A ⟨T (J c), hc⟩ = L c) (u : X) :
    ‖closed_graph_extension_map J T L A hA C hC h u‖ ^ 2 ≤
      (‖T‖ ^ 2 * ‖J‖ ^ 2 + ‖L‖ ^ 2) * ‖u‖ ^ 2 := by
  rw [closed_graph_extension_norm_sq]
  have ht : ‖T (J u)‖ ≤ ‖T‖ * ‖J‖ * ‖u‖ :=
    (T.le_opNorm _).trans (by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (J.le_opNorm u) (norm_nonneg T))
  have hts := pow_le_pow_left₀ (norm_nonneg _) ht 2
  have hls := pow_le_pow_left₀ (norm_nonneg _) (L.le_opNorm u) 2
  nlinarith

lemma closed_graph_extension_forms (C : Submodule ℂ X) (hC : Dense (C : Set X))
    (b c : GW.Analysis.BoundedForm X) (h : ∀ u : C, ∀ v : C, b u v = c u v) : b = c := by
  apply GW.Analysis.form_dense_determination b c C hC
  intro u hu v hv
  exact h ⟨u, hu⟩ ⟨v, hv⟩
end GW.Operators
