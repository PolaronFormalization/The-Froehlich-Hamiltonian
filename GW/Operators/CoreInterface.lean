module
public import GW.Operators.GraphIntegration
public import GW.Operators.Adjoints
public import Mathlib.Tactic
/-! Source basic:partial-operator-bridge. Graph-norm density and exact adjoint
domain witnesses use the previously verified graph and adjoint interfaces. -/
@[expose] public section
noncomputable section
open scoped Topology InnerProductSpace
namespace GW.Operators
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

lemma core_graph_image (T : E →ₗ.[ℂ] F) (hT : T.IsClosed) (C : Submodule ℂ E)
    (_hC : C ≤ T.domain) :
    (fun v : GraphDomain T hT => (graphInclusion T hT v, graphAction T hT v)) ''
      {v | graphInclusion T hT v ∈ C} = ((T.domRestrict C).graph : Set (E × F)) := by
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨u, hu, hau⟩ := graphDomain_mem T hT v
    refine (T.domRestrict C).mem_graph_iff.mpr ⟨⟨u, ?_⟩, hu, ?_⟩
    · exact ⟨hu.symm ▸ hv, u.property⟩
    · exact (LinearPMap.domRestrict_apply rfl).trans hau
  · intro hz
    obtain ⟨u, hu, hau⟩ := (T.domRestrict C).mem_graph_iff.mp hz
    let v : T.domain := ⟨u, u.property.2⟩
    refine ⟨graphLift T hT v, ?_, ?_⟩
    · exact u.property.1
    · exact Prod.ext hu ((LinearPMap.domRestrict_apply (x := u) (y := v) rfl).symm.trans hau)

/-- Graph-norm density is exactly equality of ambient graph closures. -/
lemma graph_dense_iff_closure (T : E →ₗ.[ℂ] F) (hT : T.IsClosed) (C : Submodule ℂ E)
    (hC : C ≤ T.domain) :
    Dense {v : GraphDomain T hT | graphInclusion T hT v ∈ C} ↔
      (T.domRestrict C).graph.topologicalClosure = T.graph := by
  have hind : Topology.IsInducing (fun v : GraphDomain T hT =>
      (graphInclusion T hT v, graphAction T hT v)) :=
    (WithLp.prodContinuousLinearEquiv 2 ℂ E F).toHomeomorph.isInducing.comp
      Topology.IsInducing.subtypeVal
  rw [hind.dense_iff, core_graph_image T hT C hC]
  constructor
  · intro hd
    apply le_antisymm
    · change closure ((T.domRestrict C).graph : Set (E × F)) ⊆ (T.graph : Set (E × F))
      exact closure_minimal (LinearPMap.le_graph_of_le LinearPMap.domRestrict_le) hT
    · intro z hz
      obtain ⟨u, hu⟩ := T.mem_graph_iff'.mp hz
      change z ∈ closure ((T.domRestrict C).graph : Set (E × F))
      have hv := hd (graphLift T hT u)
      simpa only [graphInclusion_lift, graphAction_lift, hu] using hv
  · intro he v
    have hm : (graphInclusion T hT v, graphAction T hT v) ∈ T.graph := v.property
    rw [← he] at hm
    exact hm

/-- Exact core interface, including the prerequisite domain inclusion. -/
lemma hasCore_iff_graph_dense (T : E →ₗ.[ℂ] F) (hT : T.IsClosed) (C : Submodule ℂ E)
    (hC : C ≤ T.domain) :
    T.HasCore C ↔ Dense {v : GraphDomain T hT | graphInclusion T hT v ∈ C} := by
  have hc : (T.domRestrict C).IsClosable := hT.isClosable.leIsClosable LinearPMap.domRestrict_le
  rw [graph_dense_iff_closure T hT C hC, hc.graph_closure_eq_closure_graph]
  exact ⟨fun h => congrArg LinearPMap.graph h.closure_eq,
    fun h => ⟨hC, LinearPMap.eq_of_eq_graph h⟩⟩
section AdjointWitness
variable [CompleteSpace E]

/-- Exact equality of the full adjoint domain with the manuscript witness set. -/
lemma adjoint_domain_iff_witness (T : E →ₗ.[ℂ] F) (hd : Dense (T.domain : Set E)) (y : F) :
    y ∈ T.adjoint.domain ↔ ∃ h : E, ∀ x : T.domain, ⟪T x, y⟫_ℂ = ⟪(x : E), h⟫_ℂ := by
  constructor
  · intro hy
    exact ⟨T.adjoint ⟨y, hy⟩, fun x => adjoint_pairing T hd x ⟨y, hy⟩⟩
  · rintro ⟨h, hh⟩
    exact adjoint_mem_of_witness T hh

lemma adjoint_witness_unique (T : E →ₗ.[ℂ] F) (hd : Dense (T.domain : Set E))
    {y : F} {h k : E}
    (hh : ∀ x : T.domain, ⟪T x, y⟫_ℂ = ⟪(x : E), h⟫_ℂ)
    (hk : ∀ x : T.domain, ⟪T x, y⟫_ℂ = ⟪(x : E), k⟫_ℂ) : h = k := by
  let ya : T.adjoint.domain := ⟨y, adjoint_mem_of_witness T hh⟩
  exact (adjoint_eq_of_witness T hd ya hh).symm.trans (adjoint_eq_of_witness T hd ya hk)
end AdjointWitness

end GW.Operators
