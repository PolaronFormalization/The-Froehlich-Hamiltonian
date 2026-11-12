module
public import GW.Operators.CoreInterface
public import GW.Analysis.MixedForms
/-! Source bridge:closure-core. Symmetry and density give a single-valued
closed graph; dense parametrized cores use their given norm and bounded coordinates. -/
@[expose] public section
noncomputable section
open scoped Topology InnerProductSpace
namespace GW.Operators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Continuity passes the symmetric pairing to both coordinates of the graph closure. -/
lemma symmetric_graph_closure_pairing (T : H →ₗ.[ℂ] H) (hs : T.IsFormalAdjoint T) :
    ∀ p ∈ closure (T.graph : Set (H × H)), ∀ q ∈ closure (T.graph : Set (H × H)),
      ⟪p.2, q.1⟫_ℂ = ⟪p.1, q.2⟫_ℂ := by
  apply eqOn_closure₂'
  · intro p hp q hq
    obtain ⟨u, hu⟩ := T.mem_graph_iff'.mp hp
    obtain ⟨v, hv⟩ := T.mem_graph_iff'.mp hq
    rw [← hu, ← hv]
    exact hs u v
  · intro p
    exact continuous_const.inner continuous_fst
  · intro q
    exact continuous_snd.inner continuous_const
  · intro p
    exact continuous_const.inner continuous_snd
  · intro q
    exact continuous_fst.inner continuous_const

lemma symmetric_closure_zero (T : H →ₗ.[ℂ] H) (hd : Dense (T.domain : Set H))
    (hs : T.IsFormalAdjoint T) (p : H × H) (hp : p ∈ T.graph.topologicalClosure)
    (hzero : p.1 = 0) : p.2 = 0 := by
  have hann : Set.EqOn (fun x : H => ⟪x, p.2⟫_ℂ) (fun _ => 0) T.domain := by
    intro x hx
    have he := symmetric_graph_closure_pairing T hs ((x, T ⟨x,hx⟩))
      (subset_closure (T.mem_graph ⟨x,hx⟩)) p hp
    simpa only [hzero, inner_zero_right] using he.symm
  have hall := hann.closure (continuous_id.inner continuous_const) continuous_const
  exact inner_self_eq_zero.mp (hall (hd p.2))

/-- Density and symmetry prove the graph is single-valued before library closure is used. -/
lemma symmetric_isClosable (T : H →ₗ.[ℂ] H) (hd : Dense (T.domain : Set H))
    (hs : T.IsFormalAdjoint T) : T.IsClosable := by
  use T.graph.topologicalClosure.toLinearPMap
  rw [Submodule.toLinearPMap_graph_eq]
  exact symmetric_closure_zero T hd hs

lemma symmetric_closure_dense (T : H →ₗ.[ℂ] H) (hd : Dense (T.domain : Set H)) :
    Dense (T.closure.domain : Set H) :=
  Dense.mono T.le_closure.1 hd

lemma symmetric_closure_symmetric (T : H →ₗ.[ℂ] H) (hd : Dense (T.domain : Set H))
    (hs : T.IsFormalAdjoint T) : T.closure.IsFormalAdjoint T.closure := by
  have hc := symmetric_isClosable T hd hs
  intro u v
  apply symmetric_graph_closure_pairing T hs ((u : H), T.closure u) ?_ ((v : H), T.closure v) ?_
  · change ((u : H), T.closure u) ∈ T.graph.topologicalClosure
    rw [hc.graph_closure_eq_closure_graph]
    exact T.closure.mem_graph u
  · change ((v : H), T.closure v) ∈ T.graph.topologicalClosure
    rw [hc.graph_closure_eq_closure_graph]
    exact T.closure.mem_graph v

lemma symmetric_closure_closed (T : H →ₗ.[ℂ] H) (hd : Dense (T.domain : Set H))
    (hs : T.IsFormalAdjoint T) : T.closure.IsClosed :=
  (symmetric_isClosable T hd hs).closure_isClosed
lemma graph_coordinate_injective (A : H →ₗ.[ℂ] H) (hA : A.IsClosed) :
    Function.Injective (graphInclusion A hA) := by
  intro v w hv
  obtain ⟨u, hu, hau⟩ := graphDomain_mem A hA v
  obtain ⟨z, hz, haz⟩ := graphDomain_mem A hA w
  have he : u = z := Subtype.ext (hu.trans (hv.trans hz.symm))
  apply Subtype.ext
  apply (WithLp.equiv 2 (H × H)).injective
  apply Prod.ext hv
  exact hau.symm.trans ((congrArg A.toFun he).trans haz)

/-- An extension agrees with its source on every subdomain of the source. -/
lemma restriction_of_extension {T A : H →ₗ.[ℂ] H} (hTA : T ≤ A) (S : Submodule ℂ H)
    (hS : S ≤ T.domain) : A.domRestrict S = T.domRestrict S := by
  ext x h1 h2
  · change x ∈ S ⊓ A.domain ↔ x ∈ S ⊓ T.domain
    exact ⟨fun h => ⟨h.1, hS h.1⟩, fun h => ⟨h.1, hTA.1 h.2⟩⟩
  · change A ⟨x, h1.2⟩ = T ⟨x, h2.2⟩
    exact (hTA.2 rfl).symm

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The two bounded coordinates lift into the closed graph of the actual closure. -/
def closureGraphMap (T : H →ₗ.[ℂ] H) (hd : Dense (T.domain : Set H))
    (hs : T.IsFormalAdjoint T) (J L : X →L[ℂ] H)
    (hL : ∀ x, ∃ u : T.domain, (u : H) = J x ∧ T u = L x) :
    X →L[ℂ] GraphDomain T.closure (symmetric_closure_closed T hd hs) :=
  (((WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.toContinuousLinearMap).comp (J.prod L)).codRestrict
    (hilbertGraph T.closure (symmetric_closure_closed T hd hs)).toSubmodule (fun x => by
      have hp : (J x, L x) ∈ T.graph := by
        obtain ⟨u, hu, hTu⟩ := hL x
        exact T.mem_graph_iff.mpr ⟨u, hu, hTu⟩
      exact LinearPMap.le_graph_of_le T.le_closure hp)

lemma closureGraphMap_range (T : H →ₗ.[ℂ] H) (hd : Dense (T.domain : Set H))
    (hs : T.IsFormalAdjoint T) (J L : X →L[ℂ] H)
    (hJ : Set.range J = (T.domain : Set H))
    (hL : ∀ x, ∃ u : T.domain, (u : H) = J x ∧ T u = L x) :
    Set.range (closureGraphMap T hd hs J L hL) =
      {v | graphInclusion T.closure (symmetric_closure_closed T hd hs) v ∈ T.domain} := by
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    change J x ∈ T.domain
    exact (show J x ∈ (T.domain : Set H) from hJ ▸ Set.mem_range_self x)
  · intro hv
    have hv' : graphInclusion T.closure (symmetric_closure_closed T hd hs) v ∈ Set.range J :=
      hJ.symm ▸ (show graphInclusion T.closure (symmetric_closure_closed T hd hs) v ∈ (T.domain : Set H) from hv)
    obtain ⟨x, hx⟩ := hv'
    refine ⟨x, graph_coordinate_injective T.closure (symmetric_closure_closed T hd hs) ?_⟩
    exact hx

lemma closureGraphMap_denseRange (T : H →ₗ.[ℂ] H) (hd : Dense (T.domain : Set H))
    (hs : T.IsFormalAdjoint T) (J L : X →L[ℂ] H)
    (hJ : Set.range J = (T.domain : Set H))
    (hL : ∀ x, ∃ u : T.domain, (u : H) = J x ∧ T u = L x) :
    DenseRange (closureGraphMap T hd hs J L hL) := by
  rw [DenseRange, closureGraphMap_range T hd hs J L hJ hL]
  exact (hasCore_iff_graph_dense T.closure (symmetric_closure_closed T hd hs)
    T.domain T.le_closure.1).mp T.closureHasCore

/-- Density in the given X norm gives a core of the closed symmetric operator. -/
lemma symmetric_closure_hasCore (T : H →ₗ.[ℂ] H) (hd : Dense (T.domain : Set H))
    (hs : T.IsFormalAdjoint T) (J L : X →L[ℂ] H)
    (hJ : Set.range J = (T.domain : Set H))
    (hL : ∀ x, ∃ u : T.domain, (u : H) = J x ∧ T u = L x)
    (C : Submodule ℂ X) (hC : Dense (C : Set X)) : T.closure.HasCore (C.map J.toLinearMap) := by
  have hsub : C.map J.toLinearMap ≤ T.domain := by
    rintro y ⟨x, hx, rfl⟩
    exact (show J x ∈ (T.domain : Set H) from hJ ▸ Set.mem_range_self x)
  apply (hasCore_iff_graph_dense T.closure (symmetric_closure_closed T hd hs)
    (C.map J.toLinearMap) (hsub.trans T.le_closure.1)).mpr
  have hDense := (closureGraphMap_denseRange T hd hs J L hJ hL).dense_image
    (closureGraphMap T hd hs J L hL).continuous hC
  apply Dense.mono ?_ hDense
  rintro v ⟨x, hx, rfl⟩
  exact ⟨x, hx, rfl⟩

lemma closureGraphMap_norm_sq (T : H →ₗ.[ℂ] H) (hd : Dense (T.domain : Set H))
    (hs : T.IsFormalAdjoint T) (J L : X →L[ℂ] H)
    (hL : ∀ x, ∃ u : T.domain, (u : H) = J x ∧ T u = L x) (x : X) :
    ‖closureGraphMap T hd hs J L hL x‖ ^ 2 = ‖J x‖ ^ 2 + ‖L x‖ ^ 2 :=
  graphDomain_norm_sq T.closure (symmetric_closure_closed T hd hs) _

lemma closureGraphMap_bound (T : H →ₗ.[ℂ] H) (hd : Dense (T.domain : Set H))
    (hs : T.IsFormalAdjoint T) (J L : X →L[ℂ] H)
    (hL : ∀ x, ∃ u : T.domain, (u : H) = J x ∧ T u = L x) (x : X) :
    ‖closureGraphMap T hd hs J L hL x‖ ^ 2 ≤ (‖J‖ ^ 2 + ‖L‖ ^ 2) * ‖x‖ ^ 2 := by
  rw [closureGraphMap_norm_sq]
  have hj := pow_le_pow_left₀ (norm_nonneg _) (J.le_opNorm x) 2
  have hl := pow_le_pow_left₀ (norm_nonneg _) (L.le_opNorm x) 2
  nlinarith

/-- The two source graph closures agree on the nose, with full domains retained. -/
lemma dense_restriction_graph_closure (T : H →ₗ.[ℂ] H) (hd : Dense (T.domain : Set H))
    (hs : T.IsFormalAdjoint T) (J L : X →L[ℂ] H)
    (hJ : Set.range J = (T.domain : Set H))
    (hL : ∀ x, ∃ u : T.domain, (u : H) = J x ∧ T u = L x)
    (C : Submodule ℂ X) (hC : Dense (C : Set X)) :
    (T.domRestrict (C.map J.toLinearMap)).graph.topologicalClosure = T.graph.topologicalClosure := by
  have hc := symmetric_isClosable T hd hs
  have hr : (T.domRestrict (C.map J.toLinearMap)).IsClosable := hc.leIsClosable LinearPMap.domRestrict_le
  have hsub : C.map J.toLinearMap ≤ T.domain := by
    rintro y ⟨x, hx, rfl⟩
    exact (show J x ∈ (T.domain : Set H) from hJ ▸ Set.mem_range_self x)
  rw [hr.graph_closure_eq_closure_graph, hc.graph_closure_eq_closure_graph]
  apply congrArg LinearPMap.graph
  rw [← restriction_of_extension T.le_closure _ hsub]
  exact (symmetric_closure_hasCore T hd hs J L hJ hL C hC).closure_eq

/-- Complete source package: an actual densely defined closed symmetric closure
and equality of both graph closures for every given dense parametrized core. -/
lemma symmetric_closure_core (T : H →ₗ.[ℂ] H) (hd : Dense (T.domain : Set H))
    (hs : T.IsFormalAdjoint T) (J L : X →L[ℂ] H) (_hInjective : Function.Injective J)
    (hJ : Set.range J = (T.domain : Set H))
    (hL : ∀ x, ∃ u : T.domain, (u : H) = J x ∧ T u = L x)
    (C : Submodule ℂ X) (hC : Dense (C : Set X)) :
    ∃ A : H →ₗ.[ℂ] H, Dense (A.domain : Set H) ∧ A.IsClosed ∧ A.IsFormalAdjoint A ∧
      T ≤ A ∧ T.graph.topologicalClosure = A.graph ∧
      (T.domRestrict (C.map J.toLinearMap)).graph.topologicalClosure = A.graph ∧
      A.HasCore (C.map J.toLinearMap) := by
  have hc := symmetric_isClosable T hd hs
  refine ⟨T.closure, symmetric_closure_dense T hd, symmetric_closure_closed T hd hs,
    symmetric_closure_symmetric T hd hs, T.le_closure, hc.graph_closure_eq_closure_graph, ?_,
    symmetric_closure_hasCore T hd hs J L hJ hL C hC⟩
  exact (dense_restriction_graph_closure T hd hs J L hJ hL C hC).trans hc.graph_closure_eq_closure_graph

end GW.Operators
