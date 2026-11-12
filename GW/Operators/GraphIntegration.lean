module
public import GW.Conventions
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Source basic:graph-integration. The graph carrier uses the Hilbert product
WithLp 2, and its two coordinates retain the actual partial operator domain. -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ENNReal Topology
namespace GW.Operators
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The closed graph inside the Hilbert product, with the L² product norm. -/
def hilbertGraph (A : E →ₗ.[ℂ] F) (hA : A.IsClosed) :
    ClosedSubmodule ℂ (WithLp 2 (E × F)) where
  toSubmodule := A.graph.comap (WithLp.linearEquiv 2 ℂ (E × F)).toLinearMap
  isClosed' := hA.preimage (WithLp.prodContinuousLinearEquiv 2 ℂ E F).continuous

abbrev GraphDomain (A : E →ₗ.[ℂ] F) (hA : A.IsClosed) := hilbertGraph A hA

lemma graphDomain_mem (A : E →ₗ.[ℂ] F) (hA : A.IsClosed) (v : GraphDomain A hA) :
    ∃ u : A.domain, (u : E) = (v : WithLp 2 (E × F)).fst ∧
      A u = (v : WithLp 2 (E × F)).snd :=
  (A.mem_graph_iff).mp v.property

/-- The ambient coordinate of the graph domain. -/
def graphInclusion (A : E →ₗ.[ℂ] F) (hA : A.IsClosed) : GraphDomain A hA →L[ℂ] E :=
  (WithLp.fstL 2 ℂ E F).comp (hilbertGraph A hA).toSubmodule.subtypeL

/-- The image coordinate of the graph domain. -/
def graphAction (A : E →ₗ.[ℂ] F) (hA : A.IsClosed) : GraphDomain A hA →L[ℂ] F :=
  (WithLp.sndL 2 ℂ E F).comp (hilbertGraph A hA).toSubmodule.subtypeL

lemma graphDomain_norm_sq (A : E →ₗ.[ℂ] F) (hA : A.IsClosed) (v : GraphDomain A hA) :
    ‖v‖ ^ 2 = ‖graphInclusion A hA v‖ ^ 2 + ‖graphAction A hA v‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 (v : WithLp 2 (E × F))

lemma graphDomain_inner (A : E →ₗ.[ℂ] F) (hA : A.IsClosed) (v z : GraphDomain A hA) :
    ⟪v,z⟫_ℂ = ⟪graphInclusion A hA v, graphInclusion A hA z⟫_ℂ +
      ⟪graphAction A hA v, graphAction A hA z⟫_ℂ := rfl

lemma graphInclusion_bound (A : E →ₗ.[ℂ] F) (hA : A.IsClosed) (v : GraphDomain A hA) :
    ‖graphInclusion A hA v‖ ≤ ‖v‖ := WithLp.norm_fst_le E (v : WithLp 2 (E × F))
lemma graphAction_bound (A : E →ₗ.[ℂ] F) (hA : A.IsClosed) (v : GraphDomain A hA) :
    ‖graphAction A hA v‖ ≤ ‖v‖ := WithLp.norm_snd_le E (v : WithLp 2 (E × F))
/-- Algebraic graph lift. Its domain's ambient subtype norm is not called a graph norm. -/
def graphLift (A : E →ₗ.[ℂ] F) (hA : A.IsClosed) : A.domain →ₗ[ℂ] GraphDomain A hA where
  toFun u := ⟨WithLp.toLp 2 ((u : E), A u), A.mem_graph u⟩
  map_add' u v := by
    apply Subtype.ext
    change WithLp.toLp 2 _ = WithLp.toLp 2 _
    congr 1
    exact Prod.ext rfl (map_add A.toFun u v)
  map_smul' c u := by
    apply Subtype.ext
    change WithLp.toLp 2 _ = WithLp.toLp 2 _
    congr 1
    exact Prod.ext rfl (map_smul A.toFun c u)

@[simp] lemma graphInclusion_lift (A : E →ₗ.[ℂ] F) (hA : A.IsClosed) (u : A.domain) :
    graphInclusion A hA (graphLift A hA u) = u := rfl
@[simp] lemma graphAction_lift (A : E →ₗ.[ℂ] F) (hA : A.IsClosed) (u : A.domain) :
    graphAction A hA (graphLift A hA u) = A u := rfl

lemma graphLift_bijective (A : E →ₗ.[ℂ] F) (hA : A.IsClosed) :
    Function.Bijective (graphLift A hA) := by
  constructor
  · intro u v h
    apply Subtype.ext
    exact congrArg (graphInclusion A hA) h
  · intro v
    obtain ⟨u, hu, hau⟩ := graphDomain_mem A hA v
    refine ⟨u, ?_⟩
    apply Subtype.ext
    apply (WithLp.equiv 2 (E × F)).injective
    exact Prod.ext hu hau

/-- The actual operator domain is identified algebraically with its Hilbert graph carrier. -/
def graphDomainEquiv (A : E →ₗ.[ℂ] F) (hA : A.IsClosed) : A.domain ≃ₗ[ℂ] GraphDomain A hA :=
  LinearEquiv.ofBijective (graphLift A hA) (graphLift_bijective A hA)

lemma graph_norm_le_sum (A : E →ₗ.[ℂ] F) (hA : A.IsClosed) (v : GraphDomain A hA) :
    ‖v‖ ≤ ‖graphInclusion A hA v‖ + ‖graphAction A hA v‖ := by
  have hsq := graphDomain_norm_sq A hA v
  nlinarith [norm_nonneg v, norm_nonneg (graphInclusion A hA v),
    norm_nonneg (graphAction A hA v)]

lemma graphLift_norm_sq (A : E →ₗ.[ℂ] F) (hA : A.IsClosed) (u : A.domain) :
    ‖graphLift A hA u‖ ^ 2 = ‖(u : E)‖ ^ 2 + ‖A u‖ ^ 2 :=
  graphDomain_norm_sq A hA (graphLift A hA u)

lemma graphLift_inner (A : E →ₗ.[ℂ] F) (hA : A.IsClosed) (u v : A.domain) :
    ⟪graphLift A hA u, graphLift A hA v⟫_ℂ = ⟪(u : E), (v : E)⟫_ℂ + ⟪A u, A v⟫_ℂ := rfl

lemma graphInclusion_opNorm_le (A : E →ₗ.[ℂ] F) (hA : A.IsClosed) :
    ‖graphInclusion A hA‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simpa only [one_mul] using graphInclusion_bound A hA v

lemma graphAction_opNorm_le (A : E →ₗ.[ℂ] F) (hA : A.IsClosed) :
    ‖graphAction A hA‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simpa only [one_mul] using graphAction_bound A hA v

variable [CompleteSpace E] [CompleteSpace F]
variable {S : Type*} [MeasurableSpace S] {μ : Measure S}

/-- Project the ambient measurable pair onto the closed graph as in the source proof. -/
lemma graphLift_aestronglyMeasurable (A : E →ₗ.[ℂ] F) (hA : A.IsClosed) (f : S → A.domain)
    (hf : AEStronglyMeasurable (fun x => (f x : E)) μ)
    (hAf : AEStronglyMeasurable (fun x => A (f x)) μ) :
    AEStronglyMeasurable (fun x => graphLift A hA (f x)) μ := by
  have hp := (WithLp.prodContinuousLinearEquiv 2 ℂ E F).symm.continuous.comp_aestronglyMeasurable
    (hf.prodMk hAf)
  have hproj := (hilbertGraph A hA).toSubmodule.orthogonalProjectionOnto.continuous.comp_aestronglyMeasurable hp
  apply hproj.congr
  apply Filter.Eventually.of_forall
  intro x
  exact (hilbertGraph A hA).toSubmodule.orthogonalProjectionOnto_mem_subspace_eq_self
    (graphLift A hA (f x))

lemma graphLift_integrable (A : E →ₗ.[ℂ] F) (hA : A.IsClosed) (f : S → A.domain)
    (hf : AEStronglyMeasurable (fun x => (f x : E)) μ)
    (hAf : AEStronglyMeasurable (fun x => A (f x)) μ)
    (hi : Integrable (fun x => ‖(f x : E)‖ + ‖A (f x)‖) μ) :
    Integrable (fun x => graphLift A hA (f x)) μ := by
  apply hi.mono' (graphLift_aestronglyMeasurable A hA f hf hAf)
  exact Filter.Eventually.of_forall (fun x => graph_norm_le_sum A hA (graphLift A hA (f x)))

/-- The ambient integral has an actual domain witness and the stated operator value. -/
lemma closed_operator_integral (A : E →ₗ.[ℂ] F) (hA : A.IsClosed) (f : S → A.domain)
    (hf : AEStronglyMeasurable (fun x => (f x : E)) μ)
    (hAf : AEStronglyMeasurable (fun x => A (f x)) μ)
    (hi : Integrable (fun x => ‖(f x : E)‖ + ‖A (f x)‖) μ) :
    ∃ u : A.domain, (u : E) = ∫ x, (f x : E) ∂μ ∧ A u = ∫ x, A (f x) ∂μ := by
  have hfi := graphLift_integrable A hA f hf hAf hi
  obtain ⟨u, hu, hau⟩ := graphDomain_mem A hA (∫ x, graphLift A hA (f x) ∂μ)
  refine ⟨u, ?_, ?_⟩
  · exact hu.trans ((graphInclusion A hA).integral_comp_comm hfi).symm
  · exact hau.trans ((graphAction A hA).integral_comp_comm hfi).symm

/- Exact finite-extended-integral version of the source's integrability condition. -/
omit [CompleteSpace E] [CompleteSpace F] in
lemma graph_sum_integrable_iff (A : E →ₗ.[ℂ] F) (f : S → A.domain)
    (hf : AEStronglyMeasurable (fun x => (f x : E)) μ)
    (hAf : AEStronglyMeasurable (fun x => A (f x)) μ) :
    Integrable (fun x => ‖(f x : E)‖ + ‖A (f x)‖) μ ↔
      (∫⁻ x, ENNReal.ofReal (‖(f x : E)‖ + ‖A (f x)‖) ∂μ) < ∞ := by
  have hn : 0 ≤ᵐ[μ] (fun x => ‖(f x : E)‖ + ‖A (f x)‖) :=
    Filter.Eventually.of_forall (fun x => add_nonneg (norm_nonneg _) (norm_nonneg _))
  exact ⟨fun h => (hasFiniteIntegral_iff_ofReal hn).mp h.2,
    fun h => ⟨hf.norm.add hAf.norm, (hasFiniteIntegral_iff_ofReal hn).mpr h⟩⟩

end GW.Operators
