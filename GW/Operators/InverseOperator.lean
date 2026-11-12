module
public import GW.Operators.CoreInterface
public import GW.Operators.ClosureCore
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
/-! Source basic:inverse-operator. The inverse is constructed on the actual
range. Adjoint witnesses, real shifts and cores retain their full domains. -/
@[expose] public section
noncomputable section
open scoped Topology InnerProductSpace
namespace GW.Operators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Actual inverse on the range, defined by the unique injective-map witness. -/
def inverseOperator (R : H →L[ℂ] H) (hR : Function.Injective R) : H →ₗ.[ℂ] H where
  domain := R.range
  toFun := (LinearEquiv.ofInjective R.toLinearMap hR).symm.toLinearMap

lemma inverseOperator_domain (R : H →L[ℂ] H) (hR : Function.Injective R) :
    (inverseOperator R hR).domain = R.range := rfl

lemma inverseOperator_right (R : H →L[ℂ] H) (hR : Function.Injective R)
    (u : (inverseOperator R hR).domain) : R (inverseOperator R hR u) = (u : H) :=
  LinearEquiv.ofInjective_symm_apply R.toLinearMap (h := hR) u

lemma inverseOperator_left (R : H →L[ℂ] H) (hR : Function.Injective R) (f : H) :
    inverseOperator R hR ⟨R f, LinearMap.mem_range_self R.toLinearMap f⟩ = f :=
  (LinearEquiv.ofInjective R.toLinearMap hR).symm_apply_apply f

lemma inverseOperator_apply_eq (R : H →L[ℂ] H) (hR : Function.Injective R)
    (u : (inverseOperator R hR).domain) (f : H) (hf : R f = (u : H)) :
    inverseOperator R hR u = f :=
  hR ((inverseOperator_right R hR u).trans hf.symm)

lemma inverseOperator_graph_iff (R : H →L[ℂ] H) (hR : Function.Injective R) (p : H × H) :
    p ∈ (inverseOperator R hR).graph ↔ R p.2 = p.1 := by
  constructor
  · intro hp
    obtain ⟨u, hu, hSu⟩ := (inverseOperator R hR).mem_graph_iff.mp hp
    rw [← hSu, inverseOperator_right, hu]
  · intro hp
    let u : (inverseOperator R hR).domain := ⟨p.1, ⟨p.2, hp⟩⟩
    exact (inverseOperator R hR).mem_graph_iff.mpr
      ⟨u, rfl, inverseOperator_apply_eq R hR u p.2 hp⟩

lemma inverseOperator_closed (R : H →L[ℂ] H) (hR : Function.Injective R) :
    (inverseOperator R hR).IsClosed := by
  have he : ((inverseOperator R hR).graph : Set (H × H)) = {p | R p.2 = p.1} :=
    Set.ext (inverseOperator_graph_iff R hR)
  change IsClosed ((inverseOperator R hR).graph : Set (H × H))
  rw [he]
  exact isClosed_eq (R.continuous.comp continuous_snd) continuous_fst

lemma inverseOperator_unique (R : H →L[ℂ] H) (hR : Function.Injective R)
    (S : H →ₗ.[ℂ] H) (hdom : S.domain = R.range)
    (hleft : ∀ f, ∃ hf : R f ∈ S.domain, S ⟨R f, hf⟩ = f) : S = inverseOperator R hR := by
  apply LinearPMap.dExt hdom
  intro x y hxy
  obtain ⟨f, hf⟩ := y.property
  obtain ⟨hmem, hval⟩ := hleft f
  have he : (⟨R f, hmem⟩ : S.domain) = x := Subtype.ext (hf.trans hxy.symm)
  rw [he] at hval
  exact hval.trans (inverseOperator_apply_eq R hR y f hf).symm

lemma inverseOperator_existsUnique (R : H →L[ℂ] H) (hR : Function.Injective R) :
    ∃! S : H →ₗ.[ℂ] H, S.domain = R.range ∧
      ∀ f, ∃ hf : R f ∈ S.domain, S ⟨R f, hf⟩ = f := by
  refine ⟨inverseOperator R hR, ⟨rfl, fun f => ?_⟩, ?_⟩
  · exact ⟨LinearMap.mem_range_self R.toLinearMap f, inverseOperator_left R hR f⟩
  · intro S hS
    exact inverseOperator_unique R hR S hS.1 hS.2

lemma closure_eq_of_closed (S : H →ₗ.[ℂ] H) (hS : S.IsClosed) : S.closure = S := by
  apply LinearPMap.eq_of_eq_graph
  rw [← hS.isClosable.graph_closure_eq_closure_graph, hS.submodule_topologicalClosure_eq]

lemma inverseOperator_graph_norm_bounds (R : H →L[ℂ] H) (hR : Function.Injective R) (f : H) :
    ‖f‖ ^ 2 ≤ ‖graphLift (inverseOperator R hR) (inverseOperator_closed R hR)
      ⟨R f, LinearMap.mem_range_self R.toLinearMap f⟩‖ ^ 2 ∧
    ‖graphLift (inverseOperator R hR) (inverseOperator_closed R hR)
      ⟨R f, LinearMap.mem_range_self R.toLinearMap f⟩‖ ^ 2 ≤ (1 + ‖R‖ ^ 2) * ‖f‖ ^ 2 := by
  rw [graphLift_norm_sq, inverseOperator_left]
  have h := pow_le_pow_left₀ (norm_nonneg _) (R.le_opNorm f) 2
  constructor <;> nlinarith [sq_nonneg ‖R f‖]

/-- A scalar shift on exactly the original operator domain. -/
def complexShift (S : H →ₗ.[ℂ] H) (z : ℂ) : H →ₗ.[ℂ] H where
  domain := S.domain
  toFun := S.toFun - z • S.domain.subtype

lemma complexShift_domain (S : H →ₗ.[ℂ] H) (z : ℂ) : (complexShift S z).domain = S.domain := rfl

lemma complexShift_apply (S : H →ₗ.[ℂ] H) (z : ℂ) (u : S.domain) :
    complexShift S z u = S u - z • (u : H) := rfl

/-- Real shifts are the same scalar-shift construction. -/
def realShift (S : H →ₗ.[ℂ] H) (c : ℝ) : H →ₗ.[ℂ] H := complexShift S (c : ℂ)

lemma complexShift_real (S : H →ₗ.[ℂ] H) (c : ℝ) : complexShift S (c : ℂ) = realShift S c := rfl

lemma realShift_domain (S : H →ₗ.[ℂ] H) (c : ℝ) : (realShift S c).domain = S.domain := rfl

lemma realShift_apply (S : H →ₗ.[ℂ] H) (c : ℝ) (u : S.domain) :
    realShift S c u = S u - (c : ℂ) • (u : H) := rfl

/-- Moving the real scalar across the pairing gives the exact adjoint witness shift. -/
lemma realShift_witness_iff (S : H →ₗ.[ℂ] H) (c : ℝ) (y h : H) :
    (∀ x : S.domain, ⟪realShift S c x, y⟫_ℂ = ⟪(x : H), h⟫_ℂ) ↔
    (∀ x : S.domain, ⟪S x, y⟫_ℂ = ⟪(x : H), h + (c : ℂ) • y⟫_ℂ) := by
  simp only [realShift_apply, inner_sub_left, inner_smul_left, inner_add_right,
    inner_smul_right, Complex.conj_ofReal]
  constructor
  · intro hw x
    have hx := hw x
    linear_combination hx
  · intro hw x
    have hx := hw x
    linear_combination hx

lemma realShift_symmetric (S : H →ₗ.[ℂ] H) (hs : S.IsFormalAdjoint S) (c : ℝ) :
    (realShift S c).IsFormalAdjoint (realShift S c) := by
  intro u v
  change ⟪S u - (c : ℂ) • (u : H), (v : H)⟫_ℂ =
    ⟪(u : H), S v - (c : ℂ) • (v : H)⟫_ℂ
  simp only [inner_sub_left, inner_smul_left, inner_sub_right,
    inner_smul_right, Complex.conj_ofReal, hs u v]

lemma realShift_graph_iff (S : H →ₗ.[ℂ] H) (c : ℝ) (p : H × H) :
    p ∈ (realShift S c).graph ↔ (p.1, p.2 + (c : ℂ) • p.1) ∈ S.graph := by
  constructor
  · intro hp
    obtain ⟨u, hu, hval⟩ := (realShift S c).mem_graph_iff.mp hp
    refine S.mem_graph_iff.mpr ⟨u, hu, ?_⟩
    change S u - (c : ℂ) • (u : H) = p.2 at hval
    change S u = p.2 + (c : ℂ) • p.1
    rw [← hu]
    exact (sub_eq_iff_eq_add).mp hval
  · intro hp
    obtain ⟨u, hu, hval⟩ := S.mem_graph_iff.mp hp
    refine (realShift S c).mem_graph_iff.mpr ⟨u, hu, ?_⟩
    change S u - (c : ℂ) • (u : H) = p.2
    change (u : H) = p.1 at hu
    change S u = p.2 + (c : ℂ) • p.1 at hval
    rw [hval, hu]
    module

lemma realShift_closed (S : H →ₗ.[ℂ] H) (hS : S.IsClosed) (c : ℝ) : (realShift S c).IsClosed := by
  have he : ((realShift S c).graph : Set (H × H)) =
      (fun p : H × H => (p.1, p.2 + (c : ℂ) • p.1)) ⁻¹' (S.graph : Set (H × H)) :=
    Set.ext (realShift_graph_iff S c)
  change IsClosed ((realShift S c).graph : Set (H × H))
  rw [he]
  exact hS.preimage (continuous_fst.prodMk (continuous_snd.add (continuous_fst.const_smul (c : ℂ))))

lemma realShift_cancel (S : H →ₗ.[ℂ] H) (c : ℝ) : realShift (realShift S c) (-c) = S := by
  apply LinearPMap.ext (f := realShift (realShift S c) (-c)) (g := S) rfl
  intro x h1 h2
  change (S ⟨x, h1⟩ - (c : ℂ) • x) - ((-c : ℝ) : ℂ) • x = S ⟨x, h2⟩
  simp only [Complex.ofReal_neg, neg_smul]
  module

lemma realShift_graph_comparison (S : H →ₗ.[ℂ] H) (c : ℝ) (u : S.domain) :
    ‖realShift S c u‖ ≤ ‖S u‖ + |c| * ‖(u : H)‖ ∧
    ‖S u‖ ≤ ‖realShift S c u‖ + |c| * ‖(u : H)‖ := by
  have hn : ‖(c : ℂ) • (u : H)‖ = |c| * ‖(u : H)‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  constructor
  · rw [realShift_apply]
    simpa only [hn] using norm_sub_le (S u) ((c : ℂ) • (u : H))
  · have he : S u = realShift S c u + (c : ℂ) • (u : H) := by rw [realShift_apply]; abel
    calc
      ‖S u‖ = ‖realShift S c u + (c : ℂ) • (u : H)‖ := congrArg norm he
      _ ≤ ‖realShift S c u‖ + ‖(c : ℂ) • (u : H)‖ := norm_add_le _ _
      _ = _ := by rw [hn]

lemma inverseOperator_shift_left (R : H →L[ℂ] H) (hR : Function.Injective R) (c : ℝ) (f : H) :
    realShift (inverseOperator R hR) c ⟨R f, LinearMap.mem_range_self R.toLinearMap f⟩ +
      (c : ℂ) • R f = f := by
  change (inverseOperator R hR ⟨R f, _⟩ - (c : ℂ) • R f) + (c : ℂ) • R f = f
  rw [inverseOperator_left]
  module

lemma inverseOperator_shift_right (R : H →L[ℂ] H) (hR : Function.Injective R) (c : ℝ)
    (u : (inverseOperator R hR).domain) :
    R (realShift (inverseOperator R hR) c u + (c : ℂ) • (u : H)) = (u : H) := by
  have he : realShift (inverseOperator R hR) c u + (c : ℂ) • (u : H) = inverseOperator R hR u := by
    rw [realShift_apply]
    abel
  rw [he, inverseOperator_right]


variable [CompleteSpace H]

lemma inverseOperator_dense (R : H →L[ℂ] H) (hR : Function.Injective R) (hs : R.adjoint = R) :
    Dense ((inverseOperator R hR).domain : Set H) := by
  change Dense (R.range : Set H)
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply R.range.topologicalClosure_eq_top_iff.mpr
  rw [R.orthogonal_range, hs]
  exact LinearMap.ker_eq_bot.mpr hR

lemma inverseOperator_symmetric (R : H →L[ℂ] H) (hR : Function.Injective R) (hs : R.adjoint = R) :
    (inverseOperator R hR).IsFormalAdjoint (inverseOperator R hR) := by
  intro u v
  have he := R.adjoint_inner_right (inverseOperator R hR u) (inverseOperator R hR v)
  rw [hs, inverseOperator_right, inverseOperator_right] at he
  exact he

lemma inverseOperator_adjoint_witness (R : H →L[ℂ] H) (hR : Function.Injective R)
    (hs : R.adjoint = R) (y : (inverseOperator R hR).adjoint.domain) :
    R ((inverseOperator R hR).adjoint y) = (y : H) := by
  apply ext_inner_left ℂ
  intro f
  have hp := adjoint_pairing (inverseOperator R hR) (inverseOperator_dense R hR hs)
    ⟨R f, LinearMap.mem_range_self R.toLinearMap f⟩ y
  rw [inverseOperator_left] at hp
  have he := R.adjoint_inner_right f ((inverseOperator R hR).adjoint y)
  rw [hs] at he
  exact he.trans hp.symm

lemma inverseOperator_selfadjoint (R : H →L[ℂ] H) (hR : Function.Injective R)
    (hs : R.adjoint = R) : IsSelfAdjointOperator (inverseOperator R hR) := by
  refine ⟨inverseOperator_dense R hR hs, le_antisymm ?_ ?_⟩
  · apply LinearPMap.le_of_le_graph
    intro p hp
    obtain ⟨y, hy⟩ := (inverseOperator R hR).adjoint.mem_graph_iff'.mp hp
    rw [← hy, inverseOperator_graph_iff]
    exact inverseOperator_adjoint_witness R hR hs y
  · exact LinearPMap.IsFormalAdjoint.le_adjoint (inverseOperator_dense R hR hs)
      (inverseOperator_symmetric R hR hs)

lemma inverseOperator_nonneg (R : H →L[ℂ] H) (hR : Function.Injective R) (hs : R.adjoint = R)
    (hp : ∀ f, 0 ≤ (⟪f, R f⟫_ℂ).re) (u : (inverseOperator R hR).domain) :
    0 ≤ (⟪(u : H), inverseOperator R hR u⟫_ℂ).re := by
  have he := R.adjoint_inner_right (inverseOperator R hR u) (inverseOperator R hR u)
  rw [hs, inverseOperator_right] at he
  rw [← he]
  simpa only [inverseOperator_right] using hp (inverseOperator R hR u)
lemma inverseOperator_core (R : H →L[ℂ] H) (hR : Function.Injective R) (hs : R.adjoint = R)
    (C : Submodule ℂ H) (hC : Dense (C : Set H)) :
    (inverseOperator R hR).HasCore (C.map R.toLinearMap) := by
  have hc := symmetric_closure_hasCore (inverseOperator R hR) (inverseOperator_dense R hR hs)
    (inverseOperator_symmetric R hR hs) R (ContinuousLinearMap.id ℂ H) rfl
    (fun f => ⟨⟨R f, LinearMap.mem_range_self R.toLinearMap f⟩, rfl, inverseOperator_left R hR f⟩) C hC
  rwa [closure_eq_of_closed _ (inverseOperator_closed R hR)] at hc

lemma realShift_selfadjoint (S : H →ₗ.[ℂ] H) (hS : IsSelfAdjointOperator S) (c : ℝ) :
    IsSelfAdjointOperator (realShift S c) := by
  have hsym : S.IsFormalAdjoint S := by
    simpa only [hS.2] using LinearPMap.adjoint_isFormalAdjoint hS.1
  have hD : Dense ((realShift S c).domain : Set H) := hS.1
  refine ⟨hD, le_antisymm ?_ (LinearPMap.IsFormalAdjoint.le_adjoint hD (realShift_symmetric S hsym c))⟩
  apply LinearPMap.le_of_le_graph
  intro p hp
  obtain ⟨y, hy⟩ := (realShift S c).adjoint.mem_graph_iff'.mp hp
  have hwH : ∀ x : S.domain, ⟪realShift S c x, (y : H)⟫_ℂ =
      ⟪(x : H), (realShift S c).adjoint y⟫_ℂ :=
    fun x => adjoint_pairing (realShift S c) hD x y
  have hwS := (realShift_witness_iff S c (y : H) ((realShift S c).adjoint y)).mp hwH
  have hySad := adjoint_mem_of_witness S hwS
  have hval := adjoint_eq_of_witness S hS.1 ⟨(y : H), hySad⟩ hwS
  obtain ⟨v, hv, hSv⟩ := LinearPMap.exists_of_le (le_of_eq hS.2) ⟨(y : H), hySad⟩
  rw [← hy]
  apply (realShift S c).mem_graph_iff.mpr
  refine ⟨v, hv.symm, ?_⟩
  change S v - (c : ℂ) • (v : H) = (realShift S c).adjoint y
  rw [← hSv, hval, ← hv]
  module

lemma inverseOperator_shift_core (R : H →L[ℂ] H) (hR : Function.Injective R) (hs : R.adjoint = R)
    (c : ℝ) (C : Submodule ℂ H) (hC : Dense (C : Set H)) :
    (realShift (inverseOperator R hR) c).HasCore (C.map R.toLinearMap) := by
  have hclosed := realShift_closed (inverseOperator R hR) (inverseOperator_closed R hR) c
  have hsym := realShift_symmetric (inverseOperator R hR) (inverseOperator_symmetric R hR hs) c
  let L : H →L[ℂ] H := ContinuousLinearMap.id ℂ H - (c : ℂ) • R
  have hc := symmetric_closure_hasCore (realShift (inverseOperator R hR) c)
    (inverseOperator_dense R hR hs) hsym R L rfl
    (fun f => ⟨⟨R f, LinearMap.mem_range_self R.toLinearMap f⟩, rfl, by
      change inverseOperator R hR ⟨R f, _⟩ - (c : ℂ) • R f = f - (c : ℂ) • R f
      rw [inverseOperator_left]⟩) C hC
  rwa [closure_eq_of_closed _ hclosed] at hc

end GW.Operators
