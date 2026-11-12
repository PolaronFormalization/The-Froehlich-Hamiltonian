module
public import GW.Operators.InverseOperator
public import Mathlib.Tactic
/-! Source basic:selfadjoint-criterion. Adjoint graphs and scalar shifts retain
actual domains. Nonreal resolvents are constructed from proved graph-map bijections. -/
@[expose] public section
noncomputable section
open scoped Topology InnerProductSpace
namespace GW.Operators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma selfadjoint_dense (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjointOperator T) :
    Dense (T.domain : Set H) := hT.1

lemma adjoint_graph_iff (T : H →ₗ.[ℂ] H) (hd : Dense (T.domain : Set H)) (p : H × H) :
    p ∈ T.adjoint.graph ↔ ∀ x : T.domain, ⟪T x, p.1⟫_ℂ = ⟪(x : H), p.2⟫_ℂ := by
  constructor
  · intro hp
    obtain ⟨y, hy⟩ := T.adjoint.mem_graph_iff'.mp hp
    rw [← hy]
    exact fun x => adjoint_pairing T hd x y
  · intro hp
    have hy := adjoint_mem_of_witness T hp
    exact T.adjoint.mem_graph_iff.mpr
      ⟨⟨p.1, hy⟩, rfl, adjoint_eq_of_witness T hd ⟨p.1,hy⟩ hp⟩

lemma adjoint_closed (T : H →ₗ.[ℂ] H) (hd : Dense (T.domain : Set H)) : T.adjoint.IsClosed := by
  have he : (T.adjoint.graph : Set (H × H)) =
      ⋂ x : T.domain, {p | ⟪T x, p.1⟫_ℂ = ⟪(x : H), p.2⟫_ℂ} := by
    ext p
    simpa only [SetLike.mem_coe, Set.mem_iInter, Set.mem_ofPred_eq] using adjoint_graph_iff T hd p
  change IsClosed (T.adjoint.graph : Set (H × H))
  rw [he]
  exact isClosed_iInter (fun x => isClosed_eq
    (continuous_const.inner continuous_fst) (continuous_const.inner continuous_snd))

lemma selfadjoint_closed (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjointOperator T) : T.IsClosed := by
  have hc := adjoint_closed T hT.1
  rwa [hT.2] at hc

omit [CompleteSpace H] in
lemma complexShift_witness_iff (T : H →ₗ.[ℂ] H) (z : ℂ) (y h : H) :
    (∀ x : T.domain, ⟪complexShift T z x, y⟫_ℂ = ⟪(x : H), h⟫_ℂ) ↔
    (∀ x : T.domain, ⟪T x, y⟫_ℂ = ⟪(x : H), h + ((starRingEnd ℂ) z) • y⟫_ℂ) := by
  simp only [complexShift_apply, inner_sub_left, inner_smul_left, inner_add_right, inner_smul_right]
  constructor
  · intro hw x
    have hx := hw x
    linear_combination hx
  · intro hw x
    have hx := hw x
    linear_combination hx

omit [CompleteSpace H] in
lemma complexShift_graph_iff (T : H →ₗ.[ℂ] H) (z : ℂ) (p : H × H) :
    p ∈ (complexShift T z).graph ↔ (p.1, p.2 + z • p.1) ∈ T.graph := by
  constructor
  · intro hp
    obtain ⟨u, hu, hval⟩ := (complexShift T z).mem_graph_iff.mp hp
    refine T.mem_graph_iff.mpr ⟨u, hu, ?_⟩
    change T u - z • (u : H) = p.2 at hval
    change T u = p.2 + z • p.1
    rw [← hu]
    exact (sub_eq_iff_eq_add).mp hval
  · intro hp
    obtain ⟨u, hu, hval⟩ := T.mem_graph_iff.mp hp
    refine (complexShift T z).mem_graph_iff.mpr ⟨u, hu, ?_⟩
    change T u - z • (u : H) = p.2
    change (u : H) = p.1 at hu
    change T u = p.2 + z • p.1 at hval
    rw [hval, hu]
    module

lemma complexShift_adjoint (T : H →ₗ.[ℂ] H) (hd : Dense (T.domain : Set H)) (z : ℂ) :
    (complexShift T z).adjoint = complexShift T.adjoint ((starRingEnd ℂ) z) := by
  apply LinearPMap.eq_of_eq_graph
  ext p
  rw [adjoint_graph_iff (complexShift T z) hd, complexShift_graph_iff, adjoint_graph_iff T hd]
  exact complexShift_witness_iff T z p.1 p.2

lemma operator_range_orthogonal (T : H →ₗ.[ℂ] H) (hd : Dense (T.domain : Set H)) :
    T.toFun.rangeᗮ = T.adjoint.ker := by
  ext y
  rw [Submodule.mem_orthogonal]
  constructor
  · intro hy
    have hw : ∀ x : T.domain, ⟪T x,y⟫_ℂ = ⟪(x : H), (0 : H)⟫_ℂ := by
      intro x
      simpa only [inner_zero_right] using hy (T x) (LinearMap.mem_range_self T.toFun x)
    have hmem := adjoint_mem_of_witness T hw
    exact T.adjoint.mem_ker_iff.mpr ⟨⟨y,hmem⟩, rfl, adjoint_eq_of_witness T hd ⟨y,hmem⟩ hw⟩
  · intro hy
    obtain ⟨v, hv, hzero⟩ := T.adjoint.mem_ker_iff.mp hy
    rintro w ⟨x,rfl⟩
    change ⟪T x,y⟫_ℂ = 0
    rw [hv, adjoint_pairing T hd x v, hzero, inner_zero_right]
/-- The source range criterion, with equality of full operator domains. -/
lemma selfadjoint_of_imaginary_ranges (T : H →ₗ.[ℂ] H) (hd : Dense (T.domain : Set H))
    (hs : T.IsFormalAdjoint T) {t : ℝ} (_ht : 0 < t)
    (hminus : Function.Surjective (complexShift T ((t : ℂ) * Complex.I)))
    (hplus : Function.Surjective (complexShift T (-((t : ℂ) * Complex.I)))) :
    IsSelfAdjointOperator T := by
  let z : ℂ := (t : ℂ) * Complex.I
  have hInc : T ≤ T.adjoint := LinearPMap.IsFormalAdjoint.le_adjoint hd hs
  refine ⟨hd, le_antisymm ?_ hInc⟩
  apply LinearPMap.le_of_le_graph
  intro p hp
  obtain ⟨y, hy⟩ := T.adjoint.mem_graph_iff'.mp hp
  obtain ⟨x, hx⟩ := hminus (T.adjoint y - z • (y : H))
  change T x - z • (x : H) = T.adjoint y - z • (y : H) at hx
  let xa : T.adjoint.domain := ⟨(x : H), hInc.1 x.property⟩
  have hxa : T.adjoint xa = T x := (hInc.2 (show (x : H) = (xa : H) from rfl)).symm
  let w : T.adjoint.domain := y - xa
  have hw : complexShift T.adjoint z w = 0 := by
    change T.adjoint (y-xa) - z • ((y : H)-(x : H)) = 0
    rw [T.adjoint.map_sub, hxa]
    have he : (T.adjoint y - z • (y : H)) - (T x - z • (x : H)) = 0 := sub_eq_zero.mpr hx.symm
    convert he using 1; module
  have hz : (starRingEnd ℂ) (-z) = z := by simp [z]
  have horth : (w : H) ∈ (complexShift T (-z)).toFun.rangeᗮ := by
    rw [operator_range_orthogonal (complexShift T (-z)) hd, complexShift_adjoint T hd (-z), hz]
    exact (complexShift T.adjoint z).mem_ker_iff.mpr ⟨w, rfl, hw⟩
  have hrange : (complexShift T (-z)).toFun.range = ⊤ := LinearMap.range_eq_top.mpr hplus
  rw [hrange, Submodule.top_orthogonal_eq_bot] at horth
  have hwzero : (w : H) = 0 := by simpa only [Submodule.mem_bot] using horth
  change (y : H) - (x : H) = 0 at hwzero
  have hyx : (y : H) = (x : H) := sub_eq_zero.mp hwzero
  rw [hyx] at hx
  rw [← hy]
  refine T.mem_graph_iff.mpr ⟨⟨(x : H), x.property⟩, hyx.symm, ?_⟩
  change T x = T.adjoint y
  have he := congrArg (fun a : H => a + z • (x : H)) hx
  simpa only [sub_add_cancel] using he

omit [CompleteSpace H] in
lemma symmetric_diagonal_im_zero (T : H →ₗ.[ℂ] H) (hs : T.IsFormalAdjoint T) (u : T.domain) :
    (⟪(u : H), T u⟫_ℂ).im = 0 := by
  have hc : (starRingEnd ℂ) ⟪(u : H), T u⟫_ℂ = ⟪(u : H), T u⟫_ℂ :=
    (inner_conj_symm (T u) (u : H)).trans (hs u u)
  have hi := congrArg Complex.im hc
  simp only [Complex.conj_im] at hi
  linarith

omit [CompleteSpace H] in
lemma complexShift_inner_im (T : H →ₗ.[ℂ] H) (hs : T.IsFormalAdjoint T) (z : ℂ) (u : T.domain) :
    (⟪(u : H), complexShift T z u⟫_ℂ).im = -z.im * ‖(u : H)‖ ^ 2 := by
  change (⟪(u : H), T u - z • (u : H)⟫_ℂ).im = _
  rw [inner_sub_right, inner_smul_right, Complex.sub_im, symmetric_diagonal_im_zero T hs u]
  have hIm : (⟪(u : H), (u : H)⟫_ℂ).im = 0 := by
    change RCLike.im ⟪(u : H), (u : H)⟫_ℂ = 0
    exact inner_self_im _
  have hRe : (⟪(u : H), (u : H)⟫_ℂ).re = ‖(u : H)‖ ^ 2 := by
    change RCLike.re ⟪(u : H), (u : H)⟫_ℂ = ‖(u : H)‖ ^ 2
    exact inner_self_eq_norm_sq _
  rw [Complex.mul_im, hIm, hRe]
  ring

omit [CompleteSpace H] in
lemma complexShift_norm_lower (T : H →ₗ.[ℂ] H) (hs : T.IsFormalAdjoint T) (z : ℂ) (u : T.domain) :
    |z.im| * ‖(u : H)‖ ≤ ‖complexShift T z u‖ := by
  have h := (Complex.abs_im_le_norm (⟪(u : H), complexShift T z u⟫_ℂ)).trans
    (norm_inner_le_norm (𝕜 := ℂ) (u : H) (complexShift T z u))
  rw [complexShift_inner_im T hs z u] at h
  simp only [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg ‖(u : H)‖)] at h
  by_cases hn : ‖(u : H)‖ = 0
  · simpa only [hn, mul_zero] using norm_nonneg (complexShift T z u)
  · have hp : 0 < ‖(u : H)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    nlinarith

omit [CompleteSpace H] in
lemma complexShift_inverse_bound (T : H →ₗ.[ℂ] H) (hs : T.IsFormalAdjoint T) (z : ℂ)
    (hz : z.im ≠ 0) (u : T.domain) :
    ‖(u : H)‖ ≤ |z.im|⁻¹ * ‖complexShift T z u‖ := by
  have hp : 0 < |z.im| := abs_pos.mpr hz
  have hl := complexShift_norm_lower T hs z u
  have hd : ‖(u : H)‖ ≤ ‖complexShift T z u‖ / |z.im| :=
    (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hl)
  simpa only [div_eq_mul_inv, mul_comm] using hd

/-- The shifted operator is bounded on the specified complete graph carrier. -/
def shiftGraphMap (T : H →ₗ.[ℂ] H) (hT : T.IsClosed) (z : ℂ) : GraphDomain T hT →L[ℂ] H :=
  graphAction T hT - z • graphInclusion T hT

omit [CompleteSpace H] in
lemma shiftGraphMap_inverse_bound (T : H →ₗ.[ℂ] H) (hT : T.IsClosed)
    (hs : T.IsFormalAdjoint T) (z : ℂ) (hz : z.im ≠ 0) (v : GraphDomain T hT) :
    ‖graphInclusion T hT v‖ ≤ |z.im|⁻¹ * ‖shiftGraphMap T hT z v‖ := by
  obtain ⟨u, hu, hau⟩ := graphDomain_mem T hT v
  have h := complexShift_inverse_bound T hs z hz u
  change ‖(u : H)‖ ≤ |z.im|⁻¹ * ‖T u-z • (u : H)‖ at h
  rw [hu, hau] at h
  exact h

omit [CompleteSpace H] in
lemma shiftGraphMap_bound_below (T : H →ₗ.[ℂ] H) (hT : T.IsClosed)
    (hs : T.IsFormalAdjoint T) (z : ℂ) (hz : z.im ≠ 0) (v : GraphDomain T hT) :
    ‖v‖ ≤ (1 + (1+‖z‖) * |z.im|⁻¹) * ‖shiftGraphMap T hT z v‖ := by
  have hI := shiftGraphMap_inverse_bound T hT hs z hz v
  have hA : ‖graphAction T hT v‖ ≤ ‖shiftGraphMap T hT z v‖ + ‖z‖ * ‖graphInclusion T hT v‖ := by
    have he : graphAction T hT v = shiftGraphMap T hT z v + z • graphInclusion T hT v := by
      change graphAction T hT v = graphAction T hT v - z • graphInclusion T hT v + z • graphInclusion T hT v
      module
    calc
      ‖graphAction T hT v‖ = ‖shiftGraphMap T hT z v + z • graphInclusion T hT v‖ := congrArg norm he
      _ ≤ ‖shiftGraphMap T hT z v‖ + ‖z • graphInclusion T hT v‖ := norm_add_le _ _
      _ = _ := by rw [norm_smul]
  have hg := graph_norm_le_sum T hT v
  have hm := mul_le_mul_of_nonneg_left hI (show 0 ≤ 1+‖z‖ by positivity)
  nlinarith

omit [CompleteSpace H] in
lemma shiftGraphMap_range (T : H →ₗ.[ℂ] H) (hT : T.IsClosed) (z : ℂ) :
    (shiftGraphMap T hT z).range = (complexShift T z).toFun.range := by
  ext y
  constructor
  · rintro ⟨v,rfl⟩
    obtain ⟨u, hu, hau⟩ := graphDomain_mem T hT v
    refine ⟨u, ?_⟩
    change T u-z • (u : H) = graphAction T hT v-z • graphInclusion T hT v
    rw [hu,hau]
    rfl
  · rintro ⟨u,rfl⟩
    exact ⟨graphLift T hT u, rfl⟩

lemma complexShift_closed_range (T : H →ₗ.[ℂ] H) (hT : T.IsClosed)
    (hs : T.IsFormalAdjoint T) (z : ℂ) (hz : z.im ≠ 0) :
    IsClosed ((complexShift T z).toFun.range : Set H) := by
  have hK : 0 ≤ 1 + (1+‖z‖) * |z.im|⁻¹ := by positivity
  have ha : AntilipschitzWith ⟨1 + (1+‖z‖) * |z.im|⁻¹, hK⟩ (shiftGraphMap T hT z) :=
    (shiftGraphMap T hT z).antilipschitz_of_bound (shiftGraphMap_bound_below T hT hs z hz)
  rw [← shiftGraphMap_range T hT z]
  exact ha.isClosed_range (shiftGraphMap T hT z).uniformContinuous

omit [CompleteSpace H] in
lemma complexShift_ker_eq_bot (T : H →ₗ.[ℂ] H) (hs : T.IsFormalAdjoint T) (z : ℂ) (hz : z.im ≠ 0) :
    (complexShift T z).ker = ⊥ := by
  apply (complexShift T z).ker_eq_bot'.mpr
  intro u hu
  have h := complexShift_inverse_bound T hs z hz u
  rw [hu, norm_zero, mul_zero] at h
  apply Subtype.ext
  exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))

lemma selfadjoint_shift_surjective (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjointOperator T)
    (z : ℂ) (hz : z.im ≠ 0) : Function.Surjective (complexShift T z) := by
  have hs : T.IsFormalAdjoint T := by simpa only [hT.2] using LinearPMap.adjoint_isFormalAdjoint hT.1
  have hzc : ((starRingEnd ℂ) z).im ≠ 0 := by simpa only [Complex.conj_im, neg_ne_zero] using hz
  have ho : (complexShift T z).toFun.rangeᗮ = ⊥ := by
    rw [operator_range_orthogonal (complexShift T z) hT.1, complexShift_adjoint T hT.1 z, hT.2]
    exact complexShift_ker_eq_bot T hs _ hzc
  have hdense : (complexShift T z).toFun.range.topologicalClosure = ⊤ :=
    (complexShift T z).toFun.range.topologicalClosure_eq_top_iff.mpr ho
  have hc := complexShift_closed_range T (selfadjoint_closed T hT) hs z hz
  rw [hc.submodule_topologicalClosure_eq] at hdense
  exact LinearMap.range_eq_top.mp hdense

lemma shiftGraphMap_bijective (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjointOperator T)
    (z : ℂ) (hz : z.im ≠ 0) : Function.Bijective (shiftGraphMap T (selfadjoint_closed T hT) z) := by
  have hs : T.IsFormalAdjoint T := by simpa only [hT.2] using LinearPMap.adjoint_isFormalAdjoint hT.1
  have hK : 0 ≤ 1 + (1+‖z‖) * |z.im|⁻¹ := by positivity
  have ha : AntilipschitzWith ⟨1 + (1+‖z‖) * |z.im|⁻¹, hK⟩ (shiftGraphMap T (selfadjoint_closed T hT) z) :=
    (shiftGraphMap T (selfadjoint_closed T hT) z).antilipschitz_of_bound
      (shiftGraphMap_bound_below T (selfadjoint_closed T hT) hs z hz)
  refine ⟨ha.injective, ?_⟩
  apply LinearMap.range_eq_top.mp
  rw [shiftGraphMap_range]
  exact LinearMap.range_eq_top.mpr (selfadjoint_shift_surjective T hT z hz)

/-- The inverse graph map is constructed only after bijectivity is proved. -/
def resolventGraph (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjointOperator T) (z : ℂ) (hz : z.im ≠ 0) :
    H →L[ℂ] GraphDomain T (selfadjoint_closed T hT) := by
  let L := shiftGraphMap T (selfadjoint_closed T hT) z
  let e := LinearEquiv.ofBijective L.toLinearMap (shiftGraphMap_bijective T hT z hz)
  have hs : T.IsFormalAdjoint T := by simpa only [hT.2] using LinearPMap.adjoint_isFormalAdjoint hT.1
  refine e.symm.toLinearMap.mkContinuous (1+(1+‖z‖)*|z.im|⁻¹) (fun f => ?_)
  change ‖e.symm f‖ ≤ (1+(1+‖z‖)*|z.im|⁻¹) * ‖f‖
  have h := shiftGraphMap_bound_below T (selfadjoint_closed T hT) hs z hz (e.symm f)
  change ‖e.symm f‖ ≤ (1+(1+‖z‖)*|z.im|⁻¹) * ‖e (e.symm f)‖ at h
  simpa only [e.apply_symm_apply] using h

lemma shiftGraphMap_resolventGraph (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjointOperator T)
    (z : ℂ) (hz : z.im ≠ 0) (f : H) :
    shiftGraphMap T (selfadjoint_closed T hT) z (resolventGraph T hT z hz f) = f := by
  unfold resolventGraph
  exact (LinearEquiv.ofBijective (shiftGraphMap T (selfadjoint_closed T hT) z).toLinearMap
    (shiftGraphMap_bijective T hT z hz)).apply_symm_apply f

lemma resolventGraph_shiftGraphMap (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjointOperator T)
    (z : ℂ) (hz : z.im ≠ 0) (v : GraphDomain T (selfadjoint_closed T hT)) :
    resolventGraph T hT z hz (shiftGraphMap T (selfadjoint_closed T hT) z v) = v := by
  unfold resolventGraph
  exact (LinearEquiv.ofBijective (shiftGraphMap T (selfadjoint_closed T hT) z).toLinearMap
    (shiftGraphMap_bijective T hT z hz)).symm_apply_apply v

/-- The actual bounded ambient resolvent with its graph-domain witness. -/
def resolvent (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjointOperator T) (z : ℂ) (hz : z.im ≠ 0) : H →L[ℂ] H :=
  (graphInclusion T (selfadjoint_closed T hT)).comp (resolventGraph T hT z hz)

lemma resolvent_domain_action (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjointOperator T)
    (z : ℂ) (hz : z.im ≠ 0) (f : H) :
    ∃ u : T.domain, (u : H) = resolvent T hT z hz f ∧ complexShift T z u = f := by
  obtain ⟨u, hu, hau⟩ := graphDomain_mem T (selfadjoint_closed T hT) (resolventGraph T hT z hz f)
  refine ⟨u, hu, ?_⟩
  change T u-z • (u : H) = f
  rw [hu,hau]
  exact shiftGraphMap_resolventGraph T hT z hz f

lemma resolvent_right_inverse (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjointOperator T)
    (z : ℂ) (hz : z.im ≠ 0) (u : T.domain) :
    resolvent T hT z hz (complexShift T z u) = (u : H) := by
  have h := congrArg (graphInclusion T (selfadjoint_closed T hT))
    (resolventGraph_shiftGraphMap T hT z hz (graphLift T (selfadjoint_closed T hT) u))
  exact h

lemma resolvent_norm_le (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjointOperator T) (z : ℂ) (hz : z.im ≠ 0) :
    ‖resolvent T hT z hz‖ ≤ |z.im|⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (abs_nonneg _))
  intro f
  have hs : T.IsFormalAdjoint T := by simpa only [hT.2] using LinearPMap.adjoint_isFormalAdjoint hT.1
  have h := shiftGraphMap_inverse_bound T (selfadjoint_closed T hT) hs z hz (resolventGraph T hT z hz f)
  rw [shiftGraphMap_resolventGraph] at h
  exact h

lemma resolvent_mem_domain (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjointOperator T)
    (z : ℂ) (hz : z.im ≠ 0) (f : H) : resolvent T hT z hz f ∈ T.domain := by
  obtain ⟨u, hu, _⟩ := resolvent_domain_action T hT z hz f
  exact hu ▸ u.property

/-- Canonical domain input for the actual resolvent value. -/
def resolventInput (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjointOperator T)
    (z : ℂ) (hz : z.im ≠ 0) (f : H) : T.domain :=
  ⟨resolvent T hT z hz f, resolvent_mem_domain T hT z hz f⟩

lemma resolventInput_coe (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjointOperator T)
    (z : ℂ) (hz : z.im ≠ 0) (f : H) : (resolventInput T hT z hz f : H) = resolvent T hT z hz f := rfl

lemma resolventInput_action (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjointOperator T)
    (z : ℂ) (hz : z.im ≠ 0) (f : H) : complexShift T z (resolventInput T hT z hz f) = f := by
  obtain ⟨u, hu, hact⟩ := resolvent_domain_action T hT z hz f
  have he : u = resolventInput T hT z hz f := Subtype.ext hu
  rw [← he]
  exact hact

lemma selfadjoint_resolvent (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjointOperator T)
    (z : ℂ) (hz : z.im ≠ 0) :
    ∃ R : H →L[ℂ] H, ‖R‖ ≤ |z.im|⁻¹ ∧
      (∀ f, ∃ u : T.domain, (u : H) = R f ∧ T u-z • (u : H) = f) ∧
      (∀ u : T.domain, R (T u-z • (u : H)) = (u : H)) := by
  refine ⟨resolvent T hT z hz, resolvent_norm_le T hT z hz, ?_, ?_⟩
  · exact resolvent_domain_action T hT z hz
  · exact resolvent_right_inverse T hT z hz

end GW.Operators
