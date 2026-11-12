module
public import GW.Operators.ResolventAlgebra
public import Mathlib.Analysis.SpecificLimits.Normed
/-! Source basic:kato-rellich. The perturbation remains linear on the actual
full domain. Relative resolvent bounds, Neumann inversion and graph norms follow the source. -/
@[expose] public section
noncomputable section
open scoped Topology InnerProductSpace
namespace GW.Operators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The sum acts on exactly the original full domain. B is not assumed ambient bounded. -/
def perturbedOperator (A : H →ₗ.[ℂ] H) (B : A.domain →ₗ[ℂ] H) : H →ₗ.[ℂ] H where
  domain := A.domain
  toFun := A.toFun+B

lemma perturbedOperator_apply (A : H →ₗ.[ℂ] H) (B : A.domain →ₗ[ℂ] H) (u : A.domain) :
    perturbedOperator A B u = A u+B u := rfl

lemma perturbedOperator_symmetric (A : H →ₗ.[ℂ] H) (hA : A.IsFormalAdjoint A)
    (B : A.domain →ₗ[ℂ] H) (hB : ∀ u v : A.domain, ⟪B u,(v : H)⟫_ℂ = ⟪(u : H),B v⟫_ℂ) :
    (perturbedOperator A B).IsFormalAdjoint (perturbedOperator A B) := by
  intro u v
  change ⟪A u+B u,(v : H)⟫_ℂ = ⟪(u : H),A v+B v⟫_ℂ
  rw [inner_add_left,inner_add_right,hA u v,hB u v]

lemma imaginary_shift_norm_sq (A : H →ₗ.[ℂ] H) (hs : A.IsFormalAdjoint A) (t : ℝ) (u : A.domain) :
    ‖complexShift A ((t : ℂ)*Complex.I) u‖ ^ 2 = ‖A u‖ ^ 2+t ^ 2*‖(u : H)‖ ^ 2 := by
  have hi : (⟪A u,(u : H)⟫_ℂ).im = 0 :=
    (congrArg Complex.im (hs u u)).trans (symmetric_diagonal_im_zero A hs u)
  have hc : RCLike.re (⟪A u,((t : ℂ)*Complex.I) • (u : H)⟫_ℂ) = 0 := by
    rw [inner_smul_right]
    change (((t : ℂ)*Complex.I)*⟪A u,(u : H)⟫_ℂ).re = 0
    rw [Complex.mul_re]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
      mul_zero,sub_zero,zero_mul,hi]
  change ‖A u-((t : ℂ)*Complex.I) • (u : H)‖ ^ 2 = _
  rw [norm_sub_sq (𝕜 := ℂ),hc]
  simp only [norm_smul,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,
    mul_pow,sq_abs,mul_zero,sub_zero]

lemma imaginary_nonreal {t : ℝ} (ht : t ≠ 0) : ((t : ℂ)*Complex.I).im ≠ 0 := by simpa using ht

lemma perturbation_upper (A : H →ₗ.[ℂ] H) (B : A.domain →ₗ[ℂ] H) {a b : ℝ}
    (hB : ∀ u, ‖B u‖ ≤ a*‖A u‖+b*‖(u : H)‖) (u : A.domain) :
    ‖perturbedOperator A B u‖ ≤ (1+a)*‖A u‖+b*‖(u : H)‖ := by
  have ht := norm_add_le (A u) (B u)
  have hb := hB u
  change ‖A u+B u‖ ≤ _
  linarith

lemma perturbation_reverse (A : H →ₗ.[ℂ] H) (B : A.domain →ₗ[ℂ] H) {a b : ℝ}
    (hB : ∀ u, ‖B u‖ ≤ a*‖A u‖+b*‖(u : H)‖) (u : A.domain) :
    (1-a)*‖A u‖ ≤ ‖perturbedOperator A B u‖+b*‖(u : H)‖ := by
  have he : A u = perturbedOperator A B u-B u := by change A u = (A u+B u)-B u; abel
  have ht : ‖A u‖ ≤ ‖perturbedOperator A B u‖+‖B u‖ := by
    calc
      ‖A u‖ = ‖perturbedOperator A B u-B u‖ := congrArg norm he
      _ ≤ _ := norm_sub_le _ _
  have hb := hB u
  nlinarith

lemma kato_graph_sum_upper (A : H →ₗ.[ℂ] H) (B : A.domain →ₗ[ℂ] H) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hB : ∀ u, ‖B u‖ ≤ a*‖A u‖+b*‖(u : H)‖) (u : A.domain) :
    ‖(u : H)‖+‖perturbedOperator A B u‖ ≤ (2+a+b)*(‖(u : H)‖+‖A u‖) := by
  have h := perturbation_upper A B hB u
  have h1 := mul_nonneg (show 0 ≤ 1+a by linarith) (norm_nonneg (u : H))
  have h2 := mul_nonneg (show 0 ≤ 1+b by linarith) (norm_nonneg (A u))
  nlinarith

lemma kato_graph_sum_reverse (A : H →ₗ.[ℂ] H) (B : A.domain →ₗ[ℂ] H) {a b : ℝ}
    (ha1 : a < 1) (hb : 0 ≤ b) (hB : ∀ u, ‖B u‖ ≤ a*‖A u‖+b*‖(u : H)‖) (u : A.domain) :
    ‖(u : H)‖+‖A u‖ ≤ (1+(1+b)/(1-a))*(‖(u : H)‖+‖perturbedOperator A B u‖) := by
  have hc : 0 < 1-a := sub_pos.mpr ha1
  have he : 1+(1+b)/(1-a) = (2-a+b)/(1-a) := by field_simp [ne_of_gt hc]; ring
  rw [he,div_mul_eq_mul_div]
  apply (le_div_iff₀ hc).mpr
  have h := perturbation_reverse A B hB u
  have hrest := mul_nonneg (show 0 ≤ 1-a+b by linarith) (norm_nonneg (perturbedOperator A B u))
  nlinarith [norm_nonneg (u : H)]

lemma graph_sum_le_sqrt_two (A : H →ₗ.[ℂ] H) (hA : A.IsClosed) (v : GraphDomain A hA) :
    ‖graphInclusion A hA v‖+‖graphAction A hA v‖ ≤ Real.sqrt 2*‖v‖ := by
  have hsq := graphDomain_norm_sq A hA v
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hm := congrArg (fun r : ℝ => r*‖v‖ ^ 2) hsqrt
  have hdiff := sq_nonneg (‖graphInclusion A hA v‖-‖graphAction A hA v‖)
  have hsum : 0 ≤ ‖graphInclusion A hA v‖+‖graphAction A hA v‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hp : 0 ≤ Real.sqrt 2*‖v‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have he : (‖graphInclusion A hA v‖+‖graphAction A hA v‖) ^ 2 ≤ (Real.sqrt 2*‖v‖) ^ 2 := by nlinarith
  exact (sq_le_sq₀ hsum hp).mp he

def perturbGraphEquiv (A : H →ₗ.[ℂ] H) (B : A.domain →ₗ[ℂ] H) (hA : A.IsClosed)
    (hS : (perturbedOperator A B).IsClosed) :
    GraphDomain A hA ≃ₗ[ℂ] GraphDomain (perturbedOperator A B) hS :=
  (graphDomainEquiv A hA).symm.trans (graphDomainEquiv (perturbedOperator A B) hS)

lemma perturbGraphEquiv_lift (A : H →ₗ.[ℂ] H) (B : A.domain →ₗ[ℂ] H) (hA : A.IsClosed)
    (hS : (perturbedOperator A B).IsClosed) (u : A.domain) :
    perturbGraphEquiv A B hA hS (graphLift A hA u) = graphLift (perturbedOperator A B) hS u := by
  change (graphDomainEquiv (perturbedOperator A B) hS)
    ((graphDomainEquiv A hA).symm ((graphDomainEquiv A hA) u)) =
      (graphDomainEquiv (perturbedOperator A B) hS) u
  rw [LinearEquiv.symm_apply_apply]

lemma perturbGraphEquiv_inclusion (A : H →ₗ.[ℂ] H) (B : A.domain →ₗ[ℂ] H) (hA : A.IsClosed)
    (hS : (perturbedOperator A B).IsClosed) (v : GraphDomain A hA) :
    graphInclusion (perturbedOperator A B) hS (perturbGraphEquiv A B hA hS v) = graphInclusion A hA v := by
  change ((graphDomainEquiv A hA).symm v : H) = graphInclusion A hA v
  exact congrArg (graphInclusion A hA) ((graphDomainEquiv A hA).apply_symm_apply v)

lemma perturbGraphEquiv_symm_inclusion (A : H →ₗ.[ℂ] H) (B : A.domain →ₗ[ℂ] H) (hA : A.IsClosed)
    (hS : (perturbedOperator A B).IsClosed) (v : GraphDomain (perturbedOperator A B) hS) :
    graphInclusion A hA ((perturbGraphEquiv A B hA hS).symm v) = graphInclusion (perturbedOperator A B) hS v := by
  have he := perturbGraphEquiv_inclusion A B hA hS ((perturbGraphEquiv A B hA hS).symm v)
  rw [LinearEquiv.apply_symm_apply] at he
  exact he.symm

lemma perturbGraphEquiv_bound (A : H →ₗ.[ℂ] H) (B : A.domain →ₗ[ℂ] H) (hA : A.IsClosed)
    (hS : (perturbedOperator A B).IsClosed) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hB : ∀ u, ‖B u‖ ≤ a*‖A u‖+b*‖(u : H)‖) (v : GraphDomain A hA) :
    ‖perturbGraphEquiv A B hA hS v‖ ≤ ((2+a+b)*Real.sqrt 2)*‖v‖ := by
  let u := (graphDomainEquiv A hA).symm v
  have hv : graphLift A hA u = v := (graphDomainEquiv A hA).apply_symm_apply v
  have he : perturbGraphEquiv A B hA hS v = graphLift (perturbedOperator A B) hS u := rfl
  have hC : 0 ≤ 2+a+b := by linarith
  calc
    ‖perturbGraphEquiv A B hA hS v‖ = ‖graphLift (perturbedOperator A B) hS u‖ := congrArg norm he
    _ ≤ ‖(u : H)‖+‖perturbedOperator A B u‖ := graph_norm_le_sum _ hS _
    _ ≤ (2+a+b)*(‖(u : H)‖+‖A u‖) := kato_graph_sum_upper A B ha hb hB u
    _ ≤ (2+a+b)*(Real.sqrt 2*‖graphLift A hA u‖) :=
      mul_le_mul_of_nonneg_left (graph_sum_le_sqrt_two A hA (graphLift A hA u)) hC
    _ = ((2+a+b)*Real.sqrt 2)*‖v‖ := by rw [hv]; ring

lemma perturbGraphEquiv_inverse_bound (A : H →ₗ.[ℂ] H) (B : A.domain →ₗ[ℂ] H) (hA : A.IsClosed)
    (hS : (perturbedOperator A B).IsClosed) {a b : ℝ} (ha1 : a < 1) (hb : 0 ≤ b)
    (hB : ∀ u, ‖B u‖ ≤ a*‖A u‖+b*‖(u : H)‖) (v : GraphDomain (perturbedOperator A B) hS) :
    ‖(perturbGraphEquiv A B hA hS).symm v‖ ≤ ((1+(1+b)/(1-a))*Real.sqrt 2)*‖v‖ := by
  let u : A.domain := (graphDomainEquiv (perturbedOperator A B) hS).symm v
  have hv : graphLift (perturbedOperator A B) hS u = v :=
    (graphDomainEquiv (perturbedOperator A B) hS).apply_symm_apply v
  have he : (perturbGraphEquiv A B hA hS).symm v = graphLift A hA u := by
    apply (perturbGraphEquiv A B hA hS).injective
    rw [LinearEquiv.apply_symm_apply,perturbGraphEquiv_lift]
    exact hv.symm
  have hc : 0 < 1-a := sub_pos.mpr ha1
  have hC : 0 ≤ 1+(1+b)/(1-a) := by positivity
  calc
    ‖(perturbGraphEquiv A B hA hS).symm v‖ = ‖graphLift A hA u‖ := congrArg norm he
    _ ≤ ‖(u : H)‖+‖A u‖ := graph_norm_le_sum _ hA _
    _ ≤ (1+(1+b)/(1-a))*(‖(u : H)‖+‖perturbedOperator A B u‖) := kato_graph_sum_reverse A B ha1 hb hB u
    _ ≤ (1+(1+b)/(1-a))*(Real.sqrt 2*‖graphLift (perturbedOperator A B) hS u‖) :=
      mul_le_mul_of_nonneg_left (graph_sum_le_sqrt_two (perturbedOperator A B) hS (graphLift (perturbedOperator A B) hS u)) hC
    _ = ((1+(1+b)/(1-a))*Real.sqrt 2)*‖v‖ := by rw [hv]; ring

/-- Both graph norms are compared on the same underlying operator domain. -/
def perturbGraphHomeomorph (A : H →ₗ.[ℂ] H) (B : A.domain →ₗ[ℂ] H) (hA : A.IsClosed)
    (hS : (perturbedOperator A B).IsClosed) {a b : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b)
    (hB : ∀ u, ‖B u‖ ≤ a*‖A u‖+b*‖(u : H)‖) :
    GraphDomain A hA ≃L[ℂ] GraphDomain (perturbedOperator A B) hS where
  toLinearEquiv := perturbGraphEquiv A B hA hS
  continuous_toFun := ((perturbGraphEquiv A B hA hS).toLinearMap.mkContinuous
    ((2+a+b)*Real.sqrt 2) (perturbGraphEquiv_bound A B hA hS ha hb hB)).continuous
  continuous_invFun := ((perturbGraphEquiv A B hA hS).symm.toLinearMap.mkContinuous
    ((1+(1+b)/(1-a))*Real.sqrt 2) (perturbGraphEquiv_inverse_bound A B hA hS ha1 hb hB)).continuous

lemma perturbation_cores (A : H →ₗ.[ℂ] H) (B : A.domain →ₗ[ℂ] H) (hA : A.IsClosed)
    (hS : (perturbedOperator A B).IsClosed) {a b : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b)
    (hB : ∀ u, ‖B u‖ ≤ a*‖A u‖+b*‖(u : H)‖) (C : Submodule ℂ H) :
    A.HasCore C ↔ (perturbedOperator A B).HasCore C := by
  let W := perturbGraphHomeomorph A B hA hS ha ha1 hb hB
  have hW (v : GraphDomain A hA) : graphInclusion (perturbedOperator A B) hS (W v) = graphInclusion A hA v :=
    perturbGraphEquiv_inclusion A B hA hS v
  have hWi (v : GraphDomain (perturbedOperator A B) hS) : graphInclusion A hA (W.symm v) =
      graphInclusion (perturbedOperator A B) hS v := perturbGraphEquiv_symm_inclusion A B hA hS v
  have hDense : Dense {v : GraphDomain A hA | graphInclusion A hA v ∈ C} ↔
      Dense {v : GraphDomain (perturbedOperator A B) hS | graphInclusion (perturbedOperator A B) hS v ∈ C} := by
    constructor
    · intro hd
      have hp := hd.preimage W.symm.toHomeomorph.isOpenMap
      have heq : W.symm ⁻¹' {v : GraphDomain A hA | graphInclusion A hA v ∈ C} =
          {v | graphInclusion (perturbedOperator A B) hS v ∈ C} := by
        ext v
        change graphInclusion A hA (W.symm v) ∈ C ↔ graphInclusion (perturbedOperator A B) hS v ∈ C
        rw [hWi]
      change Dense (W.symm ⁻¹' {v : GraphDomain A hA | graphInclusion A hA v ∈ C}) at hp
      rwa [heq] at hp
    · intro hd
      have hp := hd.preimage W.toHomeomorph.isOpenMap
      have heq : W ⁻¹' {v | graphInclusion (perturbedOperator A B) hS v ∈ C} =
          {v : GraphDomain A hA | graphInclusion A hA v ∈ C} := by
        ext v
        change graphInclusion (perturbedOperator A B) hS (W v) ∈ C ↔ graphInclusion A hA v ∈ C
        rw [hW]
      change Dense (W ⁻¹' {v | graphInclusion (perturbedOperator A B) hS v ∈ C}) at hp
      rwa [heq] at hp
  constructor
  · intro hc
    apply (hasCore_iff_graph_dense (perturbedOperator A B) hS C hc.le_domain).mpr
    exact hDense.mp ((hasCore_iff_graph_dense A hA C hc.le_domain).mp hc)
  · intro hc
    apply (hasCore_iff_graph_dense A hA C hc.le_domain).mpr
    exact hDense.mpr ((hasCore_iff_graph_dense (perturbedOperator A B) hS C hc.le_domain).mp hc)

variable [CompleteSpace H]

/-- The Neumann inverse is the geometric-series unit of the source proof. -/
lemma neumann_inverse (C : H →L[ℂ] H) (hC : ‖C‖ < 1) :
    ∃ N : H →L[ℂ] H, (1+C).comp N = 1 ∧ N.comp (1+C) = 1 := by
  obtain ⟨u,hu⟩ := isUnit_one_sub_of_norm_lt_one (x := -C) (by simpa only [norm_neg] using hC)
  refine ⟨↑(u⁻¹), ?_, ?_⟩
  · have he := u.mul_inv
    rw [hu,sub_neg_eq_add] at he
    exact he
  · have he := u.inv_mul
    rw [hu,sub_neg_eq_add] at he
    exact he

lemma neumann_surjective (C : H →L[ℂ] H) (hC : ‖C‖ < 1) : Function.Surjective (1+C : H →L[ℂ] H) := by
  obtain ⟨N,hN,_⟩ := neumann_inverse C hC
  intro f
  exact ⟨N f, congrArg (fun L : H →L[ℂ] H => L f) hN⟩

def resolventDomainLinear (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjointOperator A) (z : ℂ) (hz : z.im ≠ 0) :
    H →ₗ[ℂ] A.domain where
  toFun := resolventInput A hA z hz
  map_add' f g := Subtype.ext ((resolvent A hA z hz).map_add f g)
  map_smul' c f := Subtype.ext ((resolvent A hA z hz).map_smul c f)

lemma imaginary_resolvent_action_bound (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjointOperator A)
    {t : ℝ} (ht : t ≠ 0) (f : H) :
    ‖A (resolventInput A hA ((t : ℂ)*Complex.I) (imaginary_nonreal ht) f)‖ ≤ ‖f‖ := by
  have hs : A.IsFormalAdjoint A := by simpa only [hA.2] using LinearPMap.adjoint_isFormalAdjoint hA.1
  have he := imaginary_shift_norm_sq A hs t (resolventInput A hA ((t : ℂ)*Complex.I) (imaginary_nonreal ht) f)
  rw [resolventInput_action] at he
  have hp : 0 ≤ t ^ 2*‖(resolventInput A hA ((t : ℂ)*Complex.I) (imaginary_nonreal ht) f : H)‖ ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  nlinarith [norm_nonneg (A (resolventInput A hA ((t : ℂ)*Complex.I) (imaginary_nonreal ht) f)),norm_nonneg f]

lemma relative_resolvent_bound (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjointOperator A)
    (B : A.domain →ₗ[ℂ] H) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hB : ∀ u, ‖B u‖ ≤ a*‖A u‖+b*‖(u : H)‖) {t : ℝ} (ht : t ≠ 0) (f : H) :
    ‖B (resolventInput A hA ((t : ℂ)*Complex.I) (imaginary_nonreal ht) f)‖ ≤ (a+b/|t|)*‖f‖ := by
  have hs : A.IsFormalAdjoint A := by simpa only [hA.2] using LinearPMap.adjoint_isFormalAdjoint hA.1
  let u := resolventInput A hA ((t : ℂ)*Complex.I) (imaginary_nonreal ht) f
  have hRF : ‖(u : H)‖ ≤ |t|⁻¹*‖f‖ := by
    have h := complexShift_inverse_bound A hs ((t : ℂ)*Complex.I) (imaginary_nonreal ht) u
    change ‖(u : H)‖ ≤ |((t : ℂ)*Complex.I).im|⁻¹*‖complexShift A ((t : ℂ)*Complex.I) u‖ at h
    rw [resolventInput_action] at h
    simpa using h
  calc
    ‖B u‖ ≤ a*‖A u‖+b*‖(u : H)‖ := hB u
    _ ≤ a*‖f‖+b*(|t|⁻¹*‖f‖) := add_le_add
      (mul_le_mul_of_nonneg_left (imaginary_resolvent_action_bound A hA ht f) ha)
      (mul_le_mul_of_nonneg_left hRF hb)
    _ = (a+b/|t|)*‖f‖ := by ring
/-- The full-domain product B(A-it)⁻¹ is constructed from its proved bound. -/
def relativeResolvent (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjointOperator A)
    (B : A.domain →ₗ[ℂ] H) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hB : ∀ u, ‖B u‖ ≤ a*‖A u‖+b*‖(u : H)‖) {t : ℝ} (ht : t ≠ 0) : H →L[ℂ] H :=
  (B.comp (resolventDomainLinear A hA ((t : ℂ)*Complex.I) (imaginary_nonreal ht))).mkContinuous
    (a+b/|t|) (relative_resolvent_bound A hA B ha hb hB ht)

lemma relativeResolvent_apply (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjointOperator A)
    (B : A.domain →ₗ[ℂ] H) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hB : ∀ u, ‖B u‖ ≤ a*‖A u‖+b*‖(u : H)‖) {t : ℝ} (ht : t ≠ 0) (f : H) :
    relativeResolvent A hA B ha hb hB ht f =
      B (resolventInput A hA ((t : ℂ)*Complex.I) (imaginary_nonreal ht) f) := rfl

lemma relativeResolvent_norm_le (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjointOperator A)
    (B : A.domain →ₗ[ℂ] H) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hB : ∀ u, ‖B u‖ ≤ a*‖A u‖+b*‖(u : H)‖) {t : ℝ} (ht : t ≠ 0) :
    ‖relativeResolvent A hA B ha hb hB ht‖ ≤ a+b/|t| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact relative_resolvent_bound A hA B ha hb hB ht

lemma resolventInput_right (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjointOperator A) (z : ℂ) (hz : z.im ≠ 0)
    (u : A.domain) : resolventInput A hA z hz (complexShift A z u) = u :=
  Subtype.ext (resolvent_right_inverse A hA z hz u)

lemma perturbed_factorization (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjointOperator A)
    (B : A.domain →ₗ[ℂ] H) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hB : ∀ u, ‖B u‖ ≤ a*‖A u‖+b*‖(u : H)‖) {t : ℝ} (ht : t ≠ 0) (u : A.domain) :
    complexShift (perturbedOperator A B) ((t : ℂ)*Complex.I) u =
      (1+relativeResolvent A hA B ha hb hB ht : H →L[ℂ] H) (complexShift A ((t : ℂ)*Complex.I) u) := by
  change (A u+B u)-((t : ℂ)*Complex.I) • (u : H) =
    complexShift A ((t : ℂ)*Complex.I) u+B (resolventInput A hA ((t : ℂ)*Complex.I)
      (imaginary_nonreal ht) (complexShift A ((t : ℂ)*Complex.I) u))
  rw [resolventInput_right]
  change (A u+B u)-((t : ℂ)*Complex.I) • (u : H) = A u-((t : ℂ)*Complex.I) • (u : H)+B u
  abel

lemma perturbed_shift_surjective (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjointOperator A)
    (B : A.domain →ₗ[ℂ] H) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hB : ∀ u, ‖B u‖ ≤ a*‖A u‖+b*‖(u : H)‖) {t : ℝ} (ht : t ≠ 0)
    (hsmall : a+b/|t| < 1) : Function.Surjective (complexShift (perturbedOperator A B) ((t : ℂ)*Complex.I)) := by
  have hnorm := (relativeResolvent_norm_le A hA B ha hb hB ht).trans_lt hsmall
  intro f
  obtain ⟨g,hg⟩ := neumann_surjective (relativeResolvent A hA B ha hb hB ht) hnorm f
  refine ⟨resolventInput A hA ((t : ℂ)*Complex.I) (imaginary_nonreal ht) g, ?_⟩
  rw [perturbed_factorization A hA B ha hb hB ht, resolventInput_action]
  exact hg

lemma kato_parameter {a b : ℝ} (ha : a < 1) (hb : 0 ≤ b) :
    0 < b/(1-a)+1 ∧ a+b/(b/(1-a)+1) < 1 := by
  have hc : 0 < 1-a := sub_pos.mpr ha
  let t := b/(1-a)+1
  have ht : 0 < t := by dsimp [t]; positivity
  have he : (1-a)*t = b+(1-a) := by dsimp [t]; field_simp [ne_of_gt hc]
  have hh : b/t < 1-a := (div_lt_iff₀ ht).mpr (by nlinarith)
  exact ⟨ht, by change a+b/t < 1; linarith⟩

lemma kato_rellich_selfadjoint (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjointOperator A)
    (B : A.domain →ₗ[ℂ] H) (hSym : ∀ u v : A.domain, ⟪B u,(v : H)⟫_ℂ = ⟪(u : H),B v⟫_ℂ)
    {a b : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b)
    (hB : ∀ u, ‖B u‖ ≤ a*‖A u‖+b*‖(u : H)‖) : IsSelfAdjointOperator (perturbedOperator A B) := by
  have hs : A.IsFormalAdjoint A := by simpa only [hA.2] using LinearPMap.adjoint_isFormalAdjoint hA.1
  let t := b/(1-a)+1
  have ht : 0 < t := (kato_parameter ha1 hb).1
  have hsmall : a+b/|t| < 1 := by rw [abs_of_pos ht]; exact (kato_parameter ha1 hb).2
  apply selfadjoint_of_imaginary_ranges (perturbedOperator A B) hA.1 (perturbedOperator_symmetric A hs B hSym) ht
  · exact perturbed_shift_surjective A hA B ha hb hB ht.ne' hsmall
  · have hm := perturbed_shift_surjective A hA B ha hb hB (neg_ne_zero.mpr ht.ne')
      (by simpa only [abs_neg] using hsmall : a+b/|-t| < 1)
    have he : (((-t : ℝ) : ℂ)*Complex.I) = -((t : ℂ)*Complex.I) := by push_cast; ring
    change Function.Surjective (complexShift (perturbedOperator A B) (((-t : ℝ) : ℂ)*Complex.I)) at hm
    rw [he] at hm
    exact hm

/-- The actual complete graph carriers are linearly homeomorphic by the identity on H. -/
def kato_graph_equiv (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjointOperator A)
    (B : A.domain →ₗ[ℂ] H) (hSym : ∀ u v : A.domain, ⟪B u,(v : H)⟫_ℂ = ⟪(u : H),B v⟫_ℂ)
    {a b : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b)
    (hB : ∀ u, ‖B u‖ ≤ a*‖A u‖+b*‖(u : H)‖) :
    GraphDomain A (selfadjoint_closed A hA) ≃L[ℂ]
      GraphDomain (perturbedOperator A B)
        (selfadjoint_closed _ (kato_rellich_selfadjoint A hA B hSym ha ha1 hb hB)) :=
  perturbGraphHomeomorph A B (selfadjoint_closed A hA)
    (selfadjoint_closed _ (kato_rellich_selfadjoint A hA B hSym ha ha1 hb hB)) ha ha1 hb hB

lemma kato_rellich_core_iff (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjointOperator A)
    (B : A.domain →ₗ[ℂ] H) (hSym : ∀ u v : A.domain, ⟪B u,(v : H)⟫_ℂ = ⟪(u : H),B v⟫_ℂ)
    {a b : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b)
    (hB : ∀ u, ‖B u‖ ≤ a*‖A u‖+b*‖(u : H)‖) (C : Submodule ℂ H) :
    A.HasCore C ↔ (perturbedOperator A B).HasCore C :=
  perturbation_cores A B (selfadjoint_closed A hA)
    (selfadjoint_closed _ (kato_rellich_selfadjoint A hA B hSym ha ha1 hb hB)) ha ha1 hb hB C

lemma kato_rellich (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjointOperator A)
    (B : A.domain →ₗ[ℂ] H) (hSym : ∀ u v : A.domain, ⟪B u,(v : H)⟫_ℂ = ⟪(u : H),B v⟫_ℂ)
    {a b : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b)
    (hB : ∀ u, ‖B u‖ ≤ a*‖A u‖+b*‖(u : H)‖) :
    IsSelfAdjointOperator (perturbedOperator A B) ∧
      (∀ u : A.domain, ‖(u : H)‖+‖perturbedOperator A B u‖ ≤ (2+a+b)*(‖(u : H)‖+‖A u‖) ∧
        ‖(u : H)‖+‖A u‖ ≤ (1+(1+b)/(1-a))*(‖(u : H)‖+‖perturbedOperator A B u‖)) ∧
      (∀ C : Submodule ℂ H, A.HasCore C ↔ (perturbedOperator A B).HasCore C) :=
  ⟨kato_rellich_selfadjoint A hA B hSym ha ha1 hb hB,
    fun u => ⟨kato_graph_sum_upper A B ha hb hB u,kato_graph_sum_reverse A B ha1 hb hB u⟩,
    kato_rellich_core_iff A hA B hSym ha ha1 hb hB⟩

end GW.Operators
