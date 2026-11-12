module
public import GW.Fock.FockNumberConjugation
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal
namespace GW.Fock

set_option backward.isDefEq.respectTransparency.types false in
def weylWeightedInput (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (f : OneBoson)
    (u : NumberWeightedDomain Sector σ hσ₀) : NumberWeightedDomain Sector σ hσ₀ :=
  show (shiftedNumberPower Sector σ).domain from
  ⟨weylUnitary f (numberDomainEmbedding σ hσ₀ u),by
    apply (weyl_shifted_fractional_bound f σ hσ₀ hσ₁
      ⟨numberDomainEmbedding σ hσ₀ u,by
        rw [numberDomainEmbedding_apply]
        exact (show (shiftedNumberPower Sector σ).domain from u).property⟩).choose⟩

lemma weylWeightedInput_embedding (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (f : OneBoson)
    (u : NumberWeightedDomain Sector σ hσ₀) :
    numberDomainEmbedding σ hσ₀ (weylWeightedInput σ hσ₀ hσ₁ f u) =
      weylUnitary f (numberDomainEmbedding σ hσ₀ u) := by
  rw [numberDomainEmbedding_apply]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
lemma weylWeightedInput_norm (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (f : OneBoson)
    (u : NumberWeightedDomain Sector σ hσ₀) :
    ‖weylWeightedInput σ hσ₀ hσ₁ f u‖ ≤ (1+‖f‖)^(2*σ)*‖u‖ := by
  have h := (weyl_shifted_fractional_bound f σ hσ₀ hσ₁
    ⟨numberDomainEmbedding σ hσ₀ u,by
      rw [numberDomainEmbedding_apply]
      exact (show (shiftedNumberPower Sector σ).domain from u).property⟩).choose_spec
  change ‖shiftedNumberPower Sector σ (weylWeightedInput σ hσ₀ hσ₁ f u)‖ ≤
    (1+‖f‖)^(2*σ)*‖shiftedNumberPower Sector σ u‖
  convert! h using 1
  congr 1
  apply congrArg norm
  congr 1
  exact Subtype.ext (numberDomainEmbedding_apply σ hσ₀ u).symm

def weylWeightedLinear (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (f : OneBoson) :
    NumberWeightedDomain Sector σ hσ₀ →ₗ[ℂ] NumberWeightedDomain Sector σ hσ₀ where
  toFun := weylWeightedInput σ hσ₀ hσ₁ f
  map_add' u v := by
    apply Subtype.ext
    change weylUnitary f (numberDomainEmbedding σ hσ₀ (u+v)) =
      weylUnitary f (numberDomainEmbedding σ hσ₀ u)+weylUnitary f (numberDomainEmbedding σ hσ₀ v)
    rw [map_add,map_add]
  map_smul' c u := by
    apply Subtype.ext
    change weylUnitary f (numberDomainEmbedding σ hσ₀ (c • u)) =
      c • weylUnitary f (numberDomainEmbedding σ hσ₀ u)
    rw [map_smul,map_smul]

def weylWeightedMap (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (f : OneBoson) :
    NumberWeightedDomain Sector σ hσ₀ →L[ℂ] NumberWeightedDomain Sector σ hσ₀ :=
  (weylWeightedLinear σ hσ₀ hσ₁ f).mkContinuous ((1+‖f‖)^(2*σ))
    (weylWeightedInput_norm σ hσ₀ hσ₁ f)

lemma weylWeightedMap_coherent (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (f g : OneBoson) :
    weylWeightedMap σ hσ₀ hσ₁ f (coherentExponentialWeighted σ hσ₀ g) =
      weylCoefficient f g • coherentExponentialWeighted σ hσ₀ (g+f) := by
  apply Subtype.ext
  change weylUnitary f (numberDomainEmbedding σ hσ₀ (coherentExponentialWeighted σ hσ₀ g)) = _
  rw [numberDomainEmbedding_apply,coherentExponentialWeighted_ambient]
  rw [weylUnitary_exponential]
  change weylCoefficient f g • exponentialVector (g+f) =
    weylCoefficient f g • ((numberWeightedGraph Sector σ hσ₀).domain.subtype
      (coherentExponentialWeighted σ hσ₀ (g+f)))
  rw [coherentExponentialWeighted_ambient]

lemma weylWeightedMap_coherent_continuous (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (g : OneBoson) :
    Continuous (fun f => weylWeightedMap σ hσ₀ hσ₁ f (coherentExponentialWeighted σ hσ₀ g)) := by
  simp only [weylWeightedMap_coherent]
  have hc : Continuous (fun f => weylCoefficient f g) := by
    unfold weylCoefficient
    fun_prop
  exact hc.smul (((coherentExponentialWeighted_contDiff 0 σ hσ₀).continuous).comp
    (continuous_const.add continuous_id))


def weylWeightedCore (σ : ℝ) (hσ₀ : 0 ≤ σ) : Submodule ℂ (NumberWeightedDomain Sector σ hσ₀) :=
  Submodule.span ℂ (Set.range (fun g : (⊤ : Submodule ℂ OneBoson) => coherentExponentialWeighted σ hσ₀ g))

lemma weylWeightedCore_dense (σ : ℝ) (hσ₀ : 0 ≤ σ) :
    Dense (weylWeightedCore σ hσ₀ : Set (NumberWeightedDomain Sector σ hσ₀)) :=
  coherentExponentialWeighted_graph_total σ hσ₀ ⊤ (by simp)

lemma weylWeightedMap_span_continuous (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1)
    (u : NumberWeightedDomain Sector σ hσ₀) (hu : u ∈ weylWeightedCore σ hσ₀) :
    Continuous (fun f => weylWeightedMap σ hσ₀ hσ₁ f u) := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g,rfl⟩ := hx
    exact weylWeightedMap_coherent_continuous σ hσ₀ hσ₁ g
  | zero =>
    simp only [map_zero]
    exact continuous_const
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using ihx.fun_add ihy
  | smul a x hx ih =>
    simpa only [map_smul] using ih.fun_const_smul a

lemma weylWeightedMap_local_bound (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1)
    (f₀ f : OneBoson) (hf : dist f f₀ < 1) (u : NumberWeightedDomain Sector σ hσ₀) :
    ‖weylWeightedMap σ hσ₀ hσ₁ f u‖ ≤ (2+‖f₀‖)^2*‖u‖ := by
  have hn : ‖f‖ ≤ 1+‖f₀‖ := by
    have hd := norm_add_le (f-f₀) f₀
    rw [sub_add_cancel,← dist_eq_norm] at hd
    linarith
  have he := Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg f] : (1:ℝ) ≤ 1+‖f‖)
    (by linarith : 2*σ ≤ (2:ℝ))
  rw [Real.rpow_two] at he
  have hs : (1+‖f‖)^2 ≤ (2+‖f₀‖)^2 := by nlinarith [norm_nonneg f,norm_nonneg f₀]
  exact (weylWeightedInput_norm σ hσ₀ hσ₁ f u).trans
    (mul_le_mul_of_nonneg_right (he.trans hs) (norm_nonneg u))

lemma weylWeightedMap_dist_bound (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1)
    (f₀ f : OneBoson) (hf : dist f f₀ < 1) (u v : NumberWeightedDomain Sector σ hσ₀) :
    dist (weylWeightedMap σ hσ₀ hσ₁ f u) (weylWeightedMap σ hσ₀ hσ₁ f v) ≤
      (2+‖f₀‖)^2*dist u v := by
  simpa only [dist_eq_norm,map_sub] using weylWeightedMap_local_bound σ hσ₀ hσ₁ f₀ f hf (u-v)

lemma weylWeightedMap_strong_continuous (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1)
    (u : NumberWeightedDomain Sector σ hσ₀) : Continuous (fun f => weylWeightedMap σ hσ₀ hσ₁ f u) := by
  apply continuous_iff_continuousAt.mpr
  intro f₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  let K : ℝ := (2+‖f₀‖)^2
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨v,hv,huv⟩ := (weylWeightedCore_dense σ hσ₀).exists_dist_lt u
    (div_pos hε (by positivity : 0 < 4*K))
  obtain ⟨δ,hδ,hd⟩ := Metric.continuousAt_iff.mp
    (weylWeightedMap_span_continuous σ hσ₀ hσ₁ v hv).continuousAt
    (ε/2) (by linarith)
  refine ⟨min 1 δ,lt_min zero_lt_one hδ,?_⟩
  intro f hf
  have hf₁ := lt_of_lt_of_le hf (min_le_left 1 δ)
  have hmid := hd (lt_of_lt_of_le hf (min_le_right 1 δ))
  have hleft := weylWeightedMap_dist_bound σ hσ₀ hσ₁ f₀ f hf₁ u v
  have hright := weylWeightedMap_dist_bound σ hσ₀ hσ₁ f₀ f₀ (by simp) v u
  rw [dist_comm v u] at hright
  have htri := dist_triangle (weylWeightedMap σ hσ₀ hσ₁ f u)
    (weylWeightedMap σ hσ₀ hσ₁ f v) (weylWeightedMap σ hσ₀ hσ₁ f₀ u)
  have htri₂ := dist_triangle (weylWeightedMap σ hσ₀ hσ₁ f v)
    (weylWeightedMap σ hσ₀ hσ₁ f₀ v) (weylWeightedMap σ hσ₀ hσ₁ f₀ u)
  have happ : K*dist u v < ε/4 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 4*K)).mp huv
    nlinarith
  change _ ≤ K*dist u v at hleft hright
  linarith

lemma weylWeightedMap_joint_continuous (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) :
    Continuous (fun p : OneBoson × NumberWeightedDomain Sector σ hσ₀ =>
      weylWeightedMap σ hσ₀ hσ₁ p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  let K : ℝ := (2+‖p₀.1‖)^2
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨δ,hδ,hd⟩ := Metric.continuousAt_iff.mp
    (weylWeightedMap_strong_continuous σ hσ₀ hσ₁ p₀.2).continuousAt
    (ε/2) (by linarith)
  refine ⟨min (min 1 δ) (ε/(2*K)),lt_min (lt_min zero_lt_one hδ) (div_pos hε (by positivity)),?_⟩
  intro p hp
  rw [Prod.dist_eq,max_lt_iff] at hp
  have hf := hp.1
  have hu := hp.2
  have hf₁ : dist p.1 p₀.1 < 1 := lt_of_lt_of_le hf ((min_le_left _ _).trans (min_le_left _ _))
  have hfδ : dist p.1 p₀.1 < δ := lt_of_lt_of_le hf ((min_le_left _ _).trans (min_le_right _ _))
  have huε : dist p.2 p₀.2 < ε/(2*K) := lt_of_lt_of_le hu (min_le_right _ _)
  have hb := weylWeightedMap_dist_bound σ hσ₀ hσ₁ p₀.1 p.1 hf₁ p.2 p₀.2
  have hm := hd hfδ
  have ht := dist_triangle (weylWeightedMap σ hσ₀ hσ₁ p.1 p.2)
    (weylWeightedMap σ hσ₀ hσ₁ p.1 p₀.2) (weylWeightedMap σ hσ₀ hσ₁ p₀.1 p₀.2)
  have he : K*dist p.2 p₀.2 < ε/2 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 2*K)).mp huε
    nlinarith
  change _ ≤ K*dist p.2 p₀.2 at hb
  linarith

end GW.Fock
