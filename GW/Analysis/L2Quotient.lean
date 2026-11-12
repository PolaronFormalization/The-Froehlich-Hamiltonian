module

public import GW.Conventions
public import Mathlib.Tactic

/-! Source bridge:lp-quotient. The maximal multiplier is a partial map;
its definition does not claim boundedness, density, or self-adjointness. -/
@[expose] public section
noncomputable section
open MeasureTheory
namespace GW.Analysis
variable {K X E : Type*} [RCLike K] [MeasurableSpace X] [NormedAddCommGroup E]
  [NormedSpace K E] {μ : Measure X}

omit [NormedSpace K E] in
lemma l2_class_eq_iff {f g : X → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    hf.toLp f = hg.toLp g ↔ f =ᵐ[μ] g := by
  constructor
  · intro h
    exact hf.coeFn_toLp.symm.trans ((Filter.EventuallyEq.of_eq (congrArg
      (fun u : Lp E 2 μ => (u : X → E)) h)).trans hg.coeFn_toLp)
  · exact hf.toLp_congr hg

/-- Addition descends from representatives to the constructed classes. -/
lemma l2_class_add {f g : X → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (hf.add hg).toLp (f + g) = hf.toLp f + hg.toLp g := hf.toLp_add hg

/-- Scalar multiplication descends with the same scalar field. -/
lemma l2_class_smul (c : K) {f : X → E} (hf : MemLp f 2 μ) :
    (hf.const_smul c).toLp (c • f) = c • hf.toLp f := hf.toLp_const_smul c

/-- The exact domain witnesses are L² output representatives. -/
def multiplierDomain (a : X → K) (μ : Measure X) : Submodule K (Lp E 2 μ) where
  carrier := {u | ∃ v : Lp E 2 μ, (fun x => a x • u x) =ᵐ[μ] v}
  zero_mem' := by
    refine ⟨0, ?_⟩
    filter_upwards [Lp.coeFn_zero (E := E) (p := 2) (μ := μ)] with x hx
    change a x • (0 : Lp E 2 μ) x = (0 : Lp E 2 μ) x
    rw [hx]
    simp
  add_mem' := by
    rintro u v ⟨u', hu⟩ ⟨v', hv⟩
    refine ⟨u' + v', ?_⟩
    filter_upwards [Lp.coeFn_add u v, Lp.coeFn_add u' v', hu, hv] with x hx hy hu hv
    simp only [Pi.add_apply] at hx hy
    rw [hx, smul_add, hu, hv, hy]
  smul_mem' := by
    rintro c u ⟨v, hv⟩
    refine ⟨c • v, ?_⟩
    filter_upwards [Lp.coeFn_smul c u, Lp.coeFn_smul c v, hv] with x hx hy hv
    simp only [Pi.smul_apply] at hx hy
    rw [hx, smul_comm, hv, hy]

lemma mem_multiplierDomain_iff (a : X → K) (u : Lp E 2 μ) :
    u ∈ multiplierDomain a μ ↔ MemLp (fun x => a x • u x) 2 μ := by
  constructor
  · rintro ⟨v, hv⟩
    exact (Lp.memLp v).ae_eq hv.symm
  · intro h
    exact ⟨h.toLp _, h.coeFn_toLp.symm⟩

/-- The output is constructed only on the domain with an existence witness. -/
def multiplierValue (a : X → K) (u : multiplierDomain (E := E) a μ) : Lp E 2 μ :=
  Classical.choose u.property

lemma multiplierValue_ae (a : X → K) (u : multiplierDomain (E := E) a μ) :
    (fun x => a x • (u : Lp E 2 μ) x) =ᵐ[μ] multiplierValue a u :=
  Classical.choose_spec u.property

/-- The maximal product multiplier, with its actual linear domain. -/
def maximalMultiplier (a : X → K) (μ : Measure X) : Lp E 2 μ →ₗ.[K] Lp E 2 μ where
  domain := multiplierDomain a μ
  toFun :=
    { toFun := multiplierValue a
      map_add' := by
        intro u v
        apply Lp.ext
        filter_upwards [multiplierValue_ae a (u + v), multiplierValue_ae a u,
          multiplierValue_ae a v, Lp.coeFn_add (u : Lp E 2 μ) (v : Lp E 2 μ),
          Lp.coeFn_add (multiplierValue a u) (multiplierValue a v)] with x hsum hu hv hin hout
        change a x • ((u : Lp E 2 μ) + (v : Lp E 2 μ)) x = _ at hsum
        simp only [Pi.add_apply] at hin hout
        rw [← hsum, hin, smul_add, hu, hv, hout]
      map_smul' := by
        intro c u
        apply Lp.ext
        filter_upwards [multiplierValue_ae a (c • u), multiplierValue_ae a u,
          Lp.coeFn_smul c (u : Lp E 2 μ),
          Lp.coeFn_smul c (multiplierValue a u)] with x hsum hu hin hout
        change a x • (c • (u : Lp E 2 μ)) x = _ at hsum
        simp only [Pi.smul_apply] at hin hout
        change multiplierValue a (c • u) x = (c • multiplierValue a u) x
        rw [← hsum, hin, smul_comm, hu, hout] }

/-- Domain membership and the output value are distinct, fully specified obligations. -/
lemma maximalMultiplier_eq_iff (a : X → K)
    (u : (maximalMultiplier (E := E) a μ).domain) (v : Lp E 2 μ) :
    maximalMultiplier a μ u = v ↔
      (fun x => a x • (u : Lp E 2 μ) x) =ᵐ[μ] v := by
  constructor
  · intro h
    exact (multiplierValue_ae a u).trans
      (Filter.EventuallyEq.of_eq (congrArg (fun w : Lp E 2 μ => (w : X → E)) h))
  · intro h
    apply Lp.ext
    exact (multiplierValue_ae a u).symm.trans h


/-- The actual maximal multiplier satisfies the source bound on its domain. -/
lemma maximalMultiplier_norm_le (a : X → K) {C : ℝ}
    (hbound : ∀ᵐ x ∂μ, ‖a x‖ ≤ C)
    (u : (maximalMultiplier (E := E) a μ).domain) :
    ‖maximalMultiplier a μ u‖ ≤ C * ‖(u : Lp E 2 μ)‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [multiplierValue_ae a u, hbound] with x hx hb
  change ‖multiplierValue a u x‖ ≤ C * ‖(u : Lp E 2 μ) x‖
  rw [← hx, norm_smul]
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)


/-- Membership is independent of the representative chosen for the input class. -/
lemma multiplier_toLp_domain_iff (a : X → K) {f : X → E} (hf : MemLp f 2 μ) :
    hf.toLp f ∈ multiplierDomain a μ ↔ MemLp (fun x => a x • f x) 2 μ := by
  rw [mem_multiplierDomain_iff]
  apply memLp_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

/-- Any product representative is the actual maximal multiplier output. -/
lemma maximalMultiplier_toLp (a : X → K) {f : X → E} (hf : MemLp f 2 μ)
    (hp : MemLp (fun x => a x • f x) 2 μ) :
    ∃ h : hf.toLp f ∈ multiplierDomain a μ,
      maximalMultiplier a μ ⟨hf.toLp f, h⟩ = hp.toLp _ := by
  have h := (multiplier_toLp_domain_iff a hf).mpr hp
  refine ⟨h, (maximalMultiplier_eq_iff _ _ _).mpr ?_⟩
  filter_upwards [hf.coeFn_toLp, hp.coeFn_toLp] with x hx hy
  rw [hx, hy]

variable [MeasurableSpace K] [BorelSpace K]

/-- A bounded measurable coefficient gives every L² vector a product witness. -/
lemma mem_multiplierDomain_of_bound (a : X → K) (ha : Measurable a)
    {C : ℝ} (hbound : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) (u : Lp E 2 μ) :
    u ∈ multiplierDomain a μ := by
  apply (mem_multiplierDomain_iff a u).mpr
  apply (Lp.memLp u).of_le_mul (c := C) (ha.aestronglyMeasurable.smul
    (Lp.memLp u).aestronglyMeasurable)
  filter_upwards [hbound] with x hx
  change ‖a x • u x‖ ≤ C * ‖u x‖
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg (u x))

/-- The bounded map is the same maximal multiplier evaluated with its witnesses. -/
def boundedMultiplier (a : X → K) (ha : Measurable a) {C : ℝ}
    (hbound : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) : Lp E 2 μ →L[K] Lp E 2 μ := by
  let J : Lp E 2 μ →ₗ[K] (maximalMultiplier (E := E) a μ).domain :=
    { toFun := fun u => ⟨u, mem_multiplierDomain_of_bound a ha hbound u⟩
      map_add' := fun _ _ => Subtype.ext rfl
      map_smul' := fun _ _ => Subtype.ext rfl }
  let L : Lp E 2 μ →ₗ[K] Lp E 2 μ := (maximalMultiplier a μ).toFun.comp J
  exact L.mkContinuous C (fun u => maximalMultiplier_norm_le a hbound (J u))

lemma boundedMultiplier_ae (a : X → K) (ha : Measurable a) {C : ℝ}
    (hbound : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) (u : Lp E 2 μ) :
    (fun x => a x • u x) =ᵐ[μ] boundedMultiplier a ha hbound u :=
  multiplierValue_ae a ⟨u, mem_multiplierDomain_of_bound a ha hbound u⟩

lemma boundedMultiplier_opNorm_le (a : X → K) (ha : Measurable a) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) :
    ‖boundedMultiplier (E := E) a ha hbound‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro u
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [boundedMultiplier_ae a ha hbound u, hbound] with x hx hb
  rw [← hx, norm_smul]
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

omit [MeasurableSpace K] [BorelSpace K]

/-- A.e. strong measurability and square integrability construct the actual class. -/
def l2Class {f : X → E} (hm : AEStronglyMeasurable f μ)
    (hi : Integrable (fun x => ‖f x‖ ^ 2) μ) : Lp E 2 μ :=
  ((memLp_two_iff_integrable_sq_norm hm).mpr hi).toLp f

omit [NormedSpace K E] in
lemma l2Class_ae {f : X → E} (hm : AEStronglyMeasurable f μ)
    (hi : Integrable (fun x => ‖f x‖ ^ 2) μ) :
    l2Class hm hi =ᵐ[μ] f := MemLp.coeFn_toLp _

/-- The representative already attached to an L² element is strongly measurable. -/
lemma l2_rep_stronglyMeasurable (u : Lp E 2 μ) : StronglyMeasurable (u : X → E) :=
  Lp.stronglyMeasurable u

/-- A.e. strong measurability supplies an actual representative with its a.e. identity. -/
lemma l2_strong_representative {f : X → E} (hm : AEStronglyMeasurable f μ) :
    ∃ g : X → E, StronglyMeasurable g ∧ f =ᵐ[μ] g :=
  ⟨hm.mk f, hm.stronglyMeasurable_mk, hm.ae_eq_mk⟩

section InnerProduct
variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

include 𝕜

/-- The source squared norm identity, derived from the L² inner product. -/
lemma l2_norm_sq (u : Lp H 2 μ) : ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂μ := by
  calc
    ‖u‖ ^ 2 = RCLike.re (inner 𝕜 u u) := norm_sq_eq_re_inner u
    _ = ∫ x, RCLike.re (inner 𝕜 (u x) (u x)) ∂μ := by
      rw [L2.inner_def]
      exact (integral_re (L2.integrable_inner (𝕜 := 𝕜) u u)).symm
    _ = ∫ x, ‖u x‖ ^ 2 ∂μ := by simp_rw [← norm_sq_eq_re_inner]

lemma l2_class_sub_norm_sq {f g : X → H} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖hf.toLp f - hg.toLp g‖ ^ 2 = ∫ x, ‖f x - g x‖ ^ 2 ∂μ := by
  rw [l2_norm_sq (𝕜 := 𝕜)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g), hf.coeFn_toLp,
    hg.coeFn_toLp] with x hs hfx hgx
  simp only [Pi.sub_apply] at hs
  rw [hs, hfx, hgx]
end InnerProduct

end GW.Analysis
