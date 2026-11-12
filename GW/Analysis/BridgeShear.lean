module
public import GW.Analysis.L2Quotient
public import GW.Conventions
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Measure.Prod
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal
namespace GW.Analysis
section Shear
variable {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)

def productShear (g : Y → GW.Space) (hg : Measurable g) : GW.Space × Y ≃ᵐ GW.Space × Y where
  toFun p := (p.1 + g p.2,p.2)
  invFun p := (p.1 - g p.2,p.2)
  left_inv p := Prod.ext (add_sub_cancel_right _ _) rfl
  right_inv p := Prod.ext (sub_add_cancel _ _) rfl
  measurable_toFun := (measurable_fst.add (hg.comp measurable_snd)).prodMk measurable_snd
  measurable_invFun := (measurable_fst.sub (hg.comp measurable_snd)).prodMk measurable_snd

lemma productShear_apply (g : Y → GW.Space) (hg : Measurable g) (p : GW.Space × Y) :
    productShear g hg p = (p.1+g p.2,p.2) := rfl

lemma productShear_inverse (g : Y → GW.Space) (hg : Measurable g) :
    (productShear g hg).symm = productShear (fun y => -g y) hg.neg := by
  apply MeasurableEquiv.ext
  funext p
  change (p.1 - g p.2,p.2) = (p.1 + -g p.2,p.2)
  rw [sub_eq_add_neg]

variable [SigmaFinite ν]

lemma productShear_lintegral (g : Y → GW.Space) (hg : Measurable g)
    (a : GW.Space × Y → ℝ≥0∞) (ha : Measurable a) :
    (∫⁻ p, a (productShear g hg p) ∂((volume : Measure GW.Space).prod ν)) =
      ∫⁻ p, a p ∂((volume : Measure GW.Space).prod ν) := by
  have h₁ := lintegral_prod_symm' (μ := (volume : Measure GW.Space)) (ν := ν)
    (a ∘ productShear g hg) (ha.comp (productShear g hg).measurable)
  have h₂ := lintegral_prod_symm' (μ := (volume : Measure GW.Space)) (ν := ν) a ha
  simp only [Function.comp_apply] at h₁
  rw [h₁,h₂]
  apply lintegral_congr
  intro y
  change (∫⁻ q, a (q+g y,y) ∂(volume : Measure GW.Space)) =
    ∫⁻ q, a (q,y) ∂(volume : Measure GW.Space)
  exact lintegral_add_right_eq_self (fun q : GW.Space => a (q,y)) (g y)

lemma productShear_preserving (g : Y → GW.Space) (hg : Measurable g) :
    MeasurePreserving (productShear g hg) ((volume : Measure GW.Space).prod ν)
      ((volume : Measure GW.Space).prod ν) where
  measurable := (productShear g hg).measurable
  map_eq := by
    let μ := (volume : Measure GW.Space).prod ν
    let e := productShear g hg
    apply Measure.ext
    intro s hs
    rw [Measure.map_apply e.measurable hs]
    change μ (e ⁻¹' s) = μ s
    calc
      _ = ∫⁻ p, (e ⁻¹' s).indicator (fun _ => (1:ℝ≥0∞)) p ∂μ :=
        (lintegral_indicator_one (hs.preimage e.measurable)).symm
      _ = ∫⁻ p, s.indicator (fun _ => (1:ℝ≥0∞)) (e p) ∂μ := by
        apply lintegral_congr
        intro p
        by_cases hp : e p ∈ s
        · rw [Set.indicator_of_mem (show p ∈ e ⁻¹' s from hp),Set.indicator_of_mem hp]
        · rw [Set.indicator_of_notMem (show p ∉ e ⁻¹' s from hp),Set.indicator_of_notMem hp]
      _ = ∫⁻ p, s.indicator (fun _ => (1:ℝ≥0∞)) p ∂μ :=
        productShear_lintegral ν g hg _ (measurable_const.indicator hs)
      _ = _ := lintegral_indicator_one hs

lemma productShear_null_preimage (g : Y → GW.Space) (hg : Measurable g)
    {N : Set (GW.Space × Y)} (hN : ((volume : Measure GW.Space).prod ν) N = 0) :
    ((volume : Measure GW.Space).prod ν) ((productShear g hg) ⁻¹' N) = 0 :=
  (productShear_preserving ν g hg).quasiMeasurePreserving.preimage_null hN

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def productShearL2 (g : Y → GW.Space) (hg : Measurable g) :
    Lp E 2 ((volume : Measure GW.Space).prod ν) ≃ₗᵢ[ℂ] Lp E 2 ((volume : Measure GW.Space).prod ν) := by
  let e := productShear g hg
  let he := productShear_preserving ν g hg
  refine LinearIsometryEquiv.ofSurjective (Lp.compMeasurePreservingₗᵢ ℂ e he) (fun u => ?_)
  refine ⟨Lp.compMeasurePreserving e.symm (he.symm e) u,?_⟩
  change Lp.compMeasurePreserving e he (Lp.compMeasurePreserving e.symm (he.symm e) u) = u
  rw [← Lp.compMeasurePreserving_comp_apply]
  have h : (e.symm : GW.Space × Y → GW.Space × Y) ∘ e = id := funext e.symm_apply_apply
  simp only [h,Lp.compMeasurePreserving_id_apply]

lemma productShearL2_ae (g : Y → GW.Space) (hg : Measurable g)
    (u : Lp E 2 ((volume : Measure GW.Space).prod ν)) :
    productShearL2 ν g hg u =ᵐ[(volume : Measure GW.Space).prod ν] fun p => u (productShear g hg p) :=
  Lp.coeFn_compMeasurePreserving _ _

lemma productShearL2_inverse (g : Y → GW.Space) (hg : Measurable g) :
    (productShearL2 (E := E) ν g hg).symm = productShearL2 ν (fun y => -g y) hg.neg := by
  apply LinearIsometryEquiv.ext
  intro u
  apply (productShearL2 ν g hg).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  change u = Lp.compMeasurePreserving (productShear g hg) (productShear_preserving ν g hg)
    (Lp.compMeasurePreserving (productShear (fun y => -g y) hg.neg) (productShear_preserving ν _ _) u)
  rw [← Lp.compMeasurePreserving_comp_apply]
  have h : (productShear (fun y => -g y) hg.neg : GW.Space × Y → GW.Space × Y) ∘ productShear g hg = id := by
    rw [← productShear_inverse g hg]
    exact funext (productShear g hg).symm_apply_apply
  simp only [h,Lp.compMeasurePreserving_id_apply]

end Shear
section MomentumShears
variable {Z E : Type*} [MeasurableSpace Z] (ν : Measure Z) [SigmaFinite ν]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma measurable_momentumShift (c : ℝ) : Measurable (fun k : GW.Space => c • k) :=
  measurable_id.const_smul c

lemma measurable_momentumShiftWith (c : ℝ) : Measurable (fun p : GW.Space × Z => c • p.1) :=
  measurable_fst.const_smul c

def momentumShear (c : ℝ) : GW.Space × GW.Space ≃ᵐ GW.Space × GW.Space :=
  productShear (fun k : GW.Space => c • k) (measurable_momentumShift c)

def momentumShearWith (c : ℝ) : GW.Space × (GW.Space × Z) ≃ᵐ GW.Space × (GW.Space × Z) :=
  productShear (fun p : GW.Space × Z => c • p.1) (measurable_momentumShiftWith c)

lemma momentumShear_apply (c : ℝ) (p : GW.Space × GW.Space) :
    momentumShear c p = (p.1+c • p.2,p.2) := rfl

lemma momentumShearWith_apply (c : ℝ) (p : GW.Space × (GW.Space × Z)) :
    momentumShearWith c p = (p.1+c • p.2.1,p.2.1,p.2.2) := rfl

lemma momentumShear_inverse (c : ℝ) : (momentumShear c).symm = momentumShear (-c) := by
  apply MeasurableEquiv.ext
  funext p
  change (p.1-c • p.2,p.2) = (p.1+(-c) • p.2,p.2)
  rw [sub_eq_add_neg,neg_smul]

lemma momentumShearWith_inverse (c : ℝ) :
    (momentumShearWith (Z := Z) c).symm = momentumShearWith (-c) := by
  apply MeasurableEquiv.ext
  funext p
  change (p.1-c • p.2.1,p.2) = (p.1+(-c) • p.2.1,p.2)
  rw [sub_eq_add_neg,neg_smul]

abbrev electronMomentumMeasure := (volume : Measure GW.Space).prod (volume : Measure GW.Space)
abbrev electronMomentumMeasureWith := (volume : Measure GW.Space).prod ((volume : Measure GW.Space).prod ν)

lemma momentumShear_preserving (c : ℝ) :
    MeasurePreserving (momentumShear c) electronMomentumMeasure electronMomentumMeasure :=
  productShear_preserving (volume : Measure GW.Space) (fun k : GW.Space => c • k) (measurable_momentumShift c)

lemma momentumShearWith_preserving (c : ℝ) :
    MeasurePreserving (momentumShearWith (Z := Z) c) (electronMomentumMeasureWith ν) (electronMomentumMeasureWith ν) :=
  productShear_preserving ((volume : Measure GW.Space).prod ν) (fun p => c • p.1) (measurable_momentumShiftWith c)

def momentumShearL2 (c : ℝ) :
    Lp E 2 electronMomentumMeasure ≃ₗᵢ[ℂ] Lp E 2 electronMomentumMeasure :=
  productShearL2 volume (fun k : GW.Space => c • k) (measurable_momentumShift c)

def momentumShearWithL2 (c : ℝ) :
    Lp E 2 (electronMomentumMeasureWith ν) ≃ₗᵢ[ℂ] Lp E 2 (electronMomentumMeasureWith ν) :=
  productShearL2 ((volume : Measure GW.Space).prod ν) (fun p => c • p.1) (measurable_momentumShiftWith c)

lemma momentumShearL2_ae (c : ℝ) (u : Lp E 2 electronMomentumMeasure) :
    momentumShearL2 c u =ᵐ[electronMomentumMeasure] fun p => u (p.1+c • p.2,p.2) :=
  productShearL2_ae volume (fun k : GW.Space => c • k) (measurable_momentumShift c) u

lemma momentumShearWithL2_ae (c : ℝ) (u : Lp E 2 (electronMomentumMeasureWith ν)) :
    momentumShearWithL2 ν c u =ᵐ[electronMomentumMeasureWith ν] fun p => u (p.1+c • p.2.1,p.2) :=
  productShearL2_ae ((volume : Measure GW.Space).prod ν) (fun p => c • p.1) (measurable_momentumShiftWith c) u

lemma momentumShearL2_inverse (c : ℝ) : (momentumShearL2 (E := E) c).symm = momentumShearL2 (-c) := by
  apply LinearIsometryEquiv.ext
  intro u
  have h := productShearL2_inverse (E := E) (volume : Measure GW.Space) (fun k : GW.Space => c • k)
    (measurable_momentumShift c)
  have he := congrArg (fun U : Lp E 2 electronMomentumMeasure ≃ₗᵢ[ℂ] Lp E 2 electronMomentumMeasure => U u) h
  change (momentumShearL2 (E := E) c).symm u = _ at he
  exact he.trans (by
    apply Lp.ext
    filter_upwards [productShearL2_ae (volume : Measure GW.Space) (fun k : GW.Space => -(c • k))
      (measurable_momentumShift c).neg u,momentumShearL2_ae (-c) u] with p h₁ h₂
    exact h₁.trans (by rw [h₂,productShear_apply,neg_smul]))

lemma momentumShearWithL2_inverse (c : ℝ) :
    (momentumShearWithL2 (E := E) ν c).symm = momentumShearWithL2 ν (-c) := by
  apply LinearIsometryEquiv.ext
  intro u
  let μ := (volume : Measure GW.Space).prod ν
  let g : GW.Space × Z → GW.Space := fun p => c • p.1
  have hg : Measurable g := measurable_momentumShiftWith c
  have h := productShearL2_inverse (E := E) μ g hg
  have he := congrArg (fun U : Lp E 2 (electronMomentumMeasureWith ν) ≃ₗᵢ[ℂ] Lp E 2 (electronMomentumMeasureWith ν) => U u) h
  change (momentumShearWithL2 (E := E) ν c).symm u = _ at he
  exact he.trans (by
    apply Lp.ext
    filter_upwards [productShearL2_ae μ (fun p => -g p) hg.neg u,momentumShearWithL2_ae ν (-c) u] with p h₁ h₂
    exact h₁.trans (by rw [h₂,productShear_apply,neg_smul]))

end MomentumShears
end GW.Analysis
