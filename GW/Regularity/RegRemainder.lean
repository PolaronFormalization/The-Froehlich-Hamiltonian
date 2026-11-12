module
public import GW.Regularity.RegRegularization
public import GW.Regularity.RegSectorFourier
public import GW.Gross.MainCommutators
public import GW.Regularity.RegAnnihilationEscape
@[expose] public section

-- Compiled component Maps02
noncomputable section
open MeasureTheory Filter GW.Regularity
open scoped Topology ENNReal BigOperators
namespace GW.Fock

def fractionalRemainderCoefficientMap (ε r : ℝ) (hε : 0 < ε) : OneBoson →L[ℂ] OneBoson :=
  GW.Analysis.boundedMultiplier (fun k : GW.Space => (rho ε r ‖k‖ : ℂ))
    (Complex.continuous_ofReal.measurable.comp (radialRegularizer_measurable ε r))
    (C := ε⁻¹) (Eventually.of_forall (fun k => by
      have h := rho_bounds (r := r) hε (norm_nonneg k)
      rw [Complex.norm_real,Real.norm_of_nonneg h.1]
      exact h.2.trans (min_le_right _ _)))

lemma fractionalRemainderCoefficient_ae (ε r : ℝ) (hε : 0 < ε) (f : OneBoson) :
    (fun k => (rho ε r ‖k‖ : ℂ) • f k) =ᵐ[(volume : Measure GW.Space)]
      fractionalRemainderCoefficientMap ε r hε f :=
  GW.Analysis.boundedMultiplier_ae _ _ _ _

lemma fractionalRemainderCoefficient_norm (ε r : ℝ) (hε : 0 < ε) (f : OneBoson) :
    ‖fractionalRemainderCoefficientMap ε r hε f‖ ≤ ε⁻¹ * ‖f‖ := by
  have h : ‖fractionalRemainderCoefficientMap ε r hε‖ ≤ ε⁻¹ :=
    GW.Analysis.boundedMultiplier_opNorm_le _ _ (inv_nonneg.mpr hε.le) _
  exact (fractionalRemainderCoefficientMap ε r hε).le_of_opNorm_le h f

def fractionalRemainderMinus (ε r : ℝ) (hε : 0 < ε) (f : OneBoson) :
    FreeGraphDomain →L[ℂ] Physical :=
  (radialRegularizer ε r hε).comp (commutatorAnnihilatorGraphMap f) -
    commutatorAnnihilatorGraphMap (fractionalRemainderCoefficientMap ε r hε f)

def fractionalRemainderPlus (ε r : ℝ) (hε : 0 < ε) (f : OneBoson) :
    FreeGraphDomain →L[ℂ] Physical :=
  (radialRegularizer ε r hε).comp (commutatorCreatorGraphMap f) -
    commutatorCreatorGraphMap (fractionalRemainderCoefficientMap ε r hε f)

lemma fractionalRemainderMinus_identity (ε r : ℝ) (hε : 0 < ε) (f : OneBoson)
    (u : FreeGraphDomain) :
    radialRegularizer ε r hε (commutatorAnnihilatorGraphMap f u) =
      commutatorAnnihilatorGraphMap (fractionalRemainderCoefficientMap ε r hε f) u +
        fractionalRemainderMinus ε r hε f u := by
  change radialRegularizer ε r hε (commutatorAnnihilatorGraphMap f u) = commutatorAnnihilatorGraphMap (fractionalRemainderCoefficientMap ε r hε f) u + (radialRegularizer ε r hε (commutatorAnnihilatorGraphMap f u) - commutatorAnnihilatorGraphMap (fractionalRemainderCoefficientMap ε r hε f) u)
  abel

lemma fractionalRemainderPlus_identity (ε r : ℝ) (hε : 0 < ε) (f : OneBoson)
    (u : FreeGraphDomain) :
    radialRegularizer ε r hε (commutatorCreatorGraphMap f u) =
      commutatorCreatorGraphMap (fractionalRemainderCoefficientMap ε r hε f) u +
        fractionalRemainderPlus ε r hε f u := by
  change radialRegularizer ε r hε (commutatorCreatorGraphMap f u) = commutatorCreatorGraphMap (fractionalRemainderCoefficientMap ε r hε f) u + (radialRegularizer ε r hε (commutatorCreatorGraphMap f u) - commutatorCreatorGraphMap (fractionalRemainderCoefficientMap ε r hε f) u)
  abel

lemma fractionalRemainder_annihilation_scalar (ε r : ℝ) (hε : 0 < ε)
    (hr : 0 < r) (hr1 : r ≤ 1) (q k : GW.Space) :
    |rho ε r ‖q‖ - rho ε r ‖k‖| ≤ ‖q-k‖^r := by
  simpa only [sub_add_cancel] using
    rho_momentum_difference (q-k) k hε hr hr1

lemma fractionalRemainder_creation_scalar (ε r : ℝ) (hε : 0 < ε)
    (hr : 0 < r) (hr1 : r ≤ 1) (q k : GW.Space) :
    |rho ε r ‖q‖ - rho ε r ‖k‖| ≤ ‖q+k‖^r := by
  have h := rho_momentum_difference (q+k) (-k) hε hr hr1
  simpa only [add_neg_cancel_right,norm_neg] using h

lemma fractionalRemainder_ratio_bound (a b : ℝ) (hb : 0 ≤ b) (h : |a| ≤ b) :
    |a/b| ≤ 1 := by
  by_cases hz : b=0
  · rw [hz,div_zero,abs_zero]
    exact zero_le_one
  · rw [abs_div,abs_of_nonneg hb]
    exact (div_le_one (lt_of_le_of_ne hb (Ne.symm hz))).mpr h

lemma fractionalRemainder_ratio_reconstruct (a b : ℝ) (hb : 0 ≤ b) (h : |a| ≤ b) :
    (a/b)*b=a := by
  by_cases hz : b=0
  · have ha : a=0 := abs_eq_zero.mp (le_antisymm (by simpa only [hz] using h) (abs_nonneg a))
    rw [ha,zero_div,zero_mul]
  · exact div_mul_cancel₀ a hz

def fractionalRemainderRatio (ε r : ℝ) (q k : GW.Space) : ℝ :=
  (rho ε r ‖q‖ - rho ε r ‖k‖) / ‖q-k‖^r

lemma fractionalRemainderRatio_measurable (ε r : ℝ) :
    Measurable (fun p : GW.Space × GW.Space => fractionalRemainderRatio ε r p.1 p.2) :=
  ((radialRegularizer_measurable ε r).comp measurable_fst |>.sub
    ((radialRegularizer_measurable ε r).comp measurable_snd)).div
    ((measurable_fst.sub measurable_snd).norm.pow_const r)

lemma fractionalRemainderRatio_bound (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r) (hr1 : r ≤ 1)
    (q k : GW.Space) : |fractionalRemainderRatio ε r q k| ≤ 1 :=
  fractionalRemainder_ratio_bound _ _ (Real.rpow_nonneg (norm_nonneg _) _)
    (fractionalRemainder_annihilation_scalar ε r hε hr hr1 q k)

lemma fractionalRemainderRatio_reconstruct (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r) (hr1 : r ≤ 1)
    (q k : GW.Space) :
    fractionalRemainderRatio ε r q k * ‖q-k‖^r = rho ε r ‖q‖ - rho ε r ‖k‖ :=
  fractionalRemainder_ratio_reconstruct _ _ (Real.rpow_nonneg (norm_nonneg _) _)
    (fractionalRemainder_annihilation_scalar ε r hε hr hr1 q k)

end GW.Fock

-- Compiled component Creation04
noncomputable section
open MeasureTheory Filter GW.Regularity
open scoped Topology ENNReal BigOperators
namespace GW.Fock

lemma fractionalRemainder_creation_pullback (n : ℕ)
    {P : GW.Space × (Fin n → GW.Space) → Prop}
    (hP : ∀ᵐ p ∂((volume : Measure GW.Space).prod (sectorMeasure n)), P p) :
    ∀ᵐ p ∂((volume : Measure GW.Space).prod (sectorMeasure (n+1))),
      P (p.1+p.2 0,fun i => p.2 ((0 : Fin (n+1)).succAbove i)) := by
  let s := MeasurableEquiv.prodCongr (MeasurableEquiv.refl GW.Space) (splitCoordinates n 0)
  have hs : MeasurePreserving s ((volume : Measure GW.Space).prod (sectorMeasure (n+1)))
      ((volume : Measure GW.Space).prod ((volume : Measure GW.Space).prod (sectorMeasure n))) :=
    (MeasurePreserving.id (volume : Measure GW.Space)).prod (splitCoordinates_preserving n 0)
  have ht := (GW.Analysis.momentumShearWith_preserving (sectorMeasure n) 1).comp hs
  have hr := (sectorFourierReorder_preserving n).symm (sectorFourierReorder n)
  have h := ((Measure.quasiMeasurePreserving_fst
    (μ := (volume : Measure GW.Space).prod (sectorMeasure n)) (ν := (volume : Measure GW.Space))).comp
    (hr.comp ht).quasiMeasurePreserving).ae hP
  filter_upwards [h] with p hp
  change P (p.1+(1:ℝ) • p.2 0,fun i => p.2 ((0 : Fin (n+1)).succAbove i)) at hp
  simpa only [one_smul] using hp

def fractionalRemainderProductMultiplier (ε r : ℝ) (hε : 0 < ε) (n : ℕ) :
    Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure n)) →L[ℂ]
      Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure n)) :=
  GW.Analysis.boundedMultiplier (fun p => (rho ε r ‖p.1‖ : ℂ))
    (Complex.continuous_ofReal.measurable.comp ((radialRegularizer_measurable ε r).comp measurable_fst))
    (C := ε⁻¹) (Eventually.of_forall (fun p => by
      have h := rho_bounds (r := r) hε (norm_nonneg p.1)
      rw [Complex.norm_real,Real.norm_of_nonneg h.1]
      exact h.2.trans (min_le_right _ _)))

lemma fractionalRemainderProductMultiplier_ae (ε r : ℝ) (hε : 0 < ε) (n : ℕ)
    (U : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure n))) :
    fractionalRemainderProductMultiplier ε r hε n U =ᵐ[((volume : Measure GW.Space).prod (sectorMeasure n))]
      fun p => (rho ε r ‖p.1‖ : ℂ)*U p :=
  (GW.Analysis.boundedMultiplier_ae _ _ _ _).symm

lemma fractionalRemainder_raw_creation_bound (ε r : ℝ) (hε : 0 < ε)
    (hr : 0 < r) (hr1 : r ≤ 1) (n : ℕ) (f : OneBoson)
    (U V : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure n)))
    (hV : V =ᵐ[((volume : Measure GW.Space).prod (sectorMeasure n))]
      fun p => (‖p.1‖^r : ℝ) • U p) :
    ‖fractionalRemainderProductMultiplier ε r hε (n+1) (sectorFourierRawCreation n f U) -
      sectorFourierRawCreation n (fractionalRemainderCoefficientMap ε r hε f) U‖ ≤ ‖f‖*‖V‖ := by
  have hb : ‖fractionalRemainderProductMultiplier ε r hε (n+1) (sectorFourierRawCreation n f U) -
      sectorFourierRawCreation n (fractionalRemainderCoefficientMap ε r hε f) U‖ ≤
      ‖sectorFourierRawCreation n f V‖ := by
    apply Lp.norm_le_norm_of_ae_le
    have hg := (Measure.quasiMeasurePreserving_snd
      (μ := (volume : Measure GW.Space)) (ν := sectorMeasure (n+1))).ae
      (((Measure.quasiMeasurePreserving_fst (μ := (volume : Measure GW.Space))
        (ν := sectorMeasure n)).comp (splitCoordinates_preserving n 0).quasiMeasurePreserving).ae
        (fractionalRemainderCoefficient_ae ε r hε f))
    filter_upwards [Lp.coeFn_sub
      (fractionalRemainderProductMultiplier ε r hε (n+1) (sectorFourierRawCreation n f U))
      (sectorFourierRawCreation n (fractionalRemainderCoefficientMap ε r hε f) U),
      fractionalRemainderProductMultiplier_ae ε r hε (n+1) (sectorFourierRawCreation n f U),
      sectorFourierRawCreation_ae n f U,
      sectorFourierRawCreation_ae n (fractionalRemainderCoefficientMap ε r hε f) U,
      sectorFourierRawCreation_ae n f V,fractionalRemainder_creation_pullback n hV,hg]
      with p hsub hM hU hgU hfV hV hg
    simp only [Pi.sub_apply] at hsub
    change (rho ε r ‖p.2 0‖ : ℂ) * f (p.2 0) =
      fractionalRemainderCoefficientMap ε r hε f (p.2 0) at hg
    rw [hsub,hM,hU,hgU,hfV,hV,← hg]
    rw [Complex.real_smul]
    have he : (rho ε r ‖p.1‖ : ℂ) * (f (p.2 0) * U (p.1+p.2 0,fun i => p.2 (Fin.succAbove 0 i))) -
        ((rho ε r ‖p.2 0‖ : ℂ) * f (p.2 0)) * U (p.1+p.2 0,fun i => p.2 (Fin.succAbove 0 i)) =
        ((rho ε r ‖p.1‖ - rho ε r ‖p.2 0‖ : ℝ) : ℂ) * f (p.2 0) *
          U (p.1+p.2 0,fun i => p.2 (Fin.succAbove 0 i)) := by push_cast; ring
    rw [he,norm_mul,norm_mul,norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (fractionalRemainder_creation_scalar ε r hε hr hr1 p.1 (p.2 0))
        (norm_nonneg (f (p.2 0))))
      (norm_nonneg (U (p.1+p.2 0,fun i => p.2 (Fin.succAbove 0 i))))
    exact h.trans_eq (by ring)
  exact hb.trans_eq (sectorFourierRawCreation_norm n f V)

end GW.Fock

-- Compiled component Annihilation01
noncomputable section
open MeasureTheory Filter GW.Regularity
open scoped Topology ENNReal BigOperators
namespace GW.Fock

lemma fractionalRemainder_annihilation_pullback (n : ℕ)
    {P : GW.Space × (Fin (n+1) → GW.Space) → Prop}
    (hP : ∀ᵐ p ∂((volume : Measure GW.Space).prod (sectorMeasure (n+1))), P p) :
    ∀ᵐ p ∂(((volume : Measure GW.Space).prod (sectorMeasure n)).prod (volume : Measure GW.Space)),
      P (p.1.1-p.2,(splitCoordinates n 0).symm (p.2,p.1.2)) := by
  let s := MeasurableEquiv.prodCongr (MeasurableEquiv.refl GW.Space) (splitCoordinates n 0).symm
  have hs : MeasurePreserving s
      ((volume : Measure GW.Space).prod ((volume : Measure GW.Space).prod (sectorMeasure n)))
      ((volume : Measure GW.Space).prod (sectorMeasure (n+1))) :=
    (MeasurePreserving.id (volume : Measure GW.Space)).prod (splitCoordinates_inverse_preserving n 0)
  have ht := (hs.comp (GW.Analysis.momentumShearWith_preserving (sectorMeasure n) (-1))).comp
    (sectorFourierReorder_preserving n)
  filter_upwards [ht.quasiMeasurePreserving.ae hP] with p hp
  change P (p.1.1+(-1:ℝ) • p.2,(splitCoordinates n 0).symm (p.2,p.1.2)) at hp
  simpa only [neg_one_smul,sub_eq_add_neg] using hp

lemma fractionalRemainder_delta_bound (ε r : ℝ) (hε : 0 < ε) (q k : GW.Space) :
    |rho ε r ‖q‖-rho ε r ‖k‖| ≤ ε⁻¹ := by
  have hq := rho_bounds (r := r) hε (norm_nonneg q)
  have hk := rho_bounds (r := r) hε (norm_nonneg k)
  have hq' := hq.2.trans (min_le_right _ _)
  have hk' := hk.2.trans (min_le_right _ _)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

def fractionalRemainderAnnDelta (ε r : ℝ) (hε : 0 < ε) (n : ℕ) :
    Lp ℂ 2 (((volume : Measure GW.Space).prod (sectorMeasure n)).prod (volume : Measure GW.Space)) →L[ℂ]
      Lp ℂ 2 (((volume : Measure GW.Space).prod (sectorMeasure n)).prod (volume : Measure GW.Space)) :=
  GW.Analysis.boundedMultiplier
    (fun p => ((rho ε r ‖p.1.1‖-rho ε r ‖p.2‖ : ℝ) : ℂ))
    (Complex.continuous_ofReal.measurable.comp
      (((radialRegularizer_measurable ε r).comp (measurable_fst.comp measurable_fst)).sub
        ((radialRegularizer_measurable ε r).comp measurable_snd)))
    (C := ε⁻¹) (Eventually.of_forall (fun p => by
      rw [Complex.norm_real,Real.norm_eq_abs]
      exact fractionalRemainder_delta_bound ε r hε p.1.1 p.2))

lemma fractionalRemainderAnnDelta_ae (ε r : ℝ) (hε : 0 < ε) (n : ℕ)
    (U : Lp ℂ 2 (((volume : Measure GW.Space).prod (sectorMeasure n)).prod (volume : Measure GW.Space))) :
    fractionalRemainderAnnDelta ε r hε n U =ᵐ[
      ((volume : Measure GW.Space).prod (sectorMeasure n)).prod (volume : Measure GW.Space)]
      fun p => ((rho ε r ‖p.1.1‖-rho ε r ‖p.2‖ : ℝ) : ℂ)*U p :=
  (GW.Analysis.boundedMultiplier_ae _ _ _ _).symm

lemma fractionalRemainder_ann_delta_weighted_bound (ε r : ℝ) (hε : 0 < ε)
    (hr : 0 < r) (hr1 : r ≤ 1) (n : ℕ)
    (U V : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure (n+1))))
    (hV : V =ᵐ[((volume : Measure GW.Space).prod (sectorMeasure (n+1)))]
      fun p => (‖p.1‖^r : ℝ) • U p) :
    ‖fractionalRemainderAnnDelta ε r hε n (sectorFourierAnnInput n U)‖ ≤ ‖V‖ := by
  have hb : ‖fractionalRemainderAnnDelta ε r hε n (sectorFourierAnnInput n U)‖ ≤
      ‖sectorFourierAnnInput n V‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [fractionalRemainderAnnDelta_ae ε r hε n (sectorFourierAnnInput n U),
      sectorFourierAnnInput_ae n U,sectorFourierAnnInput_ae n V,
      fractionalRemainder_annihilation_pullback n hV] with p hD hU hV' hV
    rw [hD,hU,hV',hV,norm_mul,norm_smul,Complex.norm_real,Real.norm_eq_abs,
      Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact mul_le_mul_of_nonneg_right
      (fractionalRemainder_annihilation_scalar ε r hε hr hr1 p.1.1 p.2) (norm_nonneg _)
  exact hb.trans_eq (by
    change ‖sectorFourierReorderUnitary n (GW.Analysis.momentumShearWithL2 (E := ℂ) (sectorMeasure n) (-1)
      (sectorFourierSplit n V))‖ = ‖V‖
    rw [LinearIsometryEquiv.norm_map,LinearIsometryEquiv.norm_map,LinearIsometryEquiv.norm_map])

end GW.Fock

-- Compiled component AnnFactor01
noncomputable section
open MeasureTheory Filter GW.Regularity
open scoped Topology ENNReal BigOperators
namespace GW.Fock

lemma fractionalRemainder_raw_annihilation_eq (ε r : ℝ) (hε : 0 < ε) (n : ℕ) (f : OneBoson)
    (U : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure (n+1)))) :
    fractionalRemainderProductMultiplier ε r hε n (sectorFourierRawAnnihilation n f U) -
        sectorFourierRawAnnihilation n (fractionalRemainderCoefficientMap ε r hε f) U =
      spectatorContraction ((volume : Measure GW.Space).prod (sectorMeasure n)) (volume : Measure GW.Space) f
        (fractionalRemainderAnnDelta ε r hε n (sectorFourierAnnInput n U)) := by
  apply Lp.ext
  have hd := Measure.ae_ae_of_ae_prod
    (fractionalRemainderAnnDelta_ae ε r hε n (sectorFourierAnnInput n U))
  have hi := Measure.ae_ae_of_ae_prod (sectorFourierAnnInput_ae n U)
  filter_upwards [Lp.coeFn_sub
    (fractionalRemainderProductMultiplier ε r hε n (sectorFourierRawAnnihilation n f U))
    (sectorFourierRawAnnihilation n (fractionalRemainderCoefficientMap ε r hε f) U),
    fractionalRemainderProductMultiplier_ae ε r hε n (sectorFourierRawAnnihilation n f U),
    sectorFourierRawAnnihilation_ae n f U,
    sectorFourierRawAnnihilation_ae n (fractionalRemainderCoefficientMap ε r hε f) U,
    spectatorContractionClass_ae ((volume : Measure GW.Space).prod (sectorMeasure n)) (volume : Measure GW.Space)
      f (fractionalRemainderAnnDelta ε r hε n (sectorFourierAnnInput n U)),
    sectorFourierRawAnnihilation_integrable n f U,
    sectorFourierRawAnnihilation_integrable n (fractionalRemainderCoefficientMap ε r hε f) U,hd,hi]
    with p hsub hM hA hG hC hIf hIg hD hI
  simp only [Pi.sub_apply] at hsub
  change _ = spectatorContractionClass ((volume : Measure GW.Space).prod (sectorMeasure n))
    (volume : Measure GW.Space) f (fractionalRemainderAnnDelta ε r hε n (sectorFourierAnnInput n U)) p
  rw [hsub,hM,hA,hG,hC]
  change (rho ε r ‖p.1‖ : ℂ) * (∫ k : GW.Space, (starRingEnd ℂ) (f k) *
    U (p.1-k,(splitCoordinates n 0).symm (k,p.2)) ∂volume) -
    (∫ k : GW.Space, (starRingEnd ℂ) (fractionalRemainderCoefficientMap ε r hε f k) *
    U (p.1-k,(splitCoordinates n 0).symm (k,p.2)) ∂volume) =
    ∫ k : GW.Space, (starRingEnd ℂ) (f k) *
      fractionalRemainderAnnDelta ε r hε n (sectorFourierAnnInput n U) (p,k) ∂volume
  rw [← integral_const_mul,← integral_sub (hIf.const_mul _) hIg]
  apply integral_congr_ae
  filter_upwards [hD,hI,fractionalRemainderCoefficient_ae ε r hε f] with k hD hI hg
  change (rho ε r ‖k‖ : ℂ)*f k = fractionalRemainderCoefficientMap ε r hε f k at hg
  rw [hD,hI,← hg,map_mul]
  have hc : (starRingEnd ℂ) (rho ε r ‖k‖ : ℂ) = (rho ε r ‖k‖ : ℂ) := Complex.conj_ofReal _
  rw [hc]
  push_cast
  ring

lemma fractionalRemainder_raw_annihilation_bound (ε r : ℝ) (hε : 0 < ε)
    (hr : 0 < r) (hr1 : r ≤ 1) (n : ℕ) (f : OneBoson)
    (U V : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure (n+1))))
    (hV : V =ᵐ[((volume : Measure GW.Space).prod (sectorMeasure (n+1)))]
      fun p => (‖p.1‖^r : ℝ) • U p) :
    ‖fractionalRemainderProductMultiplier ε r hε n (sectorFourierRawAnnihilation n f U) -
      sectorFourierRawAnnihilation n (fractionalRemainderCoefficientMap ε r hε f) U‖ ≤ ‖f‖*‖V‖ := by
  rw [fractionalRemainder_raw_annihilation_eq]
  exact (spectatorContractionClass_norm ((volume : Measure GW.Space).prod (sectorMeasure n))
    (volume : Measure GW.Space) f _).trans
    (mul_le_mul_of_nonneg_left (fractionalRemainder_ann_delta_weighted_bound ε r hε hr hr1 n U V hV)
      (norm_nonneg f))

end GW.Fock

-- Compiled component Symmetry03
noncomputable section
open MeasureTheory Filter GW.Regularity
open scoped Topology ENNReal BigOperators
namespace GW.Fock

lemma fractionalRemainder_multiplier_permutation (ε r : ℝ) (hε : 0 < ε) (n : ℕ)
    (τ : Equiv.Perm (Fin n)) (U : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure n))) :
    fractionalRemainderProductMultiplier ε r hε n (productPermutation (volume : Measure GW.Space) n τ U) =
      productPermutation (volume : Measure GW.Space) n τ (fractionalRemainderProductMultiplier ε r hε n U) := by
  apply Lp.ext
  have hm := (MeasurePreserving.prod (MeasurePreserving.id (volume : Measure GW.Space))
    (coordinatePermutation_preserving n τ)).quasiMeasurePreserving.ae
      (fractionalRemainderProductMultiplier_ae ε r hε n U)
  filter_upwards [fractionalRemainderProductMultiplier_ae ε r hε n (productPermutation (volume : Measure GW.Space) n τ U),
    productPermutation_ae (volume : Measure GW.Space) n τ U,
    productPermutation_ae (volume : Measure GW.Space) n τ (fractionalRemainderProductMultiplier ε r hε n U),hm]
    with p hM hP hMP hm
  have hmap : Prod.map id (coordinatePermutation n τ) p = (p.1,fun i => p.2 (τ i)) :=
    Prod.ext rfl (coordinatePermutation_eq n τ p.2)
  rw [hmap] at hm
  change fractionalRemainderProductMultiplier ε r hε n U (p.1,fun i => p.2 (τ i)) =
    (rho ε r ‖p.1‖ : ℂ)*U (p.1,fun i => p.2 (τ i)) at hm
  rw [hM,hP,hMP,hm]

lemma fractionalRemainder_multiplier_symmetrizer (ε r : ℝ) (hε : 0 < ε) (n : ℕ)
    (U : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure n))) :
    fractionalRemainderProductMultiplier ε r hε n (productSymmetrizer (volume : Measure GW.Space) n U) =
      productSymmetrizer (volume : Measure GW.Space) n (fractionalRemainderProductMultiplier ε r hε n U) := by
  rw [productSymmetrizer_average,productSymmetrizer_average,map_smul,map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro τ _
  exact fractionalRemainder_multiplier_permutation ε r hε n τ U

lemma fractionalRemainder_creation_expression_eq (ε r : ℝ) (hε : 0 < ε) (n : ℕ) (f : OneBoson)
    (U : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure n))) :
    fractionalRemainderProductMultiplier ε r hε (n+1) (sectorFourierCreationExpression n f U) -
      sectorFourierCreationExpression n (fractionalRemainderCoefficientMap ε r hε f) U =
    (Real.sqrt (n+1:ℕ) : ℂ) • productSymmetrizer (volume : Measure GW.Space) (n+1)
      (fractionalRemainderProductMultiplier ε r hε (n+1) (sectorFourierRawCreation n f U) -
        sectorFourierRawCreation n (fractionalRemainderCoefficientMap ε r hε f) U) := by
  change fractionalRemainderProductMultiplier ε r hε (n+1)
    ((Real.sqrt (n+1:ℕ) : ℂ) • productSymmetrizer (volume : Measure GW.Space) (n+1) (sectorFourierRawCreation n f U)) -
    (Real.sqrt (n+1:ℕ) : ℂ) • productSymmetrizer (volume : Measure GW.Space) (n+1)
      (sectorFourierRawCreation n (fractionalRemainderCoefficientMap ε r hε f) U) = _
  rw [map_smul,fractionalRemainder_multiplier_symmetrizer,map_sub,smul_sub]

lemma fractionalRemainder_creation_expression_bound (ε r : ℝ) (hε : 0 < ε)
    (hr : 0 < r) (hr1 : r ≤ 1) (n : ℕ) (f : OneBoson)
    (U V : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure n)))
    (hV : V =ᵐ[((volume : Measure GW.Space).prod (sectorMeasure n))]
      fun p => (‖p.1‖^r : ℝ) • U p) :
    ‖fractionalRemainderProductMultiplier ε r hε (n+1) (sectorFourierCreationExpression n f U) -
      sectorFourierCreationExpression n (fractionalRemainderCoefficientMap ε r hε f) U‖ ≤
      Real.sqrt (n+1:ℕ)*‖f‖*‖V‖ := by
  rw [fractionalRemainder_creation_expression_eq,norm_smul,Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact (mul_le_mul_of_nonneg_left (sectorFourierProductSymmetrizer_norm (n+1) _) (Real.sqrt_nonneg _)).trans
    ((mul_le_mul_of_nonneg_left (fractionalRemainder_raw_creation_bound ε r hε hr hr1 n f U V hV)
      (Real.sqrt_nonneg _)).trans_eq (by ring))

lemma fractionalRemainder_annihilation_expression_bound (ε r : ℝ) (hε : 0 < ε)
    (hr : 0 < r) (hr1 : r ≤ 1) (n : ℕ) (f : OneBoson)
    (U V : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure (n+1))))
    (hV : V =ᵐ[((volume : Measure GW.Space).prod (sectorMeasure (n+1)))]
      fun p => (‖p.1‖^r : ℝ) • U p) :
    ‖fractionalRemainderProductMultiplier ε r hε n (sectorFourierAnnihilationExpression n f U) -
      sectorFourierAnnihilationExpression n (fractionalRemainderCoefficientMap ε r hε f) U‖ ≤
      Real.sqrt (n+1:ℕ)*‖f‖*‖V‖ := by
  change ‖fractionalRemainderProductMultiplier ε r hε n
    ((Real.sqrt (n+1:ℕ) : ℂ) • sectorFourierRawAnnihilation n f U) -
    (Real.sqrt (n+1:ℕ) : ℂ) • sectorFourierRawAnnihilation n (fractionalRemainderCoefficientMap ε r hε f) U‖ ≤ _
  rw [map_smul,← smul_sub,norm_smul,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact (mul_le_mul_of_nonneg_left (fractionalRemainder_raw_annihilation_bound ε r hε hr hr1 n f U V hV)
    (Real.sqrt_nonneg _)).trans_eq (by ring)

end GW.Fock

-- Compiled component Outer03
noncomputable section
open MeasureTheory Filter GW.Regularity
open scoped Topology ENNReal BigOperators
namespace GW.Fock

section OuterMultiplier
variable {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [SigmaFinite ν]
variable (a : GW.Space → ℂ) (ha : Measurable a) (C : ℝ)
  (hb : ∀ᵐ q ∂(volume : Measure GW.Space), ‖a q‖ ≤ C)

def fractionalRemainderOuterScalar : ElectronL2 →L[ℂ] ElectronL2 :=
  GW.Analysis.boundedMultiplier a ha hb

def fractionalRemainderOuterBochner : Lp (Lp ℂ 2 ν) 2 (volume : Measure GW.Space) →L[ℂ]
    Lp (Lp ℂ 2 ν) 2 (volume : Measure GW.Space) :=
  GW.Analysis.boundedMultiplier a ha hb

def fractionalRemainderOuterProduct : Lp ℂ 2 ((volume : Measure GW.Space).prod ν) →L[ℂ]
    Lp ℂ 2 ((volume : Measure GW.Space).prod ν) :=
  GW.Analysis.boundedMultiplier (fun p : GW.Space × Y => a p.1) (ha.comp measurable_fst)
    ((Measure.quasiMeasurePreserving_fst (μ := (volume : Measure GW.Space)) (ν := ν)).ae hb)

lemma fractionalRemainder_outer_tensor (η : ElectronL2) (v : Lp ℂ 2 ν) :
    fractionalRemainderOuterBochner ν a ha C hb (tensorEmbedding (volume : Measure GW.Space) η v) =
      tensorEmbedding (volume : Measure GW.Space) (fractionalRemainderOuterScalar a ha C hb η) v := by
  apply Lp.ext
  filter_upwards [GW.Analysis.boundedMultiplier_ae a ha hb (tensorEmbedding (volume : Measure GW.Space) η v),
    tensorEmbedding_ae (volume : Measure GW.Space) η v,
    tensorEmbedding_ae (volume : Measure GW.Space) (fractionalRemainderOuterScalar a ha C hb η) v,
    GW.Analysis.boundedMultiplier_ae a ha hb η] with q hB hT hT' hη
  change a q • tensorEmbedding (volume : Measure GW.Space) η v q =
    fractionalRemainderOuterBochner ν a ha C hb (tensorEmbedding (volume : Measure GW.Space) η v) q at hB
  change a q • η q = fractionalRemainderOuterScalar a ha C hb η q at hη
  rw [← hB,hT,hT',← hη,smul_smul]
  rfl


lemma fractionalRemainder_outer_product_tensor (η : ElectronL2) (v : Lp ℂ 2 ν) :
    fractionalRemainderOuterProduct ν a ha C hb (productFunction (volume : Measure GW.Space) ν η v) =
      productFunction (volume : Measure GW.Space) ν (fractionalRemainderOuterScalar a ha C hb η) v := by
  apply Lp.ext
  have hη := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure GW.Space)) (ν := ν)).ae (GW.Analysis.boundedMultiplier_ae a ha hb η)
  filter_upwards [GW.Analysis.boundedMultiplier_ae (fun p : GW.Space × Y => a p.1) (ha.comp measurable_fst)
      ((Measure.quasiMeasurePreserving_fst (μ := (volume : Measure GW.Space)) (ν := ν)).ae hb) (productFunction (volume : Measure GW.Space) ν η v),
    productFunction_ae (volume : Measure GW.Space) ν η v,
    productFunction_ae (volume : Measure GW.Space) ν (fractionalRemainderOuterScalar a ha C hb η) v,hη]
    with p hB hP hP' hη
  change a p.1 • productFunction (volume : Measure GW.Space) ν η v p =
    fractionalRemainderOuterProduct ν a ha C hb (productFunction (volume : Measure GW.Space) ν η v) p at hB
  change a p.1 • η p.1 = fractionalRemainderOuterScalar a ha C hb η p.1 at hη
  rw [← hB,hP,hP',← hη,smul_smul]
  rfl


lemma fractionalRemainder_outer_natural (u : Lp (Lp ℂ 2 ν) 2 (volume : Measure GW.Space)) :
    productUnitary (volume : Measure GW.Space) ν (fractionalRemainderOuterBochner ν a ha C hb u) =
      fractionalRemainderOuterProduct ν a ha C hb (productUnitary (volume : Measure GW.Space) ν u) := by
  let T := (productUnitary (E := ℂ) (volume : Measure GW.Space) ν).toContinuousLinearEquiv.toContinuousLinearMap
  let A := T.comp (fractionalRemainderOuterBochner ν a ha C hb)
  let B := (fractionalRemainderOuterProduct ν a ha C hb).comp T
  change A u = B u
  apply Lp.induction (p := 2) (μ := (volume : Measure GW.Space)) (by norm_num)
    (fun u => A u = B u) ?_ ?_ (isClosed_eq A.continuous B.continuous) u
  · intro v S hS hSf
    let η := indicatorConstLp (μ := (volume : Measure GW.Space)) 2 hS hSf.ne (1:ℂ)
    have ht : tensorEmbedding (volume : Measure GW.Space) η v = indicatorConstLp 2 hS hSf.ne v := by
      rw [tensorEmbedding_apply]
      simpa only [η,ContinuousLinearMap.toSpanSingleton_apply,one_smul] using
        compLp_indicatorConst (volume : Measure GW.Space) hS hSf.ne (ContinuousLinearMap.toSpanSingleton ℂ v) 1
    change A (indicatorConstLp 2 hS hSf.ne v) = B (indicatorConstLp 2 hS hSf.ne v)
    rw [← ht]
    change productUnitary (volume : Measure GW.Space) ν
      (fractionalRemainderOuterBochner ν a ha C hb (tensorEmbedding (volume : Measure GW.Space) η v)) =
      fractionalRemainderOuterProduct ν a ha C hb
        (productUnitary (volume : Measure GW.Space) ν (tensorEmbedding (volume : Measure GW.Space) η v))
    rw [fractionalRemainder_outer_tensor,productUnitary_tensor,productUnitary_tensor,
      fractionalRemainder_outer_product_tensor]
  · intro f g hf hg _ h₁ h₂
    exact (A.map_add (hf.toLp f) (hg.toLp g)).trans
      ((congrArg₂ (fun x y => x+y) h₁ h₂).trans (B.map_add (hf.toLp f) (hg.toLp g)).symm)

end OuterMultiplier
end GW.Fock

-- Compiled component Weight02
noncomputable section
open MeasureTheory Filter GW.Regularity
open scoped Topology ENNReal BigOperators
namespace GW.Fock

lemma fractionalRemainder_product_weight
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [SigmaFinite ν]
    (w : GW.Space → ℝ) (hw : Measurable w) (hwn : ∀ q, 0 ≤ w q)
    (u v : Lp (Lp ℂ 2 ν) 2 (volume : Measure GW.Space))
    (hv : v =ᵐ[(volume : Measure GW.Space)] fun q => (w q : ℂ) • u q) :
    productUnitary (volume : Measure GW.Space) ν v =ᵐ[(volume : Measure GW.Space).prod ν]
      fun p => (w p.1 : ℂ) • productUnitary (volume : Measure GW.Space) ν u p := by
  let b := fun q => (((1+w q)⁻¹ : ℝ) : ℂ)
  let a := fun q => ((w q/(1+w q) : ℝ) : ℂ)
  have hb : Measurable b := Complex.continuous_ofReal.measurable.comp (measurable_const.add hw).inv
  have ha : Measurable a := Complex.continuous_ofReal.measurable.comp (hw.div (measurable_const.add hw))
  have hb1 : ∀ᵐ q ∂(volume : Measure GW.Space), ‖b q‖ ≤ (1:ℝ) := Eventually.of_forall (fun q => by
    change ‖(((1+w q)⁻¹ : ℝ) : ℂ)‖ ≤ 1
    rw [Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr (by linarith [hwn q]))]
    exact inv_le_one_of_one_le₀ (by linarith [hwn q]))
  have ha1 : ∀ᵐ q ∂(volume : Measure GW.Space), ‖a q‖ ≤ (1:ℝ) := Eventually.of_forall (fun q => by
    change ‖((w q/(1+w q) : ℝ) : ℂ)‖ ≤ 1
    rw [Complex.norm_real,Real.norm_of_nonneg (div_nonneg (hwn q) (by linarith [hwn q]))]
    exact (div_le_one (by linarith [hwn q])).mpr (by linarith))
  have he : fractionalRemainderOuterBochner ν b hb 1 hb1 v =
      fractionalRemainderOuterBochner ν a ha 1 ha1 u := by
    apply Lp.ext
    filter_upwards [hv,GW.Analysis.boundedMultiplier_ae b hb hb1 v,
      GW.Analysis.boundedMultiplier_ae a ha ha1 u] with q hv hB hA
    change b q • v q = fractionalRemainderOuterBochner ν b hb 1 hb1 v q at hB
    change a q • u q = fractionalRemainderOuterBochner ν a ha 1 ha1 u q at hA
    rw [← hB,← hA,hv,smul_smul]
    congr 1
    change (((1+w q)⁻¹ : ℝ) : ℂ)*(w q : ℂ) = ((w q/(1+w q) : ℝ) : ℂ)
    push_cast
    ring
  have ht := congrArg (productUnitary (E := ℂ) (volume : Measure GW.Space) ν) he
  rw [fractionalRemainder_outer_natural,fractionalRemainder_outer_natural] at ht
  filter_upwards [
    GW.Analysis.boundedMultiplier_ae (fun p : GW.Space × Y => b p.1) (hb.comp measurable_fst)
      ((Measure.quasiMeasurePreserving_fst (μ := (volume : Measure GW.Space)) (ν := ν)).ae hb1) (productUnitary (volume : Measure GW.Space) ν v),
    GW.Analysis.boundedMultiplier_ae (fun p : GW.Space × Y => a p.1) (ha.comp measurable_fst)
      ((Measure.quasiMeasurePreserving_fst (μ := (volume : Measure GW.Space)) (ν := ν)).ae ha1) (productUnitary (volume : Measure GW.Space) ν u)]
    with p hB hA
  have he := congrArg (fun z : Lp ℂ 2 ((volume : Measure GW.Space).prod ν) => z p) ht
  change b p.1 • productUnitary (volume : Measure GW.Space) ν v p =
    fractionalRemainderOuterProduct ν b hb 1 hb1 (productUnitary (volume : Measure GW.Space) ν v) p at hB
  change a p.1 • productUnitary (volume : Measure GW.Space) ν u p =
    fractionalRemainderOuterProduct ν a ha 1 ha1 (productUnitary (volume : Measure GW.Space) ν u) p at hA
  change fractionalRemainderOuterProduct ν b hb 1 hb1 (productUnitary (volume : Measure GW.Space) ν v) p =
    fractionalRemainderOuterProduct ν a ha 1 ha1 (productUnitary (volume : Measure GW.Space) ν u) p at he
  rw [← hB,← hA] at he
  have hbn : b p.1 ≠ 0 := by
    change (((1+w p.1)⁻¹ : ℝ) : ℂ) ≠ 0
    exact_mod_cast inv_ne_zero (ne_of_gt (by linarith [hwn p.1] : 0 < 1+w p.1))
  apply (mul_left_cancel₀ hbn)
  change b p.1 * productUnitary (volume : Measure GW.Space) ν v p =
    b p.1 * ((w p.1 : ℂ) * productUnitary (volume : Measure GW.Space) ν u p)
  have hab : a p.1 = b p.1 * (w p.1 : ℂ) := by dsimp [a,b]; push_cast; ring
  simpa only [smul_eq_mul,hab,mul_assoc] using he

end GW.Fock

-- Compiled component Transport02
noncomputable section
open MeasureTheory Filter GW.Regularity
open scoped Topology ENNReal BigOperators
namespace GW.Fock

lemma fractionalRemainder_sector_weight (n : ℕ) (w : GW.Space → ℝ)
    (hw : Measurable w) (hwn : ∀ q, 0 ≤ w q) (u v : ElectronSector n)
    (hv : v =ᵐ[(volume : Measure GW.Space)] fun q => (w q : ℂ) • u q) :
    sectorFourierProductMap n v =ᵐ[(volume : Measure GW.Space).prod (sectorMeasure n)]
      fun p => (w p.1 : ℂ) • sectorFourierProductMap n u p := by
  let I := sectorFourierSectorInclusion n
  have h : amplify (volume : Measure GW.Space) I v =ᵐ[(volume : Measure GW.Space)]
      fun q => (w q : ℂ) • amplify (volume : Measure GW.Space) I u q := by
    filter_upwards [amplify_ae (volume : Measure GW.Space) I v,
      amplify_ae (volume : Measure GW.Space) I u,hv] with q hV hU hv
    rw [hV,hU,hv,map_smul]
  exact fractionalRemainder_product_weight (sectorMeasure n) w hw hwn _ _ h

lemma fractionalRemainder_sector_norm (n : ℕ) (u : ElectronSector n) :
    ‖sectorFourierProductMap n u‖ = ‖u‖ := by
  change ‖productUnitary (volume : Measure GW.Space) (sectorMeasure n)
    (amplify (volume : Measure GW.Space) (sectorFourierSectorInclusion n) u)‖ = ‖u‖
  rw [LinearIsometryEquiv.norm_map]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [GW.Analysis.l2_norm_sq (𝕜 := ℂ),GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
  apply integral_congr_ae
  filter_upwards [amplify_ae (volume : Measure GW.Space) (sectorFourierSectorInclusion n) u] with q hq
  rw [hq]
  change ‖(kernelFixedInclusion (E := ℂ) n) (ordinarySectorKernel n (u q))‖^2 = ‖u q‖^2
  rw [LinearIsometry.norm_map,LinearIsometryEquiv.norm_map]

lemma fractionalRemainder_regularizer_sector (ε r : ℝ) (hε : 0 < ε) (u : Physical) (n : ℕ) :
    sectorFourierFullSector (radialRegularizer ε r hε u) n =
      fractionalRemainderProductMultiplier ε r hε n (sectorFourierFullSector u n) := by
  apply Lp.ext
  have h := fractionalRemainder_sector_weight n (fun q => rho ε r ‖q‖)
    (radialRegularizer_measurable ε r)
    (fun q => (rho_bounds (r := r) hε (norm_nonneg q)).1)
    (freeFourierRepresentation u n) (freeFourierRepresentation (radialRegularizer ε r hε u) n)
    (radialRegularizer_ae ε r hε u n).symm
  exact h.trans (fractionalRemainderProductMultiplier_ae ε r hε n (sectorFourierFullSector u n)).symm

lemma fractionalRemainderFullSector_norm (u : Physical) (n : ℕ) :
    ‖sectorFourierFullSector u n‖ = ‖freeFourierRepresentation u n‖ :=
  fractionalRemainder_sector_norm n _

lemma fractionalRemainderFullSector_sub (u v : Physical) (n : ℕ) :
    sectorFourierFullSector (u-v) n = sectorFourierFullSector u n - sectorFourierFullSector v n := by
  change sectorFourierProductMap n (freeFourierRepresentation (u-v) n) = _
  rw [map_sub,lp.coeFn_sub,Pi.sub_apply,map_sub]
  rfl

lemma fractionalRemainder_physical_weight (w : ℕ → GW.Space → ℝ)
    (hw : ∀ n, Measurable (w n)) (hwn : ∀ n q, 0 ≤ w n q)
    (u : (physicalSectorMultiplier w).domain) (n : ℕ) :
    sectorFourierFullSector (physicalSectorMultiplier w u) n =ᵐ[
      (volume : Measure GW.Space).prod (sectorMeasure n)]
      fun p => (w n p.1 : ℂ) • sectorFourierFullSector u.val n p :=
  fractionalRemainder_sector_weight n (w n) (hw n) (hwn n) _ _
    (physicalSectorMultiplier_action w u n).symm

end GW.Fock

-- Compiled component Mixed02
noncomputable section
open MeasureTheory Filter GW.Regularity
open scoped Topology ENNReal BigOperators
namespace GW.Fock

def fractionalRemainderMixedSymbol (shifted : Bool) (r : ℝ) (n : ℕ) (q : GW.Space) : ℝ :=
  ‖q‖^r * Real.sqrt ((n:ℝ) + if shifted then 1 else 0)

lemma fractionalRemainderMixedSymbol_measurable (shifted : Bool) (r : ℝ) (n : ℕ) :
    Measurable (fractionalRemainderMixedSymbol shifted r n) :=
  (continuous_norm.measurable.pow_const r).mul measurable_const

lemma fractionalRemainderMixedSymbol_nonneg (shifted : Bool) (r : ℝ) (n : ℕ) (q : GW.Space) :
    0 ≤ fractionalRemainderMixedSymbol shifted r n q :=
  mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.sqrt_nonneg _)

lemma fractionalRemainderMixedSymbol_bound (shifted : Bool) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (n : ℕ) (q : GW.Space) :
    |fractionalRemainderMixedSymbol shifted r n q| ≤ |freeGraphWeight n q| := by
  cases shifted with
  | true => exact radial_shiftedRoot_bound r hr hr1 n q
  | false =>
    have h := radial_shiftedRoot_bound r hr hr1 n q
    rw [abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.sqrt_nonneg _))] at h
    rw [abs_of_nonneg (fractionalRemainderMixedSymbol_nonneg false r n q)]
    change ‖q‖^r*Real.sqrt ((n:ℝ)+0) ≤ _
    exact (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith : (n:ℝ)+0 ≤ (n:ℝ)+1))
      (Real.rpow_nonneg (norm_nonneg _) _)).trans h

def fractionalRemainderMixedOperator (shifted : Bool) (r : ℝ) : Physical →ₗ.[ℂ] Physical :=
  physicalSectorMultiplier (fractionalRemainderMixedSymbol shifted r)

lemma fractionalRemainderMixed_mem_bound (shifted : Bool) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (u : FreeGraphDomain) :
    ∃ hm : (show freeGraphOperator.domain from u).val ∈ (fractionalRemainderMixedOperator shifted r).domain,
      ‖fractionalRemainderMixedOperator shifted r ⟨(show freeGraphOperator.domain from u).val,hm⟩‖ ≤ ‖u‖ := by
  obtain ⟨hm,hb⟩ := physicalSectorMultiplier_domination (fractionalRemainderMixedSymbol shifted r)
    freeGraphWeight (fractionalRemainderMixedSymbol_measurable shifted r) zero_le_one
    (fun n q => by simpa only [one_mul] using fractionalRemainderMixedSymbol_bound shifted r hr hr1 n q) u
  refine ⟨hm,?_⟩
  rw [freeGraphDomain_norm]
  simpa only [one_mul,fractionalRemainderMixedOperator,freeGraphOperator] using hb

def fractionalRemainderMixedInput (shifted : Bool) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (u : FreeGraphDomain) : (fractionalRemainderMixedOperator shifted r).domain :=
  ⟨(show freeGraphOperator.domain from u).val,(fractionalRemainderMixed_mem_bound shifted r hr hr1 u).choose⟩

lemma fractionalRemainderMixed_bound (shifted : Bool) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (u : FreeGraphDomain) :
    ‖fractionalRemainderMixedOperator shifted r (fractionalRemainderMixedInput shifted r hr hr1 u)‖ ≤ ‖u‖ :=
  (fractionalRemainderMixed_mem_bound shifted r hr hr1 u).choose_spec

lemma fractionalRemainderMixed_sector (shifted : Bool) (r : ℝ)
    (u : (fractionalRemainderMixedOperator shifted r).domain) (n : ℕ) :
    sectorFourierFullSector (fractionalRemainderMixedOperator shifted r u) n =ᵐ[
      (volume : Measure GW.Space).prod (sectorMeasure n)]
      fun p => (fractionalRemainderMixedSymbol shifted r n p.1 : ℂ) • sectorFourierFullSector u.val n p :=
  fractionalRemainder_physical_weight _ (fractionalRemainderMixedSymbol_measurable shifted r)
    (fractionalRemainderMixedSymbol_nonneg shifted r) u n

lemma fractionalRemainder_unnormalize_weight (n : ℕ) (r c : ℝ) (hc : 0 < c)
    (U W : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure n)))
    (hW : W =ᵐ[((volume : Measure GW.Space).prod (sectorMeasure n))]
      fun p => ((‖p.1‖^r*c : ℝ) : ℂ) • U p) :
    (c⁻¹ : ℂ) • W =ᵐ[((volume : Measure GW.Space).prod (sectorMeasure n))]
      fun p => (‖p.1‖^r : ℝ) • U p := by
  filter_upwards [Lp.coeFn_smul (c⁻¹ : ℂ) W,hW] with p hs hW
  simp only [Pi.smul_apply] at hs
  rw [hs,hW,smul_smul,Complex.real_smul]
  congr 1
  push_cast
  field_simp [ne_of_gt hc]

end GW.Fock

-- Compiled component Graphs01
noncomputable section
open MeasureTheory Filter GW.Regularity
open scoped Topology ENNReal BigOperators
namespace GW.Fock

lemma fractionalRemainderCreatorGraph (f : OneBoson) (u : FreeGraphDomain) :
    (freeGraphDomainInclusion u,commutatorCreatorGraphMap f u) ∈
      (generalizedCreation (phaseMultiplicationKernel f)).graph := by
  simpa only [commutatorCreatorGraphMap,ContinuousLinearMap.comp_apply,commutatorGraphRootMap_value] using
    commutatorPhaseCreatorMap_graph f (commutatorGraphRootMap u)

lemma fractionalRemainderAnnihilatorGraph (f : OneBoson) (u : FreeGraphDomain) :
    (freeGraphDomainInclusion u,commutatorAnnihilatorGraphMap f u) ∈
      (generalizedAnnihilation (phaseMultiplicationKernel f)).graph := by
  simpa only [commutatorAnnihilatorGraphMap,ContinuousLinearMap.comp_apply,commutatorGraphRootMap_value] using
    commutatorPhaseAnnihilatorMap_graph f (commutatorGraphRootMap u)

lemma fractionalRemainder_creator_sector (f : OneBoson) (u : FreeGraphDomain) (n : ℕ) :
    sectorFourierFullSector (commutatorCreatorGraphMap f u) (n+1) =
      sectorFourierCreationExpression n f (sectorFourierFullSector (freeGraphDomainInclusion u) n) := by
  obtain ⟨v,hval,hout⟩ := (generalizedCreation (phaseMultiplicationKernel f)).mem_graph_iff.mp
    (fractionalRemainderCreatorGraph f u)
  have h := sectorFourierFullSector_creation f v n
  rw [hout,hval] at h
  exact h

lemma fractionalRemainder_annihilator_sector (f : OneBoson) (u : FreeGraphDomain) (n : ℕ) :
    sectorFourierFullSector (commutatorAnnihilatorGraphMap f u) n =
      sectorFourierAnnihilationExpression n f (sectorFourierFullSector (freeGraphDomainInclusion u) (n+1)) := by
  obtain ⟨v,hval,hout⟩ := (generalizedAnnihilation (phaseMultiplicationKernel f)).mem_graph_iff.mp
    (fractionalRemainderAnnihilatorGraph f u)
  have h := sectorFourierFullSector_annihilation f v n
  rw [hout,hval] at h
  exact h

lemma fractionalRemainder_creator_zero (f : OneBoson) (u : FreeGraphDomain) :
    sectorFourierFullSector (commutatorCreatorGraphMap f u) 0 = 0 := by
  obtain ⟨v,hval,hout⟩ := (generalizedCreation (phaseMultiplicationKernel f)).mem_graph_iff.mp
    (fractionalRemainderCreatorGraph f u)
  have h := sectorFourierFullSector_creation_zero f v
  rw [hout] at h
  exact h

lemma fractionalRemainderPlus_sector (ε r : ℝ) (hε : 0 < ε) (f : OneBoson)
    (u : FreeGraphDomain) (n : ℕ) :
    sectorFourierFullSector (fractionalRemainderPlus ε r hε f u) (n+1) =
      fractionalRemainderProductMultiplier ε r hε (n+1)
        (sectorFourierCreationExpression n f (sectorFourierFullSector (freeGraphDomainInclusion u) n)) -
      sectorFourierCreationExpression n (fractionalRemainderCoefficientMap ε r hε f)
        (sectorFourierFullSector (freeGraphDomainInclusion u) n) := by
  change sectorFourierFullSector
    (radialRegularizer ε r hε (commutatorCreatorGraphMap f u) -
      commutatorCreatorGraphMap (fractionalRemainderCoefficientMap ε r hε f) u) (n+1) = _
  rw [fractionalRemainderFullSector_sub,fractionalRemainder_regularizer_sector,
    fractionalRemainder_creator_sector,fractionalRemainder_creator_sector]

lemma fractionalRemainderMinus_sector (ε r : ℝ) (hε : 0 < ε) (f : OneBoson)
    (u : FreeGraphDomain) (n : ℕ) :
    sectorFourierFullSector (fractionalRemainderMinus ε r hε f u) n =
      fractionalRemainderProductMultiplier ε r hε n
        (sectorFourierAnnihilationExpression n f (sectorFourierFullSector (freeGraphDomainInclusion u) (n+1))) -
      sectorFourierAnnihilationExpression n (fractionalRemainderCoefficientMap ε r hε f)
        (sectorFourierFullSector (freeGraphDomainInclusion u) (n+1)) := by
  change sectorFourierFullSector
    (radialRegularizer ε r hε (commutatorAnnihilatorGraphMap f u) -
      commutatorAnnihilatorGraphMap (fractionalRemainderCoefficientMap ε r hε f) u) n = _
  rw [fractionalRemainderFullSector_sub,fractionalRemainder_regularizer_sector,
    fractionalRemainder_annihilator_sector,fractionalRemainder_annihilator_sector]

lemma fractionalRemainderPlus_zero (ε r : ℝ) (hε : 0 < ε) (f : OneBoson) (u : FreeGraphDomain) :
    sectorFourierFullSector (fractionalRemainderPlus ε r hε f u) 0 = 0 := by
  change sectorFourierFullSector (radialRegularizer ε r hε (commutatorCreatorGraphMap f u) -
    commutatorCreatorGraphMap (fractionalRemainderCoefficientMap ε r hε f) u) 0 = 0
  rw [fractionalRemainderFullSector_sub,fractionalRemainder_regularizer_sector,
    fractionalRemainder_creator_zero,fractionalRemainder_creator_zero,map_zero,sub_zero]

end GW.Fock

-- Compiled component SectorBounds02
noncomputable section
open MeasureTheory Filter GW.Regularity
open scoped Topology ENNReal BigOperators
namespace GW.Fock

lemma fractionalRemainderPlus_sector_bound (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r) (hr1 : r ≤ 1)
    (f : OneBoson) (u : FreeGraphDomain) (n : ℕ) :
    ‖sectorFourierFullSector (fractionalRemainderPlus ε r hε f u) (n+1)‖ ≤
      ‖f‖*‖sectorFourierFullSector
        (fractionalRemainderMixedOperator true r (fractionalRemainderMixedInput true r hr.le hr1 u)) n‖ := by
  let U := sectorFourierFullSector (freeGraphDomainInclusion u) n
  let W := sectorFourierFullSector
    (fractionalRemainderMixedOperator true r (fractionalRemainderMixedInput true r hr.le hr1 u)) n
  let c := Real.sqrt (n+1:ℕ)
  have hc : 0 < c := Real.sqrt_pos.mpr (by positivity)
  have hW : W =ᵐ[((volume : Measure GW.Space).prod (sectorMeasure n))]
      fun p => ((‖p.1‖^r*c : ℝ) : ℂ) • U p := by
    have h := fractionalRemainderMixed_sector true r (fractionalRemainderMixedInput true r hr.le hr1 u) n
    simpa only [fractionalRemainderMixedInput,fractionalRemainderMixedSymbol,ite_true,
      Nat.cast_add,Nat.cast_one,U,W,c,freeGraphDomainInclusion_apply] using h
  have hV := fractionalRemainder_unnormalize_weight n r c hc U W hW
  have hb := fractionalRemainder_creation_expression_bound ε r hε hr hr1 n f U ((c⁻¹:ℂ) • W) hV
  rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hc.le] at hb
  rw [fractionalRemainderPlus_sector]
  exact hb.trans_eq (by change c*‖f‖*(c⁻¹*‖W‖)=‖f‖*‖W‖; field_simp [ne_of_gt hc])

lemma fractionalRemainderMinus_sector_bound (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r) (hr1 : r ≤ 1)
    (f : OneBoson) (u : FreeGraphDomain) (n : ℕ) :
    ‖sectorFourierFullSector (fractionalRemainderMinus ε r hε f u) n‖ ≤
      ‖f‖*‖sectorFourierFullSector
        (fractionalRemainderMixedOperator false r (fractionalRemainderMixedInput false r hr.le hr1 u)) (n+1)‖ := by
  let U := sectorFourierFullSector (freeGraphDomainInclusion u) (n+1)
  let W := sectorFourierFullSector
    (fractionalRemainderMixedOperator false r (fractionalRemainderMixedInput false r hr.le hr1 u)) (n+1)
  let c := Real.sqrt (n+1:ℕ)
  have hc : 0 < c := Real.sqrt_pos.mpr (by positivity)
  have hW : W =ᵐ[((volume : Measure GW.Space).prod (sectorMeasure (n+1)))]
      fun p => ((‖p.1‖^r*c : ℝ) : ℂ) • U p := by
    have h := fractionalRemainderMixed_sector false r (fractionalRemainderMixedInput false r hr.le hr1 u) (n+1)
    simpa only [fractionalRemainderMixedInput,fractionalRemainderMixedSymbol,Bool.false_eq_true,ite_false,add_zero,
      U,W,c,freeGraphDomainInclusion_apply] using h
  have hV := fractionalRemainder_unnormalize_weight (n+1) r c hc U W hW
  have hb := fractionalRemainder_annihilation_expression_bound ε r hε hr hr1 n f U ((c⁻¹:ℂ) • W) hV
  rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hc.le] at hb
  rw [fractionalRemainderMinus_sector]
  exact hb.trans_eq (by change c*‖f‖*(c⁻¹*‖W‖)=‖f‖*‖W‖; field_simp [ne_of_gt hc])

lemma fractionalRemainder_creation_shift_norm {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
    (v w : lp E 2) (C : ℝ) (hC : 0 ≤ C) (hv0 : v 0 = 0)
    (h : ∀ n, ‖v (n+1)‖ ≤ C*‖w n‖) : ‖v‖ ≤ C*‖w‖ := by
  apply (sq_le_sq₀ (norm_nonneg v) (mul_nonneg hC (norm_nonneg w))).mp
  have hv : Summable (fun n => ‖v n‖^2) := (GW.Analysis.memℓp_two_iff_sq _).mp v.property
  have hw : Summable (fun n => ‖w n‖^2) := (GW.Analysis.memℓp_two_iff_sq _).mp w.property
  have hv' : Summable (fun n => ‖v (n+1)‖^2) := (summable_nat_add_iff 1).mpr hv
  rw [GW.Analysis.lp_norm_sq,mul_pow,GW.Analysis.lp_norm_sq,hv.tsum_eq_zero_add,
    hv0,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),zero_add,← tsum_mul_left]
  apply Summable.tsum_le_tsum _ hv' (hw.mul_left _)
  intro n
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (h n) 2

lemma fractionalRemainder_annihilation_shift_norm {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
    (v w : lp E 2) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ n, ‖v n‖ ≤ C*‖w (n+1)‖) : ‖v‖ ≤ C*‖w‖ := by
  apply (sq_le_sq₀ (norm_nonneg v) (mul_nonneg hC (norm_nonneg w))).mp
  have hv : Summable (fun n => ‖v n‖^2) := (GW.Analysis.memℓp_two_iff_sq _).mp v.property
  have hw : Summable (fun n => ‖w n‖^2) := (GW.Analysis.memℓp_two_iff_sq _).mp w.property
  have hw' : Summable (fun n => ‖w (n+1)‖^2) := (summable_nat_add_iff 1).mpr hw
  rw [GW.Analysis.lp_norm_sq,mul_pow,GW.Analysis.lp_norm_sq]
  calc
    _ ≤ ∑' n, C^2*‖w (n+1)‖^2 := by
      apply Summable.tsum_le_tsum _ hv (hw'.mul_left _)
      intro n
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (h n) 2
    _ = C^2*(∑' n, ‖w (n+1)‖^2) := tsum_mul_left
    _ ≤ C^2*(∑' n, ‖w n‖^2) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg C)
      rw [hw.tsum_eq_zero_add]
      exact le_add_of_nonneg_left (sq_nonneg ‖w 0‖)

end GW.Fock

-- Compiled component Full01
noncomputable section
open MeasureTheory Filter GW.Regularity
open scoped Topology ENNReal BigOperators
namespace GW.Fock

lemma fractionalRemainderPlus_bound (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r) (hr1 : r ≤ 1)
    (f : OneBoson) (u : FreeGraphDomain) :
    ‖fractionalRemainderPlus ε r hε f u‖ ≤
      ‖f‖*‖fractionalRemainderMixedOperator true r (fractionalRemainderMixedInput true r hr.le hr1 u)‖ := by
  let v := freeFourierRepresentation (fractionalRemainderPlus ε r hε f u)
  let w := freeFourierRepresentation
    (fractionalRemainderMixedOperator true r (fractionalRemainderMixedInput true r hr.le hr1 u))
  have hv0 : v 0 = 0 := by
    apply norm_eq_zero.mp
    have h := congrArg norm (fractionalRemainderPlus_zero ε r hε f u)
    simpa only [fractionalRemainderFullSector_norm,norm_zero] using h
  have h := fractionalRemainder_creation_shift_norm v w ‖f‖ (norm_nonneg f) hv0
    (fun n => by simpa only [fractionalRemainderFullSector_norm] using
      fractionalRemainderPlus_sector_bound ε r hε hr hr1 f u n)
  simpa only [v,w,LinearIsometryEquiv.norm_map] using h

lemma fractionalRemainderMinus_bound (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r) (hr1 : r ≤ 1)
    (f : OneBoson) (u : FreeGraphDomain) :
    ‖fractionalRemainderMinus ε r hε f u‖ ≤
      ‖f‖*‖fractionalRemainderMixedOperator false r (fractionalRemainderMixedInput false r hr.le hr1 u)‖ := by
  let v := freeFourierRepresentation (fractionalRemainderMinus ε r hε f u)
  let w := freeFourierRepresentation
    (fractionalRemainderMixedOperator false r (fractionalRemainderMixedInput false r hr.le hr1 u))
  have h := fractionalRemainder_annihilation_shift_norm v w ‖f‖ (norm_nonneg f)
    (fun n => by simpa only [fractionalRemainderFullSector_norm] using
      fractionalRemainderMinus_sector_bound ε r hε hr hr1 f u n)
  simpa only [v,w,LinearIsometryEquiv.norm_map] using h

lemma fractionalRemainderPlus_opNorm (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r) (hr1 : r ≤ 1)
    (f : OneBoson) : ‖fractionalRemainderPlus ε r hε f‖ ≤ ‖f‖ := by
  apply (fractionalRemainderPlus ε r hε f).opNorm_le_bound (norm_nonneg f)
  intro u
  exact (fractionalRemainderPlus_bound ε r hε hr hr1 f u).trans
    (mul_le_mul_of_nonneg_left (fractionalRemainderMixed_bound true r hr.le hr1 u) (norm_nonneg f))

lemma fractionalRemainderMinus_opNorm (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r) (hr1 : r ≤ 1)
    (f : OneBoson) : ‖fractionalRemainderMinus ε r hε f‖ ≤ ‖f‖ := by
  apply (fractionalRemainderMinus ε r hε f).opNorm_le_bound (norm_nonneg f)
  intro u
  exact (fractionalRemainderMinus_bound ε r hε hr hr1 f u).trans
    (mul_le_mul_of_nonneg_left (fractionalRemainderMixed_bound false r hr.le hr1 u) (norm_nonneg f))

lemma fractionalRemainderPlus_family_bound (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r) (hr1 : r ≤ 1)
    (fs : Fin 3 → OneBoson) (u : FreeGraphDomain) :
    ‖annihilationEscapeFamily (fun j => fractionalRemainderPlus ε r hε (fs j) u)‖ ≤
      annihilationEscapeAmplitude fs *
        ‖fractionalRemainderMixedOperator true r (fractionalRemainderMixedInput true r hr.le hr1 u)‖ :=
  annihilationEscape_family_mul_bound _ fs _ (norm_nonneg _)
    (fun j => fractionalRemainderPlus_bound ε r hε hr hr1 (fs j) u)

lemma fractionalRemainderMinus_family_bound (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r) (hr1 : r ≤ 1)
    (fs : Fin 3 → OneBoson) (u : FreeGraphDomain) :
    ‖annihilationEscapeFamily (fun j => fractionalRemainderMinus ε r hε (fs j) u)‖ ≤
      annihilationEscapeAmplitude fs *
        ‖fractionalRemainderMixedOperator false r (fractionalRemainderMixedInput false r hr.le hr1 u)‖ :=
  annihilationEscape_family_mul_bound _ fs _ (norm_nonneg _)
    (fun j => fractionalRemainderMinus_bound ε r hε hr hr1 (fs j) u)

end GW.Fock

-- Compiled component Composition05
noncomputable section
open MeasureTheory Filter GW.Regularity
open scoped Topology ENNReal BigOperators
namespace GW.Fock

lemma fractionalRemainderMixedMinus_composition (r : ℝ) (u : Physical)
    (hn : u ∈ (physicalNumberPower (1/2)).domain)
    (hm : u ∈ (fractionalRemainderMixedOperator false r).domain) :
    ∃ hp : physicalNumberPower (1/2) ⟨u,hn⟩ ∈ (electronRadialPower r).domain,
      electronRadialPower r ⟨physicalNumberPower (1/2) ⟨u,hn⟩,hp⟩ =
        fractionalRemainderMixedOperator false r ⟨u,hm⟩ := by
  have hs : fractionalRemainderMixedSymbol false r = (fun (n : ℕ) (q : GW.Space) => ‖q‖^r*Real.sqrt (n:ℝ)) := by
    funext n q
    simp only [fractionalRemainderMixedSymbol,Bool.false_eq_true,ite_false,add_zero]
  have hop : fractionalRemainderMixedOperator false r =
      physicalSectorMultiplier (fun (n : ℕ) (q : GW.Space) => ‖q‖^r*Real.sqrt (n:ℝ)) := congrArg physicalSectorMultiplier hs
  revert hn hm
  rw [physicalNumberHalf_eq_sectorMultiplier,hop]
  intro hn hm
  simpa only [electronRadialPower] using
    physicalSectorMultiplier_composition (fun n _ => Real.sqrt (n:ℝ)) (fun _ q => ‖q‖^r) u hn hm

lemma fractionalRemainderMixedPlus_composition (r : ℝ) (u : Physical)
    (hn : u ∈ (physicalShiftedNumberPower (1/2)).domain)
    (hm : u ∈ (fractionalRemainderMixedOperator true r).domain) :
    ∃ hp : physicalShiftedNumberPower (1/2) ⟨u,hn⟩ ∈ (electronRadialPower r).domain,
      electronRadialPower r ⟨physicalShiftedNumberPower (1/2) ⟨u,hn⟩,hp⟩ =
        fractionalRemainderMixedOperator true r ⟨u,hm⟩ := by
  have hs : fractionalRemainderMixedSymbol true r = (fun (n : ℕ) (q : GW.Space) => ‖q‖^r*Real.sqrt ((n:ℝ)+1)) := by
    funext n q
    simp only [fractionalRemainderMixedSymbol,ite_true]
  have hop : fractionalRemainderMixedOperator true r =
      physicalSectorMultiplier (fun (n : ℕ) (q : GW.Space) => ‖q‖^r*Real.sqrt ((n:ℝ)+1)) := congrArg physicalSectorMultiplier hs
  revert hn hm
  rw [physicalShiftedNumberHalf_eq_sectorMultiplier,hop]
  intro hn hm
  simpa only [electronRadialPower] using
    physicalSectorMultiplier_composition (fun n _ => Real.sqrt ((n:ℝ)+1)) (fun _ q => ‖q‖^r) u hn hm

/-- Both source remainders are bounded complex-linear maps on the original H2.
The sharp estimates use the actual radial/number mixed operators; their exact
original composition graphs are given by the two composition lemmas above. -/
theorem reg_remainder (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r) (hr1 : r ≤ 1)
    (f : OneBoson) (u : FreeGraphDomain) :
    radialRegularizer ε r hε (commutatorAnnihilatorGraphMap f u) =
      commutatorAnnihilatorGraphMap (fractionalRemainderCoefficientMap ε r hε f) u + fractionalRemainderMinus ε r hε f u ∧
    radialRegularizer ε r hε (commutatorCreatorGraphMap f u) =
      commutatorCreatorGraphMap (fractionalRemainderCoefficientMap ε r hε f) u + fractionalRemainderPlus ε r hε f u ∧
    ‖fractionalRemainderMinus ε r hε f u‖ ≤
      ‖f‖*‖fractionalRemainderMixedOperator false r (fractionalRemainderMixedInput false r hr.le hr1 u)‖ ∧
    ‖fractionalRemainderPlus ε r hε f u‖ ≤
      ‖f‖*‖fractionalRemainderMixedOperator true r (fractionalRemainderMixedInput true r hr.le hr1 u)‖ ∧
    ‖fractionalRemainderMinus ε r hε f‖ ≤ ‖f‖ ∧ ‖fractionalRemainderPlus ε r hε f‖ ≤ ‖f‖ :=
  ⟨fractionalRemainderMinus_identity ε r hε f u,fractionalRemainderPlus_identity ε r hε f u,
    fractionalRemainderMinus_bound ε r hε hr hr1 f u,fractionalRemainderPlus_bound ε r hε hr hr1 f u,
    fractionalRemainderMinus_opNorm ε r hε hr hr1 f,fractionalRemainderPlus_opNorm ε r hε hr hr1 f⟩

end GW.Fock
