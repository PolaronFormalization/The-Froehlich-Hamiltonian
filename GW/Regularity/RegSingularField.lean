module
public import GW.Regularity.RegRegularField
public import GW.Fock.FockCcr
@[expose] public section

-- Compiled component Mass01
noncomputable section
open MeasureTheory Filter GW.Regularity
open scoped Topology ENNReal BigOperators
namespace GW.Fock

def singularFieldDensity (r : ℝ) (f : OneBoson) (k : GW.Space) : ℝ≥0∞ :=
  ENNReal.ofReal ((‖k‖^r*‖f k‖)^2)

def singularFieldRegularizedDensity (r : ℝ) (f : OneBoson) (n : ℕ) (k : GW.Space) : ℝ≥0∞ :=
  ENNReal.ofReal ((rho (radialRegularizerStep n) r ‖k‖*‖f k‖)^2)

def singularFieldMomentMass (r : ℝ) (fs : Fin 3 → OneBoson) : ℝ≥0∞ :=
  ∑ j, ∫⁻ k, singularFieldDensity r (fs j) k ∂(volume : Measure GW.Space)

def singularFieldCoefficients (r : ℝ) (fs : Fin 3 → OneBoson) (n : ℕ) (j : Fin 3) : OneBoson :=
  fractionalRemainderCoefficientMap (radialRegularizerStep n) r (radialRegularizerStep_pos n) (fs j)

def singularFieldAmplitude (r : ℝ) (fs : Fin 3 → OneBoson) (n : ℕ) : ℝ :=
  annihilationEscapeAmplitude (singularFieldCoefficients r fs n)

lemma singularFieldDensity_source (r : ℝ) (f : OneBoson) (k : GW.Space) :
    singularFieldDensity r f k = ENNReal.ofReal (‖k‖^(2*r)*‖f k‖^2) := by
  unfold singularFieldDensity
  rw [mul_pow,show 2*r=r*2 by ring,Real.rpow_mul (norm_nonneg k),Real.rpow_two]

lemma singularFieldRegularizedDensity_measurable (r : ℝ) (f : OneBoson) (n : ℕ) :
    Measurable (singularFieldRegularizedDensity r f n) :=
  ENNReal.continuous_ofReal.measurable.comp
    (((radialRegularizer_measurable (radialRegularizerStep n) r).mul (Lp.stronglyMeasurable f).measurable.norm).pow_const 2)

lemma singularFieldRegularizedDensity_monotone (r : ℝ) (f : OneBoson) :
    Monotone (singularFieldRegularizedDensity r f) := by
  intro a b hab k
  apply ENNReal.ofReal_le_ofReal
  exact pow_le_pow_left₀
    (mul_nonneg (rho_bounds (r := r) (radialRegularizerStep_pos a) (norm_nonneg k)).1 (norm_nonneg _))
    (mul_le_mul_of_nonneg_right (radialRegularizer_scalar_monotone r ‖k‖ (norm_nonneg k) hab) (norm_nonneg _)) 2

lemma singularFieldRegularizedDensity_iSup (r : ℝ) (f : OneBoson) (k : GW.Space) :
    (⨆ n, singularFieldRegularizedDensity r f n k) = singularFieldDensity r f k := by
  exact iSup_eq_of_tendsto (fun a b hab => singularFieldRegularizedDensity_monotone r f hab k)
    (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (((radialRegularizer_scalar_tendsto r ‖k‖).mul_const ‖f k‖).pow 2))

lemma singularFieldRegularizedDensity_mass (r : ℝ) (f : OneBoson) (n : ℕ) :
    (∫⁻ k, singularFieldRegularizedDensity r f n k ∂(volume : Measure GW.Space)) =
      ENNReal.ofReal (‖fractionalRemainderCoefficientMap (radialRegularizerStep n) r (radialRegularizerStep_pos n) f‖^2) := by
  let g := fractionalRemainderCoefficientMap (radialRegularizerStep n) r (radialRegularizerStep_pos n) f
  rw [GW.Analysis.l2_norm_sq (𝕜 := ℂ),ofReal_integral_eq_lintegral_ofReal
    ((Lp.memLp g).integrable_norm_pow (p := 2) (by norm_num)) (Eventually.of_forall (fun k => sq_nonneg ‖g k‖))]
  apply lintegral_congr_ae
  filter_upwards [fractionalRemainderCoefficient_ae (radialRegularizerStep n) r (radialRegularizerStep_pos n) f] with k hk
  change (rho (radialRegularizerStep n) r ‖k‖ : ℂ) • f k = g k at hk
  rw [← hk,norm_smul,Complex.norm_real,
    Real.norm_of_nonneg (rho_bounds (r := r) (radialRegularizerStep_pos n) (norm_nonneg k)).1]
  rfl

lemma singularFieldMomentMass_iSup (r : ℝ) (fs : Fin 3 → OneBoson) :
    singularFieldMomentMass r fs = ⨆ n, ENNReal.ofReal ((singularFieldAmplitude r fs n)^2) := by
  let a (n : ℕ) (j : Fin 3) := ∫⁻ k, singularFieldRegularizedDensity r (fs j) n k ∂(volume : Measure GW.Space)
  have ha : Monotone a := fun _ _ hab j => lintegral_mono (singularFieldRegularizedDensity_monotone r (fs j) hab)
  have hj (j : Fin 3) : (∫⁻ k, singularFieldDensity r (fs j) k ∂(volume : Measure GW.Space)) = ⨆ n, a n j := by
    calc
      _ = ∫⁻ k, ⨆ n, singularFieldRegularizedDensity r (fs j) n k ∂(volume : Measure GW.Space) :=
        lintegral_congr_ae (Eventually.of_forall (fun k => (singularFieldRegularizedDensity_iSup r (fs j) k).symm))
      _ = _ := lintegral_iSup' (fun n => (singularFieldRegularizedDensity_measurable r (fs j) n).aemeasurable)
        (Eventually.of_forall (fun k _ _ hab => singularFieldRegularizedDensity_monotone r (fs j) hab k))
  have hm : (∑ j : Fin 3, ⨆ n, a n j) = ⨆ n, ∑ j : Fin 3, a n j := by
    calc
      _ = ∫⁻ j : Fin 3, ⨆ n, a n j ∂Measure.count := by rw [lintegral_count,tsum_fintype]
      _ = ⨆ n, ∫⁻ j : Fin 3, a n j ∂Measure.count :=
        lintegral_iSup (fun n => measurable_of_countable (a n)) ha
      _ = _ := by simp_rw [lintegral_count,tsum_fintype]
  unfold singularFieldMomentMass
  simp_rw [hj]
  rw [hm]
  congr 1
  funext n
  simp_rw [a,singularFieldRegularizedDensity_mass]
  symm
  have h := ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
    (fun j _ => sq_nonneg ‖singularFieldCoefficients r fs n j‖)
  simpa only [singularFieldAmplitude,annihilationEscapeAmplitude,PiLp.norm_sq_eq_of_L2,
    annihilationEscapeFamily,WithLp.ofLp_toLp,singularFieldCoefficients] using h

end GW.Fock

-- Compiled component Divergence01
noncomputable section
open MeasureTheory Filter GW.Regularity
open scoped Topology ENNReal BigOperators
namespace GW.Fock

lemma singularFieldCoefficient_norm_mono (r : ℝ) (fs : Fin 3 → OneBoson) (j : Fin 3) :
    Monotone (fun n => ‖singularFieldCoefficients r fs n j‖) := by
  intro a b hab
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [fractionalRemainderCoefficient_ae (radialRegularizerStep a) r (radialRegularizerStep_pos a) (fs j),
    fractionalRemainderCoefficient_ae (radialRegularizerStep b) r (radialRegularizerStep_pos b) (fs j)] with k ha hb
  change (rho (radialRegularizerStep a) r ‖k‖ : ℂ) • fs j k = singularFieldCoefficients r fs a j k at ha
  change (rho (radialRegularizerStep b) r ‖k‖ : ℂ) • fs j k = singularFieldCoefficients r fs b j k at hb
  rw [← ha,← hb,norm_smul,norm_smul,Complex.norm_real,Complex.norm_real,
    Real.norm_of_nonneg (rho_bounds (r := r) (radialRegularizerStep_pos a) (norm_nonneg k)).1,
    Real.norm_of_nonneg (rho_bounds (r := r) (radialRegularizerStep_pos b) (norm_nonneg k)).1]
  exact mul_le_mul_of_nonneg_right (radialRegularizer_scalar_monotone r ‖k‖ (norm_nonneg k) hab) (norm_nonneg _)

lemma singularFieldAmplitude_monotone (r : ℝ) (fs : Fin 3 → OneBoson) :
    Monotone (singularFieldAmplitude r fs) := by
  intro a b hab
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖annihilationEscapeFamily (singularFieldCoefficients r fs a)‖^2 ≤
    ‖annihilationEscapeFamily (singularFieldCoefficients r fs b)‖^2
  rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _)
    (singularFieldCoefficient_norm_mono r fs j hab) 2)

lemma singularFieldAmplitude_tendsto (r : ℝ) (fs : Fin 3 → OneBoson)
    (hdiv : singularFieldMomentMass r fs = ∞) : Tendsto (singularFieldAmplitude r fs) atTop atTop := by
  apply (singularFieldAmplitude_monotone r fs).tendsto_atTop_atTop_iff.mpr
  intro L
  have h : ENNReal.ofReal ((max L 0)^2) < ⨆ n, ENNReal.ofReal ((singularFieldAmplitude r fs n)^2) := by
    rw [← singularFieldMomentMass_iSup,hdiv]
    exact ENNReal.ofReal_lt_top
  obtain ⟨n,hn⟩ := lt_iSup_iff.mp h
  have hs : (max L 0)^2 < (singularFieldAmplitude r fs n)^2 :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (sq_nonneg _)).mp hn
  have hm : 0 ≤ max L 0 := le_max_right _ _
  have ha : 0 ≤ singularFieldAmplitude r fs n := norm_nonneg _
  exact ⟨n,(le_max_left L 0).trans ((sq_lt_sq₀ hm ha).mp hs).le⟩

lemma singularField_index_exists (r : ℝ) (fs : Fin 3 → OneBoson)
    (hdiv : singularFieldMomentMass r fs = ∞) (m : ℕ) :
    ∃ n : ℕ, m ≤ n ∧ (m:ℝ)+1 < singularFieldAmplitude r fs n := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((singularFieldAmplitude_tendsto r fs hdiv).eventually_gt_atTop ((m:ℝ)+1))
  exact ⟨max m N,le_max_left _ _,hN (max m N) (le_max_right _ _)⟩

def singularFieldIndex (r : ℝ) (fs : Fin 3 → OneBoson)
    (hdiv : singularFieldMomentMass r fs = ∞) (m : ℕ) : ℕ :=
  Nat.find (singularField_index_exists r fs hdiv m)

lemma singularFieldIndex_spec (r : ℝ) (fs : Fin 3 → OneBoson)
    (hdiv : singularFieldMomentMass r fs = ∞) (m : ℕ) :
    m ≤ singularFieldIndex r fs hdiv m ∧ (m:ℝ)+1 < singularFieldAmplitude r fs (singularFieldIndex r fs hdiv m) :=
  Nat.find_spec (singularField_index_exists r fs hdiv m)

lemma singularFieldIndex_amplitude_pos (r : ℝ) (fs : Fin 3 → OneBoson)
    (hdiv : singularFieldMomentMass r fs = ∞) (m : ℕ) :
    0 < singularFieldAmplitude r fs (singularFieldIndex r fs hdiv m) :=
  (by positivity : (0:ℝ) < (m:ℝ)+1).trans (singularFieldIndex_spec r fs hdiv m).2

def singularFieldNormalized (r : ℝ) (fs : Fin 3 → OneBoson)
    (hdiv : singularFieldMomentMass r fs = ∞) (m : ℕ) (j : Fin 3) : OneBoson :=
  ((singularFieldAmplitude r fs (singularFieldIndex r fs hdiv m))⁻¹ : ℂ) •
    singularFieldCoefficients r fs (singularFieldIndex r fs hdiv m) j

end GW.Fock

-- Compiled component Normalized01
noncomputable section
open MeasureTheory Filter GW.Regularity
open scoped Topology ENNReal BigOperators
namespace GW.Fock

lemma singularField_family_smul (c : ℂ) (fs : Fin 3 → OneBoson) :
    annihilationEscapeFamily (fun j => c • fs j) = c • annihilationEscapeFamily fs := by
  apply PiLp.ext
  intro j
  rfl

lemma singularField_amplitude_smul (c : ℂ) (fs : Fin 3 → OneBoson) :
    annihilationEscapeAmplitude (fun j => c • fs j) = ‖c‖*annihilationEscapeAmplitude fs := by
  change ‖annihilationEscapeFamily (fun j => c • fs j)‖ = _
  rw [singularField_family_smul,norm_smul]
  rfl

lemma singularFieldNormalized_amplitude (r : ℝ) (fs : Fin 3 → OneBoson)
    (hdiv : singularFieldMomentMass r fs = ∞) (m : ℕ) :
    annihilationEscapeAmplitude (singularFieldNormalized r fs hdiv m) = 1 := by
  let n := singularFieldIndex r fs hdiv m
  let A := singularFieldAmplitude r fs n
  have hA : 0 < A := singularFieldIndex_amplitude_pos r fs hdiv m
  change annihilationEscapeAmplitude (fun j => (A⁻¹:ℂ) • singularFieldCoefficients r fs n j) = 1
  rw [singularField_amplitude_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hA.le]
  change A⁻¹*A=1
  exact inv_mul_cancel₀ (ne_of_gt hA)

lemma singularField_low_coefficient_bound (r : ℝ) (hr : 0 < r) (R : ℝ) (hR : 0 < R)
    (f : OneBoson) (n : ℕ) :
    ‖annihilationEscapeLow R (fractionalRemainderCoefficientMap (radialRegularizerStep n) r
      (radialRegularizerStep_pos n) f)‖ ≤ R^r*‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [annihilationEscapeLow_ae R
      (fractionalRemainderCoefficientMap (radialRegularizerStep n) r (radialRegularizerStep_pos n) f),
    fractionalRemainderCoefficient_ae (radialRegularizerStep n) r (radialRegularizerStep_pos n) f] with k hL hg
  rw [hL]
  by_cases hk : ‖k‖ ≤ R
  · rw [ite_eq_left hk,← hg,norm_smul,Complex.norm_real,
      Real.norm_of_nonneg (rho_bounds (r := r) (radialRegularizerStep_pos n) (norm_nonneg k)).1]
    exact mul_le_mul_of_nonneg_right
      (((rho_bounds (r := r) (radialRegularizerStep_pos n) (norm_nonneg k)).2.trans (min_le_left _ _)).trans
        (Real.rpow_le_rpow (norm_nonneg k) hk hr.le)) (norm_nonneg _)
  · rw [ite_eq_right hk,norm_zero]
    exact mul_nonneg (Real.rpow_nonneg hR.le _) (norm_nonneg _)

lemma singularField_low_family_bound (r : ℝ) (hr : 0 < r) (R : ℝ) (hR : 0 < R)
    (fs : Fin 3 → OneBoson) (n : ℕ) :
    annihilationEscapeAmplitude (fun j => annihilationEscapeLow R (singularFieldCoefficients r fs n j)) ≤
      R^r*annihilationEscapeAmplitude fs := by
  have h := annihilationEscape_family_mul_bound
    (fun j => annihilationEscapeLow R (singularFieldCoefficients r fs n j)) fs (R^r)
    (Real.rpow_nonneg hR.le _) (fun j =>
      (singularField_low_coefficient_bound r hr R hR (fs j) n).trans_eq (mul_comm _ _))
  exact h.trans_eq (mul_comm _ _)

lemma singularFieldNormalized_low_bound (r : ℝ) (hr : 0 < r) (R : ℝ) (hR : 0 < R)
    (fs : Fin 3 → OneBoson) (hdiv : singularFieldMomentMass r fs = ∞) (m : ℕ) :
    annihilationEscapeAmplitude (fun j => annihilationEscapeLow R (singularFieldNormalized r fs hdiv m j)) ≤
      (R^r*annihilationEscapeAmplitude fs)/((m:ℝ)+1) := by
  let n := singularFieldIndex r fs hdiv m
  let A := singularFieldAmplitude r fs n
  have hA : 0 < A := singularFieldIndex_amplitude_pos r fs hdiv m
  have hm : 0 < (m:ℝ)+1 := by positivity
  have hlt : (m:ℝ)+1 < A := (singularFieldIndex_spec r fs hdiv m).2
  have he : (fun j => annihilationEscapeLow R (singularFieldNormalized r fs hdiv m j)) =
      (fun j => (A⁻¹:ℂ) • annihilationEscapeLow R (singularFieldCoefficients r fs n j)) := by
    funext j
    exact (annihilationEscapeLow R).map_smul _ _
  rw [he,singularField_amplitude_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hA.le]
  exact ((mul_le_mul_of_nonneg_left (singularField_low_family_bound r hr R hR fs n) (inv_nonneg.mpr hA.le)).trans
    (mul_le_mul_of_nonneg_right ((inv_le_inv₀ hA hm).mpr hlt.le)
      (mul_nonneg (Real.rpow_nonneg hR.le _) (norm_nonneg _)))).trans_eq (by rw [div_eq_mul_inv,mul_comm])

end GW.Fock

-- Compiled component CCR02
noncomputable section
open MeasureTheory Filter GW.Regularity GW.Gross
open scoped Topology ENNReal BigOperators
namespace GW.Fock

lemma singularField_fiber_norm_identity (f : OneBoson) (u : FiberRootDomain) :
    ‖fiberOrdinaryCreator f u‖^2 = ‖fiberOrdinaryAnnihilator f u‖^2 +
      ‖f‖^2*‖(fiberOrdinaryRootInput u).val‖^2 := by
  exact ordinaryCreation_norm_identity f (ordinaryAnnihilationRootInput f (fiberOrdinaryRootInputUnshifted u))
    (creation_mem_shiftedRoot ordinarySectorKernel (ordinaryKernel f) (fiberOrdinaryRootInput u))

lemma singularField_phase_norm_identity (f : OneBoson) (u : FiberPhysicalRoot) :
    ‖commutatorPhaseCreatorMap f u‖^2 = ‖commutatorPhaseAnnihilatorMap f u‖^2 +
      ‖f‖^2*‖(fiberPhysicalRootInput u).val‖^2 := by
  let c := commutatorPhaseCreatorMap f u
  let a := commutatorPhaseAnnihilatorMap f u
  let v := (fiberPhysicalRootInput u).val
  have hiA := (Lp.memLp a).integrable_norm_pow (p := 2) (by norm_num)
  have hiV := (Lp.memLp v).integrable_norm_pow (p := 2) (by norm_num)
  rw [GW.Analysis.l2_norm_sq (𝕜 := ℂ) (commutatorPhaseCreatorMap f u),
    GW.Analysis.l2_norm_sq (𝕜 := ℂ) (commutatorPhaseAnnihilatorMap f u),
    GW.Analysis.l2_norm_sq (𝕜 := ℂ) ((fiberPhysicalRootInput u).val)]
  calc
    _ = ∫ x : GW.Space, (‖a x‖^2+‖f‖^2*‖v x‖^2) ∂volume := by
      apply integral_congr_ae
      filter_upwards [grossFormCreator_ae f u,grossFormAnnihilator_ae f u,fiberRootRepresentative_ambient u]
        with x hc ha hv
      change ‖c x‖^2=‖a x‖^2+‖f‖^2*‖v x‖^2
      change c x = fiberOrdinaryCreator (GW.Analysis.phaseAt f x) (fiberRootRepresentative u x) at hc
      change a x = fiberOrdinaryAnnihilator (GW.Analysis.phaseAt f x) (fiberRootRepresentative u x) at ha
      have hr : (fiberOrdinaryRootInput (fiberRootRepresentative u x)).val = v x := by
        exact (numberDomainInclusion_apply Sector (1/2) (by norm_num) _).symm.trans hv
      rw [hc,ha,singularField_fiber_norm_identity,GW.Analysis.phaseAt_norm,hr]
    _ = _ := by rw [integral_add hiA (hiV.const_mul _),integral_const_mul] <;> rfl

lemma singularField_graph_norm_identity (f : OneBoson) (u : FreeGraphDomain) :
    ‖commutatorCreatorGraphMap f u‖^2 = ‖commutatorAnnihilatorGraphMap f u‖^2 +
      ‖f‖^2*‖freeGraphDomainInclusion u‖^2 := by
  have h := singularField_phase_norm_identity f (commutatorGraphRootMap u)
  simpa only [commutatorCreatorGraphMap,commutatorAnnihilatorGraphMap,ContinuousLinearMap.comp_apply,
    commutatorGraphRootMap_value] using h

lemma singularField_creation_family_lower (fs : Fin 3 → OneBoson) (u : FreeGraphDomain) :
    annihilationEscapeAmplitude fs*‖freeGraphDomainInclusion u‖ ≤
      ‖annihilationEscapeFamily (fun j => commutatorCreatorGraphMap (fs j) u)‖ := by
  apply (sq_le_sq₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)).mp
  rw [mul_pow]
  change ‖annihilationEscapeFamily fs‖^2*‖freeGraphDomainInclusion u‖^2 ≤
    ‖annihilationEscapeFamily (fun j => commutatorCreatorGraphMap (fs j) u)‖^2
  rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  change ‖fs j‖^2*‖freeGraphDomainInclusion u‖^2 ≤ ‖commutatorCreatorGraphMap (fs j) u‖^2
  rw [singularField_graph_norm_identity]
  exact le_add_of_nonneg_left (sq_nonneg _)

end GW.Fock

-- Compiled component Escape03
noncomputable section
open MeasureTheory Filter GW.Regularity
open scoped Topology ENNReal BigOperators
namespace GW.Fock

lemma singularFieldNormalized_low_tendsto (r : ℝ) (hr : 0 < r) (R : ℝ) (hR : 0 < R)
    (fs : Fin 3 → OneBoson) (hdiv : singularFieldMomentMass r fs = ∞) :
    Tendsto (fun m => annihilationEscapeAmplitude
      (fun j => annihilationEscapeLow R (singularFieldNormalized r fs hdiv m j))) atTop (𝓝 0) := by
  have ht : Tendsto (fun m : ℕ => (m:ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun m => le_add_of_nonneg_right zero_le_one) tendsto_natCast_atTop_atTop
  exact squeeze_zero (fun m => norm_nonneg _)
    (fun m => singularFieldNormalized_low_bound r hr R hR fs hdiv m)
    (ht.const_div_atTop (R^r*annihilationEscapeAmplitude fs))

lemma singularFieldNormalized_escape (r : ℝ) (hr : 0 < r)
    (fs : Fin 3 → OneBoson) (hdiv : singularFieldMomentMass r fs = ∞) (R : ℝ) (hR : 0 < R) :
    Tendsto (annihilationEscapeLowRatio (singularFieldNormalized r fs hdiv) R) atTop (𝓝 0) := by
  have he : annihilationEscapeLowRatio (singularFieldNormalized r fs hdiv) R =
      (fun m => (annihilationEscapeAmplitude
        (fun j => annihilationEscapeLow R (singularFieldNormalized r fs hdiv m j)))^2) := by
    funext m
    simp only [annihilationEscapeLowRatio,singularFieldNormalized_amplitude,one_pow,div_one]
  rw [he]
  simpa only [zero_pow (by decide : (2:ℕ) ≠ 0)] using
    (singularFieldNormalized_low_tendsto r hr R hR fs hdiv).pow 2

def singularFieldRootInput (u : FreeGraphDomain) : (physicalNumberPower (1/2)).domain :=
  ⟨freeGraphDomainInclusion u,
    (congrArg (fun v : Physical => v ∈ (physicalNumberPower (1/2)).domain)
      (commutatorGraphRootMap_value u)).mp
        (GW.Gross.grossForm_root_mem_unshifted (commutatorGraphRootMap u))⟩

lemma singularFieldRootInput_value (u : FreeGraphDomain) :
    (singularFieldRootInput u).val = freeGraphDomainInclusion u := rfl

lemma singularField_annihilation_value (f : OneBoson) (u : FreeGraphDomain) :
    generalizedAnnihilation (phaseMultiplicationKernel f) (tailAnnihilationFieldInput f (singularFieldRootInput u)) =
      commutatorAnnihilatorGraphMap f u := by
  exact (generalizedAnnihilation (phaseMultiplicationKernel f)).mem_graph_snd_inj
    ((generalizedAnnihilation (phaseMultiplicationKernel f)).mem_graph (tailAnnihilationFieldInput f (singularFieldRootInput u)))
    (fractionalRemainderAnnihilatorGraph f u) (singularFieldRootInput_value u)

lemma singularField_annihilation_vector (fs : Fin 3 → OneBoson) (u : FreeGraphDomain) :
    annihilationEscapeVector fs (singularFieldRootInput u) =
      annihilationEscapeFamily (fun j => commutatorAnnihilatorGraphMap (fs j) u) := by
  apply PiLp.ext
  intro j
  exact singularField_annihilation_value (fs j) u

lemma singularFieldNormalized_small_annihilation (r : ℝ) (hr : 0 < r)
    (fs : Fin 3 → OneBoson) (hdiv : singularFieldMomentMass r fs = ∞) (u : FreeGraphDomain) :
    Tendsto (fun m => ‖annihilationEscapeFamily
      (fun j => commutatorAnnihilatorGraphMap (singularFieldNormalized r fs hdiv m j) u)‖) atTop (𝓝 0) := by
  have hp : ∀ᶠ m in atTop, 0 < annihilationEscapeAmplitude (singularFieldNormalized r fs hdiv m) :=
    Eventually.of_forall (fun m => by rw [singularFieldNormalized_amplitude]; exact zero_lt_one)
  have h := reg_annihilation_escape (singularFieldNormalized r fs hdiv) hp
    (fun R hR => singularFieldNormalized_escape r hr fs hdiv R hR) (singularFieldRootInput u)
  change Tendsto (fun m : ℕ => ‖annihilationEscapeVector (singularFieldNormalized r fs hdiv m)
    (singularFieldRootInput u)‖ / annihilationEscapeAmplitude (singularFieldNormalized r fs hdiv m)) atTop (𝓝 0) at h
  simp_rw [singularFieldNormalized_amplitude,div_one,singularField_annihilation_vector] at h
  exact h

end GW.Fock

-- Compiled component Rescaling02
noncomputable section
open MeasureTheory Filter GW.Regularity GW.Gross
open scoped Topology ENNReal BigOperators
namespace GW.Fock

lemma singularField_phaseAt_smul (c : ℂ) (f : OneBoson) (x : GW.Space) :
    GW.Analysis.phaseAt (c • f) x = c • GW.Analysis.phaseAt f x := by
  unfold GW.Analysis.phaseAt
  exact ContinuousLinearMap.map_smul _ _ _

lemma singularField_phase_creator_smul (c : ℂ) (f : OneBoson) (u : FiberPhysicalRoot) :
    commutatorPhaseCreatorMap (c • f) u = c • commutatorPhaseCreatorMap f u := by
  apply Lp.ext
  filter_upwards [grossFormCreator_ae (c • f) u,grossFormCreator_ae f u,
    Lp.coeFn_smul c (commutatorPhaseCreatorMap f u)] with x hcf hf hs
  simp only [Pi.smul_apply] at hs
  rw [hcf,hs,hf,singularField_phaseAt_smul,commutatorCreator_smul_coefficient]

lemma singularField_phase_annihilator_real_smul (c : ℝ) (f : OneBoson) (u : FiberPhysicalRoot) :
    commutatorPhaseAnnihilatorMap ((c:ℂ) • f) u = (c:ℂ) • commutatorPhaseAnnihilatorMap f u := by
  apply Lp.ext
  filter_upwards [grossFormAnnihilator_ae ((c:ℂ) • f) u,grossFormAnnihilator_ae f u,
    Lp.coeFn_smul (c:ℂ) (commutatorPhaseAnnihilatorMap f u)] with x hcf hf hs
  simp only [Pi.smul_apply] at hs
  rw [hcf,hs,hf,singularField_phaseAt_smul,commutatorAnnihilator_smul_coefficient]
  exact congrArg (fun z : ℂ => z • fiberOrdinaryAnnihilator (GW.Analysis.phaseAt f x) (fiberRootRepresentative u x))
    (Complex.conj_ofReal c)

lemma singularField_field_real_smul (c : ℝ) (f : OneBoson) (u : FreeGraphDomain) :
    regularFieldGraphMap ((c:ℂ) • f) u = (c:ℂ) • regularFieldGraphMap f u := by
  change commutatorPhaseAnnihilatorMap ((c:ℂ) • f) (commutatorGraphRootMap u) +
    commutatorPhaseCreatorMap ((c:ℂ) • f) (commutatorGraphRootMap u) =
    (c:ℂ) • (commutatorPhaseAnnihilatorMap f (commutatorGraphRootMap u) +
      commutatorPhaseCreatorMap f (commutatorGraphRootMap u))
  rw [singularField_phase_annihilator_real_smul,singularField_phase_creator_smul,smul_add]

lemma singularField_physical_family_smul (c : ℂ) (v : Fin 3 → Physical) :
    annihilationEscapeFamily (fun j => c • v j) = c • annihilationEscapeFamily v := by
  apply PiLp.ext
  intro j
  rfl

lemma singularField_remainder_family_bound (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r) (hr1 : r ≤ 1)
    (fs : Fin 3 → OneBoson) (u : FreeGraphDomain) :
    ‖annihilationEscapeFamily (fun j => fractionalRemainderMinus ε r hε (fs j) u +
      fractionalRemainderPlus ε r hε (fs j) u)‖ ≤
      2*annihilationEscapeAmplitude fs*
        ‖fractionalRemainderMixedOperator true r (fractionalRemainderMixedInput true r hr.le hr1 u)‖ := by
  have he : annihilationEscapeFamily (fun j => fractionalRemainderMinus ε r hε (fs j) u +
      fractionalRemainderPlus ε r hε (fs j) u) =
      annihilationEscapeFamily (fun j => fractionalRemainderMinus ε r hε (fs j) u) +
      annihilationEscapeFamily (fun j => fractionalRemainderPlus ε r hε (fs j) u) := by
    apply PiLp.ext
    intro j
    rfl
  rw [he]
  have hm := (fractionalRemainderMinus_family_bound ε r hε hr hr1 fs u).trans
    (mul_le_mul_of_nonneg_left (regularField_mixed_minus_le_plus r hr.le hr1 u) (norm_nonneg _))
  exact (norm_add_le _ _).trans
    ((add_le_add hm (fractionalRemainderPlus_family_bound ε r hε hr hr1 fs u)).trans_eq (by ring))

lemma singularField_regularization_family_bound (ε r : ℝ) (hε : 0 < ε) (v : Fin 3 → Physical)
    (hv : ∀ j, v j ∈ (electronRadialPower r).domain) :
    ‖annihilationEscapeFamily (fun j => radialRegularizer ε r hε (v j))‖ ≤
      ‖annihilationEscapeFamily (fun j => electronRadialPower r ⟨v j,hv j⟩)‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _)
    (radialRegularizer_bound_on_domain r ε hε ⟨v j,hv j⟩) 2)

lemma singularField_regularized_field_family_bound (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r) (hr1 : r ≤ 1)
    (fs : Fin 3 → OneBoson) (u : FreeGraphDomain)
    (hv : ∀ j, regularFieldGraphMap (fs j) u ∈ (electronRadialPower r).domain) :
    ‖annihilationEscapeFamily (fun j => regularFieldGraphMap (fractionalRemainderCoefficientMap ε r hε (fs j)) u)‖ ≤
      ‖annihilationEscapeFamily (fun j => electronRadialPower r ⟨regularFieldGraphMap (fs j) u,hv j⟩)‖ +
      2*annihilationEscapeAmplitude fs*
        ‖fractionalRemainderMixedOperator true r (fractionalRemainderMixedInput true r hr.le hr1 u)‖ := by
  let A := annihilationEscapeFamily (fun j => regularFieldGraphMap (fractionalRemainderCoefficientMap ε r hε (fs j)) u)
  let M := annihilationEscapeFamily (fun j => radialRegularizer ε r hε (regularFieldGraphMap (fs j) u))
  let E := annihilationEscapeFamily (fun j => fractionalRemainderMinus ε r hε (fs j) u+
    fractionalRemainderPlus ε r hε (fs j) u)
  have he : A = M-E := by
    apply PiLp.ext
    intro j
    exact eq_sub_of_add_eq (regularField_remainder_identity ε r hε (fs j) u).symm
  change ‖A‖ ≤ _
  rw [he]
  exact (norm_sub_le M E).trans
    (add_le_add (singularField_regularization_family_bound ε r hε _ hv)
      (singularField_remainder_family_bound ε r hε hr hr1 fs u))

end GW.Fock

-- Compiled component Main02
noncomputable section
open MeasureTheory Filter GW.Regularity GW.Gross
open scoped Topology ENNReal BigOperators
namespace GW.Fock

lemma singularFieldNormalized_field_bound (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (fs : Fin 3 → OneBoson) (hdiv : singularFieldMomentMass r fs = ∞) (u : FreeGraphDomain)
    (hv : ∀ j, regularFieldGraphMap (fs j) u ∈ (electronRadialPower r).domain) (m : ℕ) :
    ‖annihilationEscapeFamily (fun j => regularFieldGraphMap (singularFieldNormalized r fs hdiv m j) u)‖ ≤
      (‖annihilationEscapeFamily (fun j => electronRadialPower r ⟨regularFieldGraphMap (fs j) u,hv j⟩)‖ +
        2*annihilationEscapeAmplitude fs*
          ‖fractionalRemainderMixedOperator true r (fractionalRemainderMixedInput true r hr.le hr1 u)‖) / ((m:ℝ)+1) := by
  let n := singularFieldIndex r fs hdiv m
  let A := singularFieldAmplitude r fs n
  let L := ‖annihilationEscapeFamily (fun j => electronRadialPower r ⟨regularFieldGraphMap (fs j) u,hv j⟩)‖
  let C := 2*annihilationEscapeAmplitude fs*
    ‖fractionalRemainderMixedOperator true r (fractionalRemainderMixedInput true r hr.le hr1 u)‖
  have hA : 0 < A := singularFieldIndex_amplitude_pos r fs hdiv m
  have hm : 0 < (m:ℝ)+1 := by positivity
  have hlt : (m:ℝ)+1 < A := (singularFieldIndex_spec r fs hdiv m).2
  have hLC : 0 ≤ L+C := by dsimp [L,C]; unfold annihilationEscapeAmplitude; positivity
  have he : annihilationEscapeFamily (fun j => regularFieldGraphMap (singularFieldNormalized r fs hdiv m j) u) =
      (A⁻¹:ℂ) • annihilationEscapeFamily (fun j => regularFieldGraphMap (singularFieldCoefficients r fs n j) u) := by
    rw [← singularField_physical_family_smul]
    apply PiLp.ext
    intro j
    change regularFieldGraphMap (singularFieldNormalized r fs hdiv m j) u =
      (A⁻¹:ℂ) • regularFieldGraphMap (singularFieldCoefficients r fs n j) u
    have h := singularField_field_real_smul (A⁻¹) (singularFieldCoefficients r fs n j) u
    simpa only [singularFieldNormalized,Complex.ofReal_inv] using h
  rw [he,norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hA.le]
  have hb : ‖annihilationEscapeFamily (fun j => regularFieldGraphMap (singularFieldCoefficients r fs n j) u)‖ ≤ L+C :=
    singularField_regularized_field_family_bound (radialRegularizerStep n) r (radialRegularizerStep_pos n)
      hr hr1 fs u hv
  exact ((mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hA.le)).trans
    (mul_le_mul_of_nonneg_right ((inv_le_inv₀ hA hm).mpr hlt.le) hLC)).trans_eq (by rw [div_eq_mul_inv,mul_comm])

lemma singularFieldNormalized_final_bound (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (fs : Fin 3 → OneBoson) (hdiv : singularFieldMomentMass r fs = ∞) (u : FreeGraphDomain)
    (hv : ∀ j, regularFieldGraphMap (fs j) u ∈ (electronRadialPower r).domain) (m : ℕ) :
    ‖freeGraphDomainInclusion u‖ ≤
      ‖annihilationEscapeFamily (fun j => commutatorAnnihilatorGraphMap (singularFieldNormalized r fs hdiv m j) u)‖ +
      (‖annihilationEscapeFamily (fun j => electronRadialPower r ⟨regularFieldGraphMap (fs j) u,hv j⟩)‖ +
        2*annihilationEscapeAmplitude fs*
          ‖fractionalRemainderMixedOperator true r (fractionalRemainderMixedInput true r hr.le hr1 u)‖) / ((m:ℝ)+1) := by
  have hl := singularField_creation_family_lower (singularFieldNormalized r fs hdiv m) u
  rw [singularFieldNormalized_amplitude,one_mul] at hl
  let F := annihilationEscapeFamily (fun j => regularFieldGraphMap (singularFieldNormalized r fs hdiv m j) u)
  let A := annihilationEscapeFamily (fun j => commutatorAnnihilatorGraphMap (singularFieldNormalized r fs hdiv m j) u)
  have he : annihilationEscapeFamily (fun j => commutatorCreatorGraphMap (singularFieldNormalized r fs hdiv m j) u) = F-A := by
    apply PiLp.ext
    intro j
    change commutatorCreatorGraphMap (singularFieldNormalized r fs hdiv m j) u =
      regularFieldGraphMap (singularFieldNormalized r fs hdiv m j) u-
        commutatorAnnihilatorGraphMap (singularFieldNormalized r fs hdiv m j) u
    rw [regularFieldGraphMap_value]
    abel
  rw [he] at hl
  have hF := singularFieldNormalized_field_bound r hr hr1 fs hdiv u hv m
  change ‖F‖ ≤ _ at hF
  exact (hl.trans (norm_sub_le F A)).trans
    ((add_le_add hF (le_refl ‖A‖)).trans_eq (add_comm _ _))

/-- The source divergent-moment obstruction on the original free domain.
The moment is an extended nonnegative integral; no divergent real integral is used. -/
theorem reg_singular_field (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (fs : Fin 3 → OneBoson) (hdiv : singularFieldMomentMass r fs = ∞) (u : FreeGraphDomain)
    (hv : ∀ j, regularFieldGraphMap (fs j) u ∈ (electronRadialPower r).domain) :
    freeGraphDomainInclusion u = 0 := by
  classical
  by_contra hu
  let d := ‖freeGraphDomainInclusion u‖
  have hd : 0 < d := norm_pos_iff.mpr hu
  let L := ‖annihilationEscapeFamily (fun j => electronRadialPower r ⟨regularFieldGraphMap (fs j) u,hv j⟩)‖
  let C := 2*annihilationEscapeAmplitude fs*
    ‖fractionalRemainderMixedOperator true r (fractionalRemainderMixedInput true r hr.le hr1 u)‖
  let a := fun m => ‖annihilationEscapeFamily
    (fun j => commutatorAnnihilatorGraphMap (singularFieldNormalized r fs hdiv m j) u)‖
  have h1 : ∃ N : ℕ, ∀ m ≥ N, a m < d/2 := by
    obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (singularFieldNormalized_small_annihilation r hr fs hdiv u)
      (d/2) (by linarith)
    exact ⟨N,fun m hm => by simpa only [Real.dist_eq,sub_zero,abs_of_nonneg (norm_nonneg _)] using hN m hm⟩
  let m1 := Nat.find h1
  have hm1 := Nat.find_spec h1
  have h2 : ∃ m : ℕ, 2*(L+C)/d < (m:ℝ)+1 := by
    obtain ⟨m,hm⟩ := exists_nat_gt (2*(L+C)/d)
    exact ⟨m,by linarith⟩
  let m2 := Nat.find h2
  have hm2 := Nat.find_spec h2
  let m := max m1 m2
  have ha : a m < d/2 := hm1 m (le_max_left _ _)
  have hnat : (m2:ℝ) ≤ (m:ℝ) := by exact_mod_cast (le_max_right m1 m2)
  have hlt : 2*(L+C)/d < (m:ℝ)+1 := hm2.trans_le (by linarith)
  have hnum := (div_lt_iff₀ hd).mp hlt
  have hrem : (L+C)/((m:ℝ)+1) < d/2 := by
    apply (div_lt_iff₀ (by positivity : 0 < (m:ℝ)+1)).mpr
    nlinarith
  have hb := singularFieldNormalized_final_bound r hr hr1 fs hdiv u hv m
  change d ≤ a m+(L+C)/((m:ℝ)+1) at hb
  linarith

end GW.Fock
