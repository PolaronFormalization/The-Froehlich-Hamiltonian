module
public import GW.Regularity.Fractional
public import GW.Regularity.RegComponentDomain
@[expose] public section
noncomputable section
open Filter MeasureTheory GW.Regularity
open scoped ENNReal Topology BigOperators
namespace GW.Fock

lemma radialRegularizer_measurable (ε r : ℝ) : Measurable (fun q : GW.Space => rho ε r ‖q‖) := by
  unfold rho
  exact (continuous_norm.measurable.pow_const _).div
    (measurable_const.add (measurable_const.mul (continuous_norm.measurable.pow_const _)))

def radialRegularizerSector (ε r : ℝ) (hε : 0 < ε) (n : ℕ) :
    ElectronSector n →L[ℂ] ElectronSector n :=
  GW.Analysis.boundedMultiplier (fun q : GW.Space => (rho ε r ‖q‖ : ℂ))
    (Complex.continuous_ofReal.measurable.comp (radialRegularizer_measurable ε r))
    (C := ε⁻¹) (Eventually.of_forall (fun q => by
      have h := rho_bounds (r := r) hε (norm_nonneg q)
      rw [Complex.norm_real,Real.norm_of_nonneg h.1]
      exact h.2.trans (min_le_right _ _)))

lemma radialRegularizerSector_norm (ε r : ℝ) (hε : 0 < ε) (n : ℕ) :
    ‖radialRegularizerSector ε r hε n‖ ≤ ε⁻¹ :=
  GW.Analysis.boundedMultiplier_opNorm_le _ _ (inv_nonneg.mpr hε.le) _

def radialRegularizerDiagonal (ε r : ℝ) (hε : 0 < ε) : ElectronBosonSum →L[ℂ] ElectronBosonSum :=
  GW.Spaces.diagonalMap (radialRegularizerSector ε r hε) (inv_nonneg.mpr hε.le) (radialRegularizerSector_norm ε r hε)

def radialRegularizer (ε r : ℝ) (hε : 0 < ε) : Physical →L[ℂ] Physical :=
  freeFourierRepresentation.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((radialRegularizerDiagonal ε r hε).comp freeFourierRepresentation.toLinearIsometry.toContinuousLinearMap)

lemma radialRegularizer_ae (ε r : ℝ) (hε : 0 < ε) (u : Physical) (n : ℕ) :
    (fun q => (rho ε r ‖q‖ : ℂ) • freeFourierRepresentation u n q) =ᵐ[volume]
      freeFourierRepresentation (radialRegularizer ε r hε u) n := by
  have h : freeFourierRepresentation (radialRegularizer ε r hε u) =
      radialRegularizerDiagonal ε r hε (freeFourierRepresentation u) :=
    freeFourierRepresentation.apply_symm_apply _
  rw [h]
  exact GW.Analysis.boundedMultiplier_ae _ _ _ _

lemma radialRegularizer_graph (ε r : ℝ) (hε : 0 < ε) (u : Physical) :
    (u,radialRegularizer ε r hε u) ∈ (physicalSectorMultiplier (fun _ q => rho ε r ‖q‖)).graph := by
  let m : ℕ → GW.Space → ℝ := fun _ q => rho ε r ‖q‖
  let w := radialRegularizer ε r hε u
  have hm : u ∈ (physicalSectorMultiplier m).domain :=
    (physicalSectorMultiplier_domain m u).mpr ⟨freeFourierRepresentation w,radialRegularizer_ae ε r hε u⟩
  have he : physicalSectorMultiplier m ⟨u,hm⟩ = w := by
    apply freeFourierRepresentation.injective
    apply lp.ext
    funext n
    apply Lp.ext
    exact (physicalSectorMultiplier_action m ⟨u,hm⟩ n).symm.trans (radialRegularizer_ae ε r hε u n)
  exact (physicalSectorMultiplier m).mem_graph_iff.mpr ⟨⟨u,hm⟩,rfl,he⟩

def radialRegularizerStep (n : ℕ) : ℝ := 1/((n:ℝ)+1)

lemma radialRegularizerStep_pos (n : ℕ) : 0 < radialRegularizerStep n := by
  unfold radialRegularizerStep
  positivity

lemma radialRegularizerStep_antitone : Antitone radialRegularizerStep := by
  intro a b h
  apply one_div_le_one_div_of_le (by positivity)
  exact add_le_add (Nat.cast_le.mpr h) le_rfl

lemma radialRegularizerStep_tendsto : Tendsto radialRegularizerStep atTop (𝓝[>] (0:ℝ)) :=
  tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
    Eventually.of_forall radialRegularizerStep_pos⟩

lemma radialRegularizer_scalar_tendsto (r : ℝ) (t : ℝ) :
    Tendsto (fun n => rho (radialRegularizerStep n) r t) atTop (𝓝 (t^r)) :=
  (rho_tendsto r t).comp radialRegularizerStep_tendsto

lemma radialRegularizer_scalar_monotone (r t : ℝ) (ht : 0 ≤ t) :
    Monotone (fun n => rho (radialRegularizerStep n) r t) := by
  intro a b h
  exact rho_antitone ht (radialRegularizerStep_pos b) (radialRegularizerStep_pos a) (radialRegularizerStep_antitone h)

lemma radialRegularizer_weightMass (ε r : ℝ) (hε : 0 < ε) (u : Physical) :
    fourierWeightMass (fun _ q => rho ε r ‖q‖) u =
      ENNReal.ofReal (‖radialRegularizer ε r hε u‖^2) := by
  let m : ℕ → GW.Space → ℝ := fun _ q => rho ε r ‖q‖
  obtain ⟨v,hv,hw⟩ := (physicalSectorMultiplier m).mem_graph_iff.mp (radialRegularizer_graph ε r hε u)
  change v.val = u at hv
  change physicalSectorMultiplier m v = radialRegularizer ε r hε u at hw
  exact (congrArg (fourierWeightMass m) hv.symm).trans
    ((fourierWeightMass_norm m v).trans (congrArg (fun z : Physical => ENNReal.ofReal (‖z‖^2)) hw))

lemma radialRegularizerWeightSquare_iSup (r : ℝ) (u : Physical) (n : ℕ) (q : GW.Space) :
    (⨆ l, fourierWeightSquare (fun _ p => rho (radialRegularizerStep l) r ‖p‖) u n q) =
      fourierWeightSquare (fun _ p => ‖p‖^r) u n q := by
  let z : ℝ := ‖freeFourierRepresentation u n q‖
  have h (l : ℕ) : fourierWeightSquare (fun _ p => rho (radialRegularizerStep l) r ‖p‖) u n q =
      ENNReal.ofReal ((rho (radialRegularizerStep l) r ‖q‖ * z)^2) := by
    unfold fourierWeightSquare
    rw [norm_smul,Complex.norm_real]
    change ENNReal.ofReal ((‖rho (radialRegularizerStep l) r ‖q‖‖ * z)^2) = _
    rw [Real.norm_of_nonneg (rho_bounds (radialRegularizerStep_pos l) (norm_nonneg q)).1]
  have h₀ : fourierWeightSquare (fun _ p => ‖p‖^r) u n q = ENNReal.ofReal ((‖q‖^r*z)^2) := by
    unfold fourierWeightSquare
    rw [norm_smul,Complex.norm_real]
    change ENNReal.ofReal ((‖‖q‖^r‖ * z)^2) = _
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg q) _)]
  simp_rw [h,h₀]
  refine iSup_eq_of_tendsto (fun a b hab => ENNReal.ofReal_le_ofReal ?_) ?_
  · exact pow_le_pow_left₀ (mul_nonneg (rho_bounds (radialRegularizerStep_pos a) (norm_nonneg q)).1
      (norm_nonneg _)) (mul_le_mul_of_nonneg_right (radialRegularizer_scalar_monotone r ‖q‖ (norm_nonneg q) hab)
        (norm_nonneg _)) 2
  · exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (((radialRegularizer_scalar_tendsto r ‖q‖).mul_const z).pow 2)

lemma radialRegularizerWeightSquare_monotone (r : ℝ) (u : Physical) (n : ℕ) :
    Monotone (fun l => fourierWeightSquare (fun _ q => rho (radialRegularizerStep l) r ‖q‖) u n) := by
  intro a b hab q
  unfold fourierWeightSquare
  apply ENNReal.ofReal_le_ofReal
  rw [norm_smul,norm_smul,Complex.norm_real,Complex.norm_real]
  change (‖rho (radialRegularizerStep a) r ‖q‖‖ * ‖freeFourierRepresentation u n q‖)^2 ≤
    (‖rho (radialRegularizerStep b) r ‖q‖‖ * ‖freeFourierRepresentation u n q‖)^2
  rw [Real.norm_of_nonneg (rho_bounds (radialRegularizerStep_pos a) (norm_nonneg q)).1,
      Real.norm_of_nonneg (rho_bounds (radialRegularizerStep_pos b) (norm_nonneg q)).1]
  exact pow_le_pow_left₀ (mul_nonneg (rho_bounds (radialRegularizerStep_pos a) (norm_nonneg q)).1 (norm_nonneg _))
    (mul_le_mul_of_nonneg_right (radialRegularizer_scalar_monotone r ‖q‖ (norm_nonneg q) hab) (norm_nonneg _)) 2

lemma radialRegularizer_mass_iSup (r : ℝ) (u : Physical) :
    fourierWeightMass (fun _ q => ‖q‖^r) u =
      ⨆ l, fourierWeightMass (fun _ q => rho (radialRegularizerStep l) r ‖q‖) u := by
  let a (l n : ℕ) := ∫⁻ q, fourierWeightSquare (fun _ p => rho (radialRegularizerStep l) r ‖p‖) u n q
    ∂(volume : Measure GW.Space)
  have ha : Monotone a := fun _ _ hab n => lintegral_mono (radialRegularizerWeightSquare_monotone r u n hab)
  have h (n : ℕ) : (∫⁻ q, fourierWeightSquare (fun _ p => ‖p‖^r) u n q ∂(volume : Measure GW.Space)) =
      ⨆ l, a l n := by
    calc
      _ = ∫⁻ q, ⨆ l, fourierWeightSquare (fun _ p => rho (radialRegularizerStep l) r ‖p‖) u n q
        ∂(volume : Measure GW.Space) :=
        lintegral_congr_ae (Eventually.of_forall (fun q => (radialRegularizerWeightSquare_iSup r u n q).symm))
      _ = _ := lintegral_iSup' (fun l => fourierWeightSquare_aemeasurable _
        (fun _ => radialRegularizer_measurable (radialRegularizerStep l) r) u n)
        (Eventually.of_forall (fun q _ _ hl => radialRegularizerWeightSquare_monotone r u n hl q))
  unfold fourierWeightMass
  simp_rw [h]
  change (∑' n, ⨆ l, a l n) = ⨆ l, ∑' n, a l n
  calc
    _ = ∫⁻ n, ⨆ l, a l n ∂Measure.count := (lintegral_count _).symm
    _ = ⨆ l, ∫⁻ n, a l n ∂Measure.count :=
      lintegral_iSup (fun l => measurable_of_countable (a l)) ha
    _ = _ := by simp_rw [lintegral_count]

lemma radialRegularizer_domain_of_uniform_bound (r : ℝ) (u : Physical) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ ε : ℝ, ∀ hε : 0 < ε, ‖radialRegularizer ε r hε u‖ ≤ C) :
    u ∈ (physicalSectorMultiplier (fun _ q => ‖q‖^r)).domain := by
  apply physicalSectorMultiplier_mem_of_mass _ (fun _ => continuous_norm.measurable.pow_const r) u
  rw [radialRegularizer_mass_iSup]
  apply ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := C^2))
  apply iSup_le
  intro n
  let ε := radialRegularizerStep n
  have hε : 0 < ε := radialRegularizerStep_pos n
  rw [radialRegularizer_weightMass ε r hε u]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (h ε hε) 2)

lemma radialRegularizer_bound_on_domain (r ε : ℝ) (hε : 0 < ε)
    (u : (physicalSectorMultiplier (fun _ q => ‖q‖^r)).domain) :
    ‖radialRegularizer ε r hε u.val‖ ≤ ‖physicalSectorMultiplier (fun _ q => ‖q‖^r) u‖ := by
  let a : ℕ → GW.Space → ℝ := fun _ q => rho ε r ‖q‖
  let b : ℕ → GW.Space → ℝ := fun _ q => ‖q‖^r
  obtain ⟨v,hv⟩ := physicalSectorMultiplier_domination a b (fun _ => radialRegularizer_measurable ε r)
    zero_le_one (fun n q => by
      have h := rho_bounds (r := r) hε (norm_nonneg q)
      rw [abs_of_nonneg (show 0 ≤ a n q from h.1),
        abs_of_nonneg (show 0 ≤ b n q from Real.rpow_nonneg (norm_nonneg q) _),one_mul]
      exact h.2.trans (min_le_left _ _)) u
  have he := (physicalSectorMultiplier a).mem_graph_snd_inj
    (radialRegularizer_graph ε r hε u.val) ((physicalSectorMultiplier a).mem_graph ⟨u.val,v⟩) rfl
  rw [he]
  simpa only [one_mul] using hv

lemma radialRegularizer_domain_iff (r : ℝ) (u : Physical) :
    u ∈ (physicalSectorMultiplier (fun _ q => ‖q‖^r)).domain ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, ∀ hε : 0 < ε, ‖radialRegularizer ε r hε u‖ ≤ C := by
  constructor
  · intro h
    exact ⟨_,norm_nonneg _,fun ε hε => radialRegularizer_bound_on_domain r ε hε ⟨u,h⟩⟩
  · rintro ⟨C,hC,h⟩
    exact radialRegularizer_domain_of_uniform_bound r u C hC h

lemma radialRegularizer_sector_bound (r ε : ℝ) (hε : 0 < ε)
    (u : (physicalSectorMultiplier (fun _ q => ‖q‖^r)).domain) (n : ℕ) :
    ‖freeFourierRepresentation (radialRegularizer ε r hε u.val) n‖ ≤
      ‖freeFourierRepresentation (physicalSectorMultiplier (fun _ q => ‖q‖^r) u) n‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [radialRegularizer_ae ε r hε u.val n,
    physicalSectorMultiplier_action (fun _ q => ‖q‖^r) u n] with q h₁ h₂
  rw [← h₁,← h₂,norm_smul,norm_smul,Complex.norm_real,Complex.norm_real]
  have h := rho_bounds (r := r) hε (norm_nonneg q)
  change ‖rho ε r ‖q‖‖ * ‖freeFourierRepresentation u.val n q‖ ≤ ‖‖q‖^r‖ * ‖freeFourierRepresentation u.val n q‖
  rw [Real.norm_of_nonneg h.1,Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg q) _)]
  exact mul_le_mul_of_nonneg_right (h.2.trans (min_le_left _ _)) (norm_nonneg _)

lemma radialRegularizer_sector_sequence (r : ℝ)
    (u : (physicalSectorMultiplier (fun _ q => ‖q‖^r)).domain) (n : ℕ) :
    Tendsto (fun l : ℕ => freeFourierRepresentation
      (radialRegularizer (radialRegularizerStep l) r (radialRegularizerStep_pos l) u.val) n) atTop
        (𝓝 (freeFourierRepresentation (physicalSectorMultiplier (fun _ q => ‖q‖^r) u) n)) := by
  let y := freeFourierRepresentation (physicalSectorMultiplier (fun _ q => ‖q‖^r) u) n
  let z (l : ℕ) := freeFourierRepresentation
    (radialRegularizer (radialRegularizerStep l) r (radialRegularizerStep_pos l) u.val) n
  let g (q : GW.Space) := ‖y q‖
  have hZ (l : ℕ) : (fun q => (rho (radialRegularizerStep l) r ‖q‖ : ℂ) •
      freeFourierRepresentation u.val n q) =ᵐ[volume] z l :=
    radialRegularizer_ae _ _ _ _ _
  have hY : (fun q => ((‖q‖^r : ℝ) : ℂ) • freeFourierRepresentation u.val n q) =ᵐ[volume] y :=
    physicalSectorMultiplier_action (fun _ q => ‖q‖^r) u n
  have hl : ∀ᵐ q ∂(volume : Measure GW.Space), Tendsto (fun l : ℕ => z l q) atTop (𝓝 (y q)) := by
    filter_upwards [ae_all_iff.mpr hZ,hY] with q hz hy
    change ∀ l, (rho (radialRegularizerStep l) r ‖q‖ : ℂ) • freeFourierRepresentation u.val n q = z l q at hz
    change ((‖q‖^r : ℝ) : ℂ) • freeFourierRepresentation u.val n q = y q at hy
    rw [← hy]
    have hs := Complex.continuous_ofReal.continuousAt.tendsto.comp (radialRegularizer_scalar_tendsto r ‖q‖)
    exact (hs.smul_const (freeFourierRepresentation u.val n q)).congr' (Eventually.of_forall hz)
  have hb (l : ℕ) : ∀ᵐ q ∂(volume : Measure GW.Space), ‖z l q‖ ≤ g q := by
    filter_upwards [hZ l,hY] with q hz hy
    change ‖z l q‖ ≤ ‖y q‖
    rw [← hz,← hy,norm_smul,norm_smul,Complex.norm_real,Complex.norm_real]
    have h := rho_bounds (r := r) (radialRegularizerStep_pos l) (norm_nonneg q)
    rw [Real.norm_of_nonneg h.1,Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg q) _)]
    exact mul_le_mul_of_nonneg_right (h.2.trans (min_le_left _ _)) (norm_nonneg _)
  obtain ⟨hz,hy,hlim⟩ := GW.Analysis.dominated_l2_convergence (𝕜 := ℂ)
    (fun l => Lp.aestronglyMeasurable (z l)) hl (Lp.stronglyMeasurable y).norm.measurable
    ((Lp.memLp y).integrable_norm_pow (p := 2) (by norm_num)) hb
  have hez (l : ℕ) : (hz l).toLp (z l) = z l := Lp.ext (MemLp.coeFn_toLp (hz l))
  have hey : hy.toLp y = y := Lp.ext (MemLp.coeFn_toLp hy)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [hez,hey] using hlim

lemma radialRegularizer_sequence_tendsto (r : ℝ)
    (u : (physicalSectorMultiplier (fun _ q => ‖q‖^r)).domain) :
    Tendsto (fun l : ℕ => radialRegularizer (radialRegularizerStep l) r (radialRegularizerStep_pos l) u.val)
      atTop (𝓝 (physicalSectorMultiplier (fun _ q => ‖q‖^r) u)) := by
  let y := freeFourierRepresentation (physicalSectorMultiplier (fun _ q => ‖q‖^r) u)
  let z (l : ℕ) := freeFourierRepresentation
    (radialRegularizer (radialRegularizerStep l) r (radialRegularizerStep_pos l) u.val)
  have h : Tendsto z atTop (𝓝 y) := GW.Analysis.dominated_lp_tendsto
    ((GW.Analysis.memℓp_two_iff_sq _).mp y.property)
    (fun l n => radialRegularizer_sector_bound r _ (radialRegularizerStep_pos l) u n)
    (radialRegularizer_sector_sequence r u)
  have he := freeFourierRepresentation.symm.continuous.continuousAt.tendsto.comp h
  simpa only [Function.comp_def,z,y,LinearIsometryEquiv.symm_apply_apply] using he

lemma radialRegularizer_error_mono (r ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (h : ε ≤ δ)
    (u : (physicalSectorMultiplier (fun _ q => ‖q‖^r)).domain) :
    ‖radialRegularizer ε r hε u.val - physicalSectorMultiplier (fun _ q => ‖q‖^r) u‖ ≤
      ‖radialRegularizer δ r hδ u.val - physicalSectorMultiplier (fun _ q => ‖q‖^r) u‖ := by
  let z := physicalSectorMultiplier (fun _ q => ‖q‖^r) u
  let x := radialRegularizer ε r hε u.val
  let y := radialRegularizer δ r hδ u.val
  change ‖x-z‖ ≤ ‖y-z‖
  rw [← freeFourierRepresentation.norm_map (x-z),← freeFourierRepresentation.norm_map (y-z),map_sub,map_sub]
  apply lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0)
  intro n
  change ‖freeFourierRepresentation x n-freeFourierRepresentation z n‖ ≤
    ‖freeFourierRepresentation y n-freeFourierRepresentation z n‖
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [radialRegularizer_ae ε r hε u.val n,radialRegularizer_ae δ r hδ u.val n,
    physicalSectorMultiplier_action (fun _ q => ‖q‖^r) u n,
    Lp.coeFn_sub (freeFourierRepresentation x n) (freeFourierRepresentation z n),
    Lp.coeFn_sub (freeFourierRepresentation y n) (freeFourierRepresentation z n)] with q h₁ h₂ h₃ h₄ h₅
  rw [h₄,h₅]
  change ‖freeFourierRepresentation x n q-freeFourierRepresentation z n q‖ ≤
    ‖freeFourierRepresentation y n q-freeFourierRepresentation z n q‖
  change (rho ε r ‖q‖ : ℂ) • freeFourierRepresentation u.val n q = freeFourierRepresentation x n q at h₁
  change (rho δ r ‖q‖ : ℂ) • freeFourierRepresentation u.val n q = freeFourierRepresentation y n q at h₂
  change ((‖q‖^r : ℝ) : ℂ) • freeFourierRepresentation u.val n q = freeFourierRepresentation z n q at h₃
  rw [← h₁,← h₂,← h₃,← sub_smul,← sub_smul,← Complex.ofReal_sub,← Complex.ofReal_sub,
    norm_smul,norm_smul,Complex.norm_real,Complex.norm_real]
  have hb₁ := (rho_bounds (r := r) hε (norm_nonneg q)).2.trans (min_le_left _ _)
  have hb₂ := (rho_bounds (r := r) hδ (norm_nonneg q)).2.trans (min_le_left _ _)
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hb₁),abs_of_nonpos (sub_nonpos.mpr hb₂),
    neg_sub,neg_sub]
  exact mul_le_mul_of_nonneg_right (sub_le_sub_left (rho_antitone (norm_nonneg q) hε hδ h) _)
    (norm_nonneg _)

def radialRegularizerTotal (ε r : ℝ) : Physical →L[ℂ] Physical :=
  if h : 0 < ε then radialRegularizer ε r h else 0

lemma radialRegularizer_tendsto (r : ℝ)
    (u : (physicalSectorMultiplier (fun _ q => ‖q‖^r)).domain) :
    Tendsto (fun ε : ℝ => radialRegularizerTotal ε r u.val) (𝓝[>] 0)
      (𝓝 (physicalSectorMultiplier (fun _ q => ‖q‖^r) u)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply Metric.tendsto_nhds.mpr
  intro a ha
  have hseq := tendsto_iff_norm_sub_tendsto_zero.mp (radialRegularizer_sequence_tendsto r u)
  have hex := (Metric.tendsto_nhds.mp hseq a ha).exists
  obtain ⟨l,hl⟩ := hex
  have hl' : ‖radialRegularizer (radialRegularizerStep l) r (radialRegularizerStep_pos l) u.val -
      physicalSectorMultiplier (fun _ q => ‖q‖^r) u‖ < a := by
    simpa only [Real.dist_eq,sub_zero,abs_norm] using hl
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), 0 < ε := self_mem_nhdsWithin
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), ε < radialRegularizerStep l :=
    nhdsWithin_le_nhds (Iio_mem_nhds (radialRegularizerStep_pos l))
  filter_upwards [hpos,hsmall] with ε he hs
  rw [radialRegularizerTotal,dif_pos he,Real.dist_eq,sub_zero,abs_norm]
  exact (radialRegularizer_error_mono r ε _ he (radialRegularizerStep_pos l) hs.le u).trans_lt hl'

lemma radialRegularizer_sq_norm_tendsto (r : ℝ)
    (u : (physicalSectorMultiplier (fun _ q => ‖q‖^r)).domain) :
    Tendsto (fun ε : ℝ => ‖radialRegularizerTotal ε r u.val‖^2) (𝓝[>] 0)
      (𝓝 (‖physicalSectorMultiplier (fun _ q => ‖q‖^r) u‖^2)) :=
  (radialRegularizer_tendsto r u).norm.pow 2

lemma radialRegularizer_family_domain_iff {J : Type*} [Fintype J] (r : ℝ) (u : J → Physical) :
    (∀ j, u j ∈ (physicalSectorMultiplier (fun _ q => ‖q‖^r)).domain) ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, ∀ hε : 0 < ε, ∑ j, ‖radialRegularizer ε r hε (u j)‖^2 ≤ C := by
  constructor
  · intro hu
    let y (j : J) := physicalSectorMultiplier (fun _ q => ‖q‖^r) ⟨u j,hu j⟩
    refine ⟨∑ j, ‖y j‖^2,Finset.sum_nonneg (fun _ _ => sq_nonneg _),?_⟩
    intro ε hε
    apply Finset.sum_le_sum
    intro j _
    exact pow_le_pow_left₀ (norm_nonneg _) (radialRegularizer_bound_on_domain r ε hε ⟨u j,hu j⟩) 2
  · rintro ⟨C,hC,hb⟩ j
    apply radialRegularizer_domain_of_uniform_bound r (u j) (Real.sqrt C) (Real.sqrt_nonneg C)
    intro ε hε
    apply Real.le_sqrt_of_sq_le
    exact (Finset.single_le_sum (fun j _ => sq_nonneg ‖radialRegularizer ε r hε (u j)‖)
      (Finset.mem_univ j)).trans (hb ε hε)

lemma radialRegularizer_family_sq_norm_tendsto {J : Type*} [Fintype J] (r : ℝ)
    (u : J → (physicalSectorMultiplier (fun _ q => ‖q‖^r)).domain) :
    Tendsto (fun ε : ℝ => ∑ j, ‖radialRegularizerTotal ε r (u j).val‖^2) (𝓝[>] 0)
      (𝓝 (∑ j, ‖physicalSectorMultiplier (fun _ q => ‖q‖^r) (u j)‖^2)) := by
  have h (s : Finset J) : Tendsto (fun ε : ℝ => ∑ j ∈ s, ‖radialRegularizerTotal ε r (u j).val‖^2) (𝓝[>] 0)
      (𝓝 (∑ j ∈ s, ‖physicalSectorMultiplier (fun _ q => ‖q‖^r) (u j)‖^2)) := by
    classical
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using (tendsto_const_nhds (x := (0:ℝ)))
    | insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      exact (radialRegularizer_sq_norm_tendsto r (u j)).add ih
  exact h Finset.univ

end GW.Fock
