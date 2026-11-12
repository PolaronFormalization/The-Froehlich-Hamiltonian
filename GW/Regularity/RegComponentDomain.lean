module
public import GW.Operators.BasicFree
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators
namespace GW.Fock

def fourierWeightSquare (m : ℕ → GW.Space → ℝ) (u : Physical) (n : ℕ) (q : GW.Space) : ℝ≥0∞ :=
  ENNReal.ofReal (‖(m n q : ℂ) • freeFourierRepresentation u n q‖^2)

def fourierWeightMass (m : ℕ → GW.Space → ℝ) (u : Physical) : ℝ≥0∞ :=
  ∑' n, ∫⁻ q, fourierWeightSquare m u n q ∂(volume : Measure GW.Space)

lemma fourierWeightSquare_aemeasurable (m : ℕ → GW.Space → ℝ) (hm : ∀ n, Measurable (m n))
    (u : Physical) (n : ℕ) : AEMeasurable (fourierWeightSquare m u n) volume :=
  (Complex.continuous_ofReal.measurable.comp (hm n)).aestronglyMeasurable.smul
    (Lp.aestronglyMeasurable (freeFourierRepresentation u n))
  |>.norm.aemeasurable.pow_const 2 |>.ennreal_ofReal

lemma fourierWeightMass_norm (m : ℕ → GW.Space → ℝ) (u : (physicalSectorMultiplier m).domain) :
    fourierWeightMass m u.val = ENNReal.ofReal (‖physicalSectorMultiplier m u‖^2) := by
  let v := freeFourierRepresentation (physicalSectorMultiplier m u)
  have hv (n : ℕ) : (∫⁻ q, fourierWeightSquare m u.val n q ∂(volume : Measure GW.Space)) =
      ENNReal.ofReal (‖v n‖^2) := by
    calc
      _ = ∫⁻ q, ENNReal.ofReal (‖v n q‖^2) ∂(volume : Measure GW.Space) :=
        lintegral_congr_ae ((physicalSectorMultiplier_action m u n).mono
          (fun q h => congrArg (fun z : Sector n => ENNReal.ofReal (‖z‖^2)) h))
      _ = _ := by
        rw [GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
        symm
        exact ofReal_integral_eq_lintegral_ofReal ((Lp.memLp (v n)).integrable_norm_pow (p := 2) (by norm_num))
          (Eventually.of_forall (fun _ => sq_nonneg _))
  change (∑' n, ∫⁻ q, fourierWeightSquare m u.val n q ∂(volume : Measure GW.Space)) = _
  simp_rw [hv]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) ((GW.Analysis.memℓp_two_iff_sq _).mp v.property),
    ← GW.Analysis.lp_norm_sq,LinearIsometryEquiv.norm_map]

lemma physicalSectorMultiplier_mem_of_mass (m : ℕ → GW.Space → ℝ) (hm : ∀ n, Measurable (m n))
    (u : Physical) (hf : fourierWeightMass m u ≠ ∞) :
    u ∈ (physicalSectorMultiplier m).domain := by
  let z := freeFourierRepresentation u
  let f (n : ℕ) (q : GW.Space) := (m n q : ℂ) • z n q
  let S (n : ℕ) := ∫⁻ q, fourierWeightSquare m u n q ∂(volume : Measure GW.Space)
  have hS (n : ℕ) : S n ≠ ∞ := ne_top_of_le_ne_top hf (le_tsum S n)
  have hm' (n : ℕ) : AEStronglyMeasurable (f n) volume :=
    (Complex.continuous_ofReal.measurable.comp (hm n)).aestronglyMeasurable.smul
      (Lp.aestronglyMeasurable (z n))
  have hi (n : ℕ) : Integrable (fun q => ‖f n q‖^2) volume := by
    refine ⟨(hm' n).norm.pow 2,?_⟩
    rw [hasFiniteIntegral_iff_norm]
    have he : (fun q : GW.Space => ENNReal.ofReal ‖‖f n q‖^2‖) = fourierWeightSquare m u n := by
      funext q
      change ENNReal.ofReal ‖‖f n q‖^2‖ = ENNReal.ofReal (‖f n q‖^2)
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (‖f n q‖))]
    rw [he]
    exact lt_top_iff_ne_top.mpr (hS n)
  let w (n : ℕ) := ((memLp_two_iff_integrable_sq_norm (hm' n)).mpr (hi n)).toLp (f n)
  have hw (n : ℕ) : (w n : GW.Space → Sector n) =ᵐ[volume] f n :=
    MemLp.coeFn_toLp ((memLp_two_iff_integrable_sq_norm (hm' n)).mpr (hi n))
  have hn (n : ℕ) : ‖w n‖^2 = (S n).toReal := by
    rw [GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
    calc
      _ = ∫ q, ‖f n q‖^2 ∂(volume : Measure GW.Space) :=
        integral_congr_ae ((hw n).mono (fun q h => by rw [h]))
      _ = _ := by
        change _ = (∫⁻ q, ENNReal.ofReal (‖f n q‖^2) ∂(volume : Measure GW.Space)).toReal
        rw [← ofReal_integral_eq_lintegral_ofReal (hi n) (Eventually.of_forall (fun _ => sq_nonneg _)),
          ENNReal.toReal_ofReal (integral_nonneg (fun _ => sq_nonneg _))]
  have hs : Summable (fun n => ‖w n‖^2) := by
    simp_rw [hn]
    exact ENNReal.summable_toReal hf
  apply (physicalSectorMultiplier_domain m u).mpr
  exact ⟨GW.Analysis.squareSumVector w hs,fun n => (hw n).symm⟩

lemma radial_coordinate_mass (r : ℝ) (hr : 0 ≤ r) (u : Physical) :
    fourierWeightMass (fun _ q => ‖q‖^(1+r)) u =
      ∑ j : Fin 3, fourierWeightMass (fun _ q => ‖q‖^r*q j) u := by
  have hmeas (j : Fin 3) : Measurable (fun q : GW.Space => ‖q‖^r*q j) :=
    (continuous_norm.measurable.pow_const r).mul (PiLp.continuous_apply 2 _ j).measurable
  have he (n : ℕ) (q : GW.Space) : fourierWeightSquare (fun _ q => ‖q‖^(1+r)) u n q =
      ∑ j : Fin 3, fourierWeightSquare (fun _ q => ‖q‖^r*q j) u n q := by
    let z : ℝ := ‖freeFourierRepresentation u n q‖
    let a : ℝ := ‖q‖^r
    let f (j : Fin 3) : ℝ := a^2 * (q j)^2 * z^2
    have hpow : ‖q‖^(1+r) = ‖q‖ * a := by
      change ‖q‖^(1+r) = ‖q‖ * ‖q‖^r
      rw [Real.rpow_add' (norm_nonneg q) (by linarith : 1+r ≠ 0),Real.rpow_one]
    have hcalc : (‖q‖ * a)^2 * z^2 = ∑ j, f j := by
      rw [mul_pow,EuclideanSpace.real_norm_sq_eq q,Finset.sum_mul,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      unfold f
      ring
    calc
      _ = ENNReal.ofReal ((‖q‖ * a)^2 * z^2) := by
        unfold fourierWeightSquare
        rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
        change ENNReal.ofReal ((‖q‖^(1+r))^2 * z^2) = _
        rw [hpow]
      _ = ENNReal.ofReal (∑ j, f j) := congrArg ENNReal.ofReal hcalc
      _ = ∑ j, ENNReal.ofReal (f j) :=
        ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (mul_nonneg (sq_nonneg a) (sq_nonneg (q j))) (sq_nonneg z))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        unfold f a z fourierWeightSquare
        simp only [norm_smul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
  let F (n : ℕ) (j : Fin 3) (q : GW.Space) := fourierWeightSquare (fun _ q => ‖q‖^r*q j) u n q
  let M (n : ℕ) (j : Fin 3) := ∫⁻ q, F n j q ∂(volume : Measure GW.Space)
  have hi (n : ℕ) : (∫⁻ q, fourierWeightSquare (fun _ q => ‖q‖^(1+r)) u n q
      ∂(volume : Measure GW.Space)) = ∑ j : Fin 3, M n j := by
    calc
      _ = ∫⁻ q, ∑ j : Fin 3, F n j q ∂(volume : Measure GW.Space) :=
        lintegral_congr_ae (Eventually.of_forall (he n))
      _ = _ := lintegral_finsetSum' Finset.univ
        (fun j _ => fourierWeightSquare_aemeasurable _ (fun _ => hmeas j) u n)
  change (∑' n, ∫⁻ q, fourierWeightSquare (fun _ q => ‖q‖^(1+r)) u n q ∂(volume : Measure GW.Space)) =
    ∑ j : Fin 3, ∑' n, M n j
  calc
    _ = ∑' n, ∑ j : Fin 3, M n j := tsum_congr hi
    _ = ∑' n, ∑' j : Fin 3, M n j := tsum_congr (fun n => (tsum_fintype (M n)).symm)
    _ = ∑' j : Fin 3, ∑' n, M n j := tsum_comm
    _ = _ := tsum_fintype _

lemma radial_coordinate_forward (r : ℝ) (hr : 0 ≤ r) (u : Physical)
    (hu : u ∈ (physicalSectorMultiplier (fun _ q => ‖q‖^(1+r))).domain) (j : Fin 3) :
    ∃ hj : u ∈ (physicalSectorMultiplier (fun _ q => q j)).domain,
      physicalSectorMultiplier (fun _ q => q j) ⟨u,hj⟩ ∈
        (physicalSectorMultiplier (fun _ q => ‖q‖^r)).domain := by
  let a : ℕ → GW.Space → ℝ := fun _ q => ‖q‖^(1+r)
  let b : ℕ → GW.Space → ℝ := fun _ q => 1+‖q‖^(1+r)
  have hb : u ∈ (physicalSectorMultiplier b).domain := by
    apply (physicalSectorMultiplier_domain b u).mpr
    exact (congrArg (fun (V : Submodule ℂ ElectronBosonSum) => freeFourierRepresentation u ∈ V)
      (sumWeightDomain_add_one a)).mpr ((physicalSectorMultiplier_domain a u).mp hu)
  have hmeas : Measurable (fun q : GW.Space => q j) := (PiLp.continuous_apply 2 _ j).measurable
  have hq (q : GW.Space) : |q j| ≤ ‖q‖ := by
    rw [← Real.norm_eq_abs]
    exact PiLp.norm_apply_le q j
  have hj := (physicalSectorMultiplier_domination (fun _ q => q j) b (fun _ => hmeas) zero_le_one (fun n q => by
    have hn : 0 ≤ b n q := by change 0 ≤ 1+‖q‖^(1+r); positivity
    rw [abs_of_nonneg hn,one_mul]
    apply (hq q).trans
    change ‖q‖ ≤ 1+‖q‖^(1+r)
    by_cases h : ‖q‖ ≤ 1
    · exact h.trans (le_add_of_nonneg_right (Real.rpow_nonneg (norm_nonneg _) _))
    · have hle := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge h) (show (1:ℝ) ≤ 1+r by linarith)
      rw [Real.rpow_one] at hle
      exact hle.trans (le_add_of_nonneg_left zero_le_one)) ⟨u,hb⟩).choose
  have hm := (physicalSectorMultiplier_domination (fun _ q => ‖q‖^r*q j) a
    (fun _ => (continuous_norm.measurable.pow_const r).mul hmeas) zero_le_one (fun n q => by
      have hnn : 0 ≤ a n q := Real.rpow_nonneg (norm_nonneg _) _
      rw [abs_mul,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg q) _),abs_of_nonneg hnn,one_mul]
      refine (mul_le_mul_of_nonneg_left (hq q) (Real.rpow_nonneg (norm_nonneg _) _)).trans_eq ?_
      change _ = ‖q‖^(1+r)
      rw [Real.rpow_add' (norm_nonneg q) (by linarith : 1+r ≠ 0),Real.rpow_one,mul_comm]) ⟨u,hu⟩).choose
  exact ⟨hj,(physicalSectorMultiplier_composition (fun _ q => q j) (fun _ q => ‖q‖^r) u hj hm).choose⟩

lemma radial_coordinate_product_graph (r : ℝ) (u : Physical) (j : Fin 3)
    (hj : u ∈ (physicalSectorMultiplier (fun _ q => q j)).domain)
    (hp : physicalSectorMultiplier (fun _ q => q j) ⟨u,hj⟩ ∈
      (physicalSectorMultiplier (fun _ q => ‖q‖^r)).domain) :
    (u,physicalSectorMultiplier (fun _ q => ‖q‖^r)
      ⟨physicalSectorMultiplier (fun _ q => q j) ⟨u,hj⟩,hp⟩) ∈
        (physicalSectorMultiplier (fun _ q => ‖q‖^r*q j)).graph := by
  let v := physicalSectorMultiplier (fun _ q => q j) ⟨u,hj⟩
  let w := physicalSectorMultiplier (fun _ q => ‖q‖^r) ⟨v,hp⟩
  let m : ℕ → GW.Space → ℝ := fun _ q => ‖q‖^r*q j
  have h (n : ℕ) : (fun q => (m n q : ℂ) • freeFourierRepresentation u n q) =ᵐ[volume]
      freeFourierRepresentation w n := by
    filter_upwards [physicalSectorMultiplier_action (fun _ q => q j) ⟨u,hj⟩ n,
      physicalSectorMultiplier_action (fun _ q => ‖q‖^r) ⟨v,hp⟩ n] with q ha hb
    change (q j : ℂ) • freeFourierRepresentation u n q = freeFourierRepresentation v n q at ha
    change ((‖q‖^r : ℝ) : ℂ) • freeFourierRepresentation v n q = freeFourierRepresentation w n q at hb
    change ((‖q‖^r*q j : ℝ) : ℂ) • freeFourierRepresentation u n q = _
    rw [Complex.ofReal_mul,mul_smul,ha,hb]
  have hm : u ∈ (physicalSectorMultiplier m).domain :=
    (physicalSectorMultiplier_domain m u).mpr ⟨freeFourierRepresentation w,h⟩
  have he : physicalSectorMultiplier m ⟨u,hm⟩ = w := by
    apply freeFourierRepresentation.injective
    apply lp.ext
    funext n
    apply Lp.ext
    exact (physicalSectorMultiplier_action m ⟨u,hm⟩ n).symm.trans (h n)
  exact (physicalSectorMultiplier m).mem_graph_iff.mpr ⟨⟨u,hm⟩,rfl,he⟩

lemma radial_component_domain (r : ℝ) (hr : 0 ≤ r) (u : Physical) :
    u ∈ (physicalSectorMultiplier (fun _ q => ‖q‖^(1+r))).domain ↔
      ∀ j : Fin 3, ∃ hj : u ∈ (physicalSectorMultiplier (fun _ q => q j)).domain,
        physicalSectorMultiplier (fun _ q => q j) ⟨u,hj⟩ ∈
          (physicalSectorMultiplier (fun _ q => ‖q‖^r)).domain := by
  refine ⟨fun hu j => radial_coordinate_forward r hr u hu j,?_⟩
  intro h
  have hm (j : Fin 3) : fourierWeightMass (fun _ q => ‖q‖^r*q j) u ≠ ∞ := by
    obtain ⟨hj,hp⟩ := h j
    let T := physicalSectorMultiplier (fun _ q => ‖q‖^r*q j)
    obtain ⟨v,hv,_⟩ := T.mem_graph_iff.mp (radial_coordinate_product_graph r u j hj hp)
    change v.val = u at hv
    rw [← hv, fourierWeightMass_norm]
    exact ENNReal.ofReal_ne_top
  apply physicalSectorMultiplier_mem_of_mass _ (fun _ => continuous_norm.measurable.pow_const _) u
  rw [radial_coordinate_mass r hr u]
  exact ENNReal.sum_ne_top.mpr (fun j _ => hm j)

lemma radial_component_norm_sq (r : ℝ) (hr : 0 ≤ r)
    (u : (physicalSectorMultiplier (fun _ q => ‖q‖^(1+r))).domain)
    (hj : ∀ j : Fin 3, u.val ∈ (physicalSectorMultiplier (fun _ q => q j)).domain)
    (hp : ∀ j : Fin 3, physicalSectorMultiplier (fun _ q => q j) ⟨u.val,hj j⟩ ∈
      (physicalSectorMultiplier (fun _ q => ‖q‖^r)).domain) :
    ‖physicalSectorMultiplier (fun _ q => ‖q‖^(1+r)) u‖^2 =
      ∑ j : Fin 3, ‖physicalSectorMultiplier (fun _ q => ‖q‖^r)
        ⟨physicalSectorMultiplier (fun _ q => q j) ⟨u.val,hj j⟩,hp j⟩‖^2 := by
  have he (j : Fin 3) : fourierWeightMass (fun _ q => ‖q‖^r*q j) u.val =
      ENNReal.ofReal (‖physicalSectorMultiplier (fun _ q => ‖q‖^r)
        ⟨physicalSectorMultiplier (fun _ q => q j) ⟨u.val,hj j⟩,hp j⟩‖^2) := by
    let T := physicalSectorMultiplier (fun _ q => ‖q‖^r*q j)
    obtain ⟨v,hv,hw⟩ := T.mem_graph_iff.mp (radial_coordinate_product_graph r u.val j (hj j) (hp j))
    change v.val = u.val at hv
    exact (congrArg (fourierWeightMass (fun _ q => ‖q‖^r*q j)) hv.symm).trans
      ((fourierWeightMass_norm _ v).trans (congrArg (fun w : Physical => ENNReal.ofReal (‖w‖^2)) hw))
  have h := radial_coordinate_mass r hr u.val
  rw [fourierWeightMass_norm _ u] at h
  simp_rw [he] at h
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)] at h
  exact ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) |>.mp h

lemma radialPower_zero :
    physicalSectorMultiplier (fun _ q => ‖q‖^(0:ℝ)) =
      (LinearMap.id : Physical →ₗ[ℂ] Physical).toPMap ⊤ := by
  simp only [Real.rpow_zero]
  exact (physicalSectorMultiplier_constant (fun _ => 1)).trans (bochnerDiagonal_one volume Sector)

end GW.Fock
