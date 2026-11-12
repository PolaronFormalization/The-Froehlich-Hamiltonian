module
public import GW.Analysis.L2Quotient
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
@[expose] public section
noncomputable section
open MeasureTheory
open scoped Topology InnerProductSpace ENNReal
namespace GW.Analysis
section Coordinates
variable {E : ℕ → Type*} [∀ m, NormedAddCommGroup (E m)]

lemma memℓp_two_iff_sq (z : ∀ m, E m) : Memℓp z 2 ↔ Summable (fun m => ‖z m‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
    (memℓp_gen_iff (show 0 < (2 : ℝ≥0∞).toReal by norm_num) (f := z))

lemma dominated_memℓp {b : ℕ → ℝ} (hb : Summable (fun m => b m ^ 2))
    {z : ∀ m, E m} (hz : ∀ m, ‖z m‖ ≤ b m) : Memℓp z 2 := by
  apply (memℓp_two_iff_sq z).mpr
  exact Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun m =>
    pow_le_pow_left₀ (norm_nonneg _) (hz m) 2) hb

/-- Construct the actual dependent ℓ² vector only after summability is proved. -/
def squareSumVector (z : ∀ m, E m) (hz : Summable (fun m => ‖z m‖ ^ 2)) : lp E 2 :=
  ⟨z,(memℓp_two_iff_sq z).mpr hz⟩

lemma lp_norm_sq (z : lp E 2) : ‖z‖ ^ 2 = ∑' m, ‖z m‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
    lp.norm_rpow_eq_tsum (show 0 < (2 : ℝ≥0∞).toReal by norm_num) z

lemma dominated_coordinate_limit {z : ℕ → ∀ m, E m} {v : ∀ m, E m} {b : ℕ → ℝ}
    (hb : Summable (fun m => b m ^ 2)) (hz : ∀ n m, ‖z n m‖ ≤ b m)
    (ht : ∀ m, Filter.Tendsto (fun n => z n m) Filter.atTop (𝓝 (v m))) :
    (∀ m, ‖v m‖ ≤ b m) ∧ (∀ n, Memℓp (z n) 2) ∧ Memℓp v 2 := by
  have hv : ∀ m, ‖v m‖ ≤ b m := fun m =>
    le_of_tendsto ((ht m).norm) (Filter.Eventually.of_forall (fun n => hz n m))
  exact ⟨hv,(fun n => dominated_memℓp hb (hz n)),dominated_memℓp hb hv⟩

lemma dominated_lp_tendsto {z : ℕ → lp E 2} {v : lp E 2} {b : ℕ → ℝ}
    (hb : Summable (fun m => b m ^ 2)) (hz : ∀ n m, ‖z n m‖ ≤ b m)
    (ht : ∀ m, Filter.Tendsto (fun n => z n m) Filter.atTop (𝓝 (v m))) :
    Filter.Tendsto z Filter.atTop (𝓝 v) := by
  have hv := (dominated_coordinate_limit hb hz ht).1
  have hsum : Summable (fun m => 4 * b m ^ 2) := hb.mul_left 4
  have hd : ∀ n m, ‖z n m-v m‖ ^ 2 ≤ 4 * b m ^ 2 := by
    intro n m
    have h := (norm_sub_le (z n m) (v m)).trans (add_le_add (hz n m) (hv m))
    have hp := norm_nonneg (z n m-v m)
    nlinarith
  have hs : Filter.Tendsto (fun n => ∑' m, ‖z n m-v m‖ ^ 2) Filter.atTop (𝓝 0) := by
    have hs' := tendsto_tsum_of_dominated_convergence
      (f := fun n m => ‖z n m-v m‖ ^ 2) (g := fun _ => (0 : ℝ)) hsum
      (fun m => by
        have hc : Filter.Tendsto (fun _ : ℕ => v m) Filter.atTop (𝓝 (v m)) := tendsto_const_nhds
        simpa using (((ht m).sub hc).norm.pow 2))
      (Filter.Eventually.of_forall (fun n m => by
        simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (‖z n m-v m‖))] using hd n m))
    simpa only [tsum_zero] using hs'
  have hsq : Filter.Tendsto (fun n => ‖z n-v‖ ^ 2) Filter.atTop (𝓝 0) := by
    simpa only [lp_norm_sq,lp.coeFn_sub,Pi.sub_apply,sub_self,norm_zero,zero_pow,
      ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,tsum_zero] using hs
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hroot
lemma dominated_series_exists {z : ℕ → ∀ m, E m} {v : ∀ m, E m} {b : ℕ → ℝ}
    (hb : Summable (fun m => b m ^ 2)) (hz : ∀ n m, ‖z n m‖ ≤ b m)
    (ht : ∀ m, Filter.Tendsto (fun n => z n m) Filter.atTop (𝓝 (v m))) :
    ∃ (Z : ℕ → lp E 2) (V : lp E 2),
      (∀ n m, Z n m = z n m) ∧ (∀ m, V m = v m) ∧
      Filter.Tendsto Z Filter.atTop (𝓝 V) := by
  have hd := dominated_coordinate_limit hb hz ht
  let Z : ℕ → lp E 2 := fun n => ⟨z n,hd.2.1 n⟩
  let V : lp E 2 := ⟨v,hd.2.2⟩
  exact ⟨Z,V,(fun _ _ => rfl),(fun _ => rfl),dominated_lp_tendsto hb hz ht⟩
end Coordinates
section Reconstruction
variable {E : ℕ → Type*} [∀ m, NormedAddCommGroup (E m)]
  [∀ m, NormedSpace ℂ (E m)]
  {X : Type*} [MeasurableSpace X] {μ : Measure X}

def dependentReconstruction (u : ∀ m, X → E m) (x : X) : lp E 2 :=
  by
  classical
  exact if h : Memℓp (fun m => u m x) 2 then ⟨(fun m => u m x),h⟩ else 0

omit [∀ m, NormedSpace ℂ (E m)] [MeasurableSpace X] in
lemma reconstruction_apply (u : ∀ m, X → E m) {x : X}
    (hx : Memℓp (fun m => u m x) 2) (m : ℕ) : dependentReconstruction u x m = u m x := by
  simp only [dependentReconstruction,dite_eq_left hx]

omit [∀ m, NormedSpace ℂ (E m)] in
lemma reconstruction_good {u : ∀ m, X → E m}
    (hu : ∀ m, AEStronglyMeasurable (u m) μ)
    (hf : (∑' m, ∫⁻ x, ENNReal.ofReal (‖u m x‖ ^ 2) ∂μ) < ∞) :
    ∀ᵐ x ∂μ, Memℓp (fun m => u m x) 2 := by
  have hm : ∀ m, AEMeasurable (fun x => ENNReal.ofReal (‖u m x‖ ^ 2)) μ :=
    fun m => ((hu m).norm.pow 2).aemeasurable.ennreal_ofReal
  have hi : (∫⁻ x, ∑' m, ENNReal.ofReal (‖u m x‖ ^ 2) ∂μ) < ∞ := by
    rw [lintegral_tsum hm]
    exact hf
  filter_upwards [ae_lt_top' (AEMeasurable.tsum hm) hi.ne] with x hx
  apply (memℓp_two_iff_sq _).mpr
  have hs := ENNReal.summable_toReal hx.ne
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using hs

def coordinatePartial (u : ∀ m, X → E m) (M : ℕ) (x : X) : lp E 2 :=
  ∑ m ∈ Finset.range M, lp.single 2 m (u m x)

lemma coordinatePartial_measurable {u : ∀ m, X → E m}
    (hu : ∀ m, AEStronglyMeasurable (u m) μ) (M : ℕ) :
    AEStronglyMeasurable (coordinatePartial u M) μ := by
  apply Finset.aestronglyMeasurable_fun_sum
  intro m hm
  exact (lp.singleContinuousLinearMap ℂ E 2 m).continuous.comp_aestronglyMeasurable (hu m)

omit [∀ m, NormedSpace ℂ (E m)] [MeasurableSpace X] in
lemma coordinatePartial_tendsto (u : ∀ m, X → E m) {x : X}
    (hx : Memℓp (fun m => u m x) 2) :
    Filter.Tendsto (fun M => coordinatePartial u M x) Filter.atTop (𝓝 (dependentReconstruction u x)) := by
  have h := (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (dependentReconstruction u x)).tendsto_sum_nat
  simpa only [coordinatePartial,reconstruction_apply u hx] using h

lemma reconstruction_aestronglyMeasurable {u : ∀ m, X → E m}
    (hu : ∀ m, AEStronglyMeasurable (u m) μ)
    (hf : (∑' m, ∫⁻ x, ENNReal.ofReal (‖u m x‖ ^ 2) ∂μ) < ∞) :
    AEStronglyMeasurable (dependentReconstruction u) μ :=
  aestronglyMeasurable_of_tendsto_ae Filter.atTop (coordinatePartial_measurable hu)
    ((reconstruction_good hu hf).mono (fun _ hx => coordinatePartial_tendsto u hx))

omit [∀ m, NormedSpace ℂ (E m)] in
lemma reconstruction_coordinates {u : ∀ m, X → E m}
    (hu : ∀ m, AEStronglyMeasurable (u m) μ)
    (hf : (∑' m, ∫⁻ x, ENNReal.ofReal (‖u m x‖ ^ 2) ∂μ) < ∞) :
    ∀ᵐ x ∂μ, ∀ m, dependentReconstruction u x m = u m x :=
  (reconstruction_good hu hf).mono (fun _ hx m => reconstruction_apply u hx m)

omit [∀ m, NormedSpace ℂ (E m)] in
lemma reconstruction_norm_sq {u : ∀ m, X → E m}
    (hu : ∀ m, AEStronglyMeasurable (u m) μ)
    (hf : (∑' m, ∫⁻ x, ENNReal.ofReal (‖u m x‖ ^ 2) ∂μ) < ∞) :
    (fun x => ‖dependentReconstruction u x‖ ^ 2) =ᵐ[μ] (fun x => ∑' m, ‖u m x‖ ^ 2) := by
  filter_upwards [reconstruction_coordinates hu hf] with x hx
  rw [lp_norm_sq]
  exact tsum_congr (fun m => congrArg (fun v : E m => ‖v‖ ^ 2) (hx m))

omit [∀ m, NormedSpace ℂ (E m)] in
lemma reconstruction_lintegral {u : ∀ m, X → E m}
    (hu : ∀ m, AEStronglyMeasurable (u m) μ)
    (hf : (∑' m, ∫⁻ x, ENNReal.ofReal (‖u m x‖ ^ 2) ∂μ) < ∞) :
    (∫⁻ x, ENNReal.ofReal (‖dependentReconstruction u x‖ ^ 2) ∂μ) =
      ∑' m, ∫⁻ x, ENNReal.ofReal (‖u m x‖ ^ 2) ∂μ := by
  calc
    _ = ∫⁻ x, ∑' m, ENNReal.ofReal (‖u m x‖ ^ 2) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [reconstruction_good hu hf] with x hx
      rw [lp_norm_sq]
      simp_rw [reconstruction_apply u hx]
      exact ENNReal.ofReal_tsum_of_nonneg (fun m => sq_nonneg _) ((memℓp_two_iff_sq _).mp hx)
    _ = _ := lintegral_tsum (fun m => ((hu m).norm.pow 2).aemeasurable.ennreal_ofReal)

lemma reconstruction_square_integrable {u : ∀ m, X → E m}
    (hu : ∀ m, AEStronglyMeasurable (u m) μ)
    (hf : (∑' m, ∫⁻ x, ENNReal.ofReal (‖u m x‖ ^ 2) ∂μ) < ∞) :
    Integrable (fun x => ‖dependentReconstruction u x‖ ^ 2) μ := by
  refine ⟨(reconstruction_aestronglyMeasurable hu hf).norm.pow 2, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).mpr
  rw [reconstruction_lintegral hu hf]
  exact hf

lemma reconstruction_integral {u : ∀ m, X → E m}
    (hu : ∀ m, AEStronglyMeasurable (u m) μ)
    (hf : (∑' m, ∫⁻ x, ENNReal.ofReal (‖u m x‖ ^ 2) ∂μ) < ∞) :
    (∫ x, ‖dependentReconstruction u x‖ ^ 2 ∂μ) = ∑' m, ∫ x, ‖u m x‖ ^ 2 ∂μ := by
  calc
    _ = (∫⁻ x, ENNReal.ofReal (‖dependentReconstruction u x‖ ^ 2) ∂μ).toReal :=
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
        ((reconstruction_aestronglyMeasurable hu hf).norm.pow 2)
    _ = (∑' m, ∫⁻ x, ENNReal.ofReal (‖u m x‖ ^ 2) ∂μ).toReal :=
      congrArg ENNReal.toReal (reconstruction_lintegral hu hf)
    _ = ∑' m, (∫⁻ x, ENNReal.ofReal (‖u m x‖ ^ 2) ∂μ).toReal :=
      ENNReal.tsum_toReal_eq (ne_top_of_tsum_ne_top hf.ne)
    _ = _ := tsum_congr (fun m => (integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) ((hu m).norm.pow 2)).symm)

lemma reconstruction_memLp {u : ∀ m, X → E m}
    (hu : ∀ m, AEStronglyMeasurable (u m) μ)
    (hf : (∑' m, ∫⁻ x, ENNReal.ofReal (‖u m x‖ ^ 2) ∂μ) < ∞) :
    MemLp (dependentReconstruction u) 2 μ :=
  (memLp_two_iff_integrable_sq_norm (reconstruction_aestronglyMeasurable hu hf)).mpr
    (reconstruction_square_integrable hu hf)

/-- Form the Bochner L² class only after both analytic obligations are proved. -/
def reconstructionL2 {u : ∀ m, X → E m}
    (hu : ∀ m, AEStronglyMeasurable (u m) μ)
    (hf : (∑' m, ∫⁻ x, ENNReal.ofReal (‖u m x‖ ^ 2) ∂μ) < ∞) : Lp (lp E 2) 2 μ :=
  l2Class (reconstruction_aestronglyMeasurable hu hf) (reconstruction_square_integrable hu hf)

lemma reconstructionL2_coordinates {u : ∀ m, X → E m}
    (hu : ∀ m, AEStronglyMeasurable (u m) μ)
    (hf : (∑' m, ∫⁻ x, ENNReal.ofReal (‖u m x‖ ^ 2) ∂μ) < ∞) :
    ∀ᵐ x ∂μ, ∀ m, reconstructionL2 hu hf x m = u m x := by
  filter_upwards [l2Class_ae (reconstruction_aestronglyMeasurable hu hf)
    (reconstruction_square_integrable hu hf),reconstruction_coordinates hu hf] with x hx hc
  intro m
  exact congrArg (fun v : lp E 2 => v m) hx |>.trans (hc m)

omit [∀ m, NormedSpace ℂ (E m)] in
lemma finite_square_integrals_of_real {u : ∀ m, X → E m}
    (hi : ∀ m, Integrable (fun x => ‖u m x‖ ^ 2) μ)
    (hs : Summable (fun m => ∫ x, ‖u m x‖ ^ 2 ∂μ)) :
    (∑' m, ∫⁻ x, ENNReal.ofReal (‖u m x‖ ^ 2) ∂μ) < ∞ := by
  have he (m : ℕ) : (∫⁻ x, ENNReal.ofReal (‖u m x‖ ^ 2) ∂μ) =
      ENNReal.ofReal (∫ x, ‖u m x‖ ^ 2 ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal (hi m)
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).symm
  simp_rw [he]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => integral_nonneg (fun _ => sq_nonneg _)) hs]
  exact ENNReal.ofReal_lt_top

lemma reconstruction_from_real_integrals {u : ∀ m, X → E m}
    (hu : ∀ m, AEStronglyMeasurable (u m) μ)
    (hi : ∀ m, Integrable (fun x => ‖u m x‖ ^ 2) μ)
    (hs : Summable (fun m => ∫ x, ‖u m x‖ ^ 2 ∂μ)) :
    ∃ U : Lp (lp E 2) 2 μ, (∀ᵐ x ∂μ, ∀ m, U x m = u m x) ∧
      (∫ x, ‖U x‖ ^ 2 ∂μ) = ∑' m, ∫ x, ‖u m x‖ ^ 2 ∂μ := by
  let hf := finite_square_integrals_of_real hi hs
  refine ⟨reconstructionL2 hu hf,reconstructionL2_coordinates hu hf,?_⟩
  calc
    _ = ∫ x, ‖dependentReconstruction u x‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      exact (l2Class_ae (reconstruction_aestronglyMeasurable hu hf)
        (reconstruction_square_integrable hu hf)).mono (fun _ hx => congrArg (fun v : lp E 2 => ‖v‖ ^ 2) hx)
    _ = _ := reconstruction_integral hu hf

lemma reconstruction_strong_representative {u : ∀ m, X → E m}
    (hu : ∀ m, AEStronglyMeasurable (u m) μ)
    (hf : (∑' m, ∫⁻ x, ENNReal.ofReal (‖u m x‖ ^ 2) ∂μ) < ∞) :
    ∃ g : X → lp E 2, StronglyMeasurable g ∧
      (∀ᵐ x ∂μ, ∀ m, g x m = u m x) ∧
      (∫ x, ‖g x‖ ^ 2 ∂μ) = ∑' m, ∫ x, ‖u m x‖ ^ 2 ∂μ := by
  obtain ⟨g,hg,he⟩ := l2_strong_representative (reconstruction_aestronglyMeasurable hu hf)
  refine ⟨g,hg,?_,?_⟩
  · filter_upwards [he,reconstruction_coordinates hu hf] with x hx hc
    intro m
    exact (congrArg (fun v : lp E 2 => v m) hx).symm.trans (hc m)
  · exact (integral_congr_ae (he.symm.mono (fun _ hx => congrArg
      (fun v : lp E 2 => ‖v‖ ^ 2) hx))).trans (reconstruction_integral hu hf)

end Reconstruction

end GW.Analysis
