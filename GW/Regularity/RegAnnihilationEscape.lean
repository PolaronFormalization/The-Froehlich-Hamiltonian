module
public import GW.Regularity.RegTailAnnihilation
public import GW.Gross.MainDerivativeAnnihilation
@[expose] public section

-- Compiled component Coefficients02
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Fock

def annihilationEscapeFamily {H : Type*} (v : Fin 3 → H) : PiLp 2 (fun _ : Fin 3 => H) :=
  WithLp.toLp 2 v

lemma annihilationEscapeFamily_norm {H : Type*} [NormedAddCommGroup H] (v : Fin 3 → H) :
    ‖annihilationEscapeFamily v‖ = Real.sqrt (∑ j : Fin 3, ‖v j‖^2) :=
  PiLp.norm_eq_of_L2 _

lemma annihilationEscapeFamily_bound {H : Type*} [NormedAddCommGroup H]
    (v : Fin 3 → H) (b : Fin 3 → ℝ) (hb : ∀ j, 0 ≤ b j)
    (h : ∀ j, ‖v j‖ ≤ b j) :
    ‖annihilationEscapeFamily v‖ ≤ Real.sqrt (∑ j : Fin 3, b j ^ 2) := by
  rw [annihilationEscapeFamily_norm]
  exact Real.sqrt_le_sqrt (Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (h j) 2))

def annihilationEscapeLowSymbol (R : ℝ) (k : GW.Space) : ℂ := if ‖k‖ ≤ R then 1 else 0
lemma annihilationEscapeLowSymbol_measurable (R : ℝ) : Measurable (annihilationEscapeLowSymbol R) :=
  measurable_const.ite (measurableSet_le measurable_norm measurable_const) measurable_const
lemma annihilationEscapeLowSymbol_bound (R : ℝ) (k : GW.Space) : ‖annihilationEscapeLowSymbol R k‖ ≤ 1 := by
  unfold annihilationEscapeLowSymbol
  split <;> norm_num

def annihilationEscapeLow (R : ℝ) : OneBoson →L[ℂ] OneBoson :=
  GW.Analysis.boundedMultiplier (annihilationEscapeLowSymbol R) (annihilationEscapeLowSymbol_measurable R)
    (Eventually.of_forall (annihilationEscapeLowSymbol_bound R))

def annihilationEscapeHigh (R : ℝ) : OneBoson →L[ℂ] OneBoson := tailAnnihilationProjection (E := ℂ) R

lemma annihilationEscapeLow_ae (R : ℝ) (f : OneBoson) :
    annihilationEscapeLow R f =ᵐ[(volume : Measure GW.Space)] fun k => if ‖k‖ ≤ R then f k else 0 := by
  have h := (GW.Analysis.boundedMultiplier_ae (annihilationEscapeLowSymbol R)
    (annihilationEscapeLowSymbol_measurable R) (Eventually.of_forall (annihilationEscapeLowSymbol_bound R)) f).symm
  filter_upwards [h] with k hk
  change annihilationEscapeLow R f k = annihilationEscapeLowSymbol R k • f k at hk
  rw [hk]
  unfold annihilationEscapeLowSymbol
  split <;> simp only [one_smul,zero_smul]

lemma annihilationEscapeHigh_ae (R : ℝ) (f : OneBoson) :
    annihilationEscapeHigh R f =ᵐ[(volume : Measure GW.Space)] fun k => if R < ‖k‖ then f k else 0 := by
  filter_upwards [tailAnnihilationProjection_ae R f] with k hk
  change annihilationEscapeHigh R f k = tailAnnihilationSymbol R k • f k at hk
  rw [hk]
  unfold tailAnnihilationSymbol
  split <;> simp only [one_smul,zero_smul]

lemma annihilationEscapeHigh_supported (R : ℝ) (f : OneBoson) :
    ∀ᵐ k ∂(volume : Measure GW.Space), ‖k‖ ≤ R → annihilationEscapeHigh R f k = 0 := by
  filter_upwards [annihilationEscapeHigh_ae R f] with k hk hR
  rw [hk,ite_eq_right (not_lt.mpr hR)]

lemma annihilationEscapeLow_norm (R : ℝ) (f : OneBoson) : ‖annihilationEscapeLow R f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [annihilationEscapeLow_ae R f] with k hk
  rw [hk]
  split <;> simp only [le_refl,norm_zero,norm_nonneg]

lemma annihilationEscapeHigh_norm (R : ℝ) (f : OneBoson) : ‖annihilationEscapeHigh R f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [annihilationEscapeHigh_ae R f] with k hk
  rw [hk]
  split <;> simp only [le_refl,norm_zero,norm_nonneg]

lemma annihilationEscape_coefficient_split (R : ℝ) (f : OneBoson) :
    f = annihilationEscapeLow R f + annihilationEscapeHigh R f := by
  apply Lp.ext
  filter_upwards [annihilationEscapeLow_ae R f,annihilationEscapeHigh_ae R f,
    Lp.coeFn_add (annihilationEscapeLow R f) (annihilationEscapeHigh R f)] with k hL hH hA
  rw [hA,Pi.add_apply,hL,hH]
  by_cases hk : ‖k‖ ≤ R
  · rw [ite_eq_left hk,ite_eq_right (not_lt.mpr hk),add_zero]
  · rw [ite_eq_right hk,ite_eq_left (lt_of_not_ge hk),zero_add]

lemma annihilationEscape_fiber_value (f : OneBoson) (u : (physicalNumberPower (1/2)).domain) :
    generalizedAnnihilation (phaseMultiplicationKernel f) (tailAnnihilationFieldInput f u) =
      GW.Fock.commutatorPhaseAnnihilatorMap f (fiberPhysicalFromUnshifted u) := by
  have hg := fiberGeneralizedAnnihilatorMap_graph (phaseMultiplicationKernel f) (fiberPhysicalFromUnshifted u)
  rw [fiberPhysicalFromUnshifted_inclusion] at hg
  exact (generalizedAnnihilation (phaseMultiplicationKernel f)).mem_graph_snd_inj
    ((generalizedAnnihilation (phaseMultiplicationKernel f)).mem_graph (tailAnnihilationFieldInput f u)) hg rfl

lemma annihilationEscape_field_add (f g : OneBoson) (u : (physicalNumberPower (1/2)).domain) :
    generalizedAnnihilation (phaseMultiplicationKernel (f+g)) (tailAnnihilationFieldInput (f+g) u) =
      generalizedAnnihilation (phaseMultiplicationKernel f) (tailAnnihilationFieldInput f u) +
      generalizedAnnihilation (phaseMultiplicationKernel g) (tailAnnihilationFieldInput g u) :=
  (annihilationEscape_fiber_value (f+g) u).trans
    ((GW.Gross.derivative_annihilator_add f g (fiberPhysicalFromUnshifted u)).trans
      (congrArg₂ (fun x y : Physical => x+y) (annihilationEscape_fiber_value f u).symm
        (annihilationEscape_fiber_value g u).symm))

end GW.Fock

-- Compiled component Estimate02
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Fock

def annihilationEscapeAmplitude (fs : Fin 3 → OneBoson) : ℝ := ‖annihilationEscapeFamily fs‖
def annihilationEscapeVector (fs : Fin 3 → OneBoson) (u : (physicalNumberPower (1/2)).domain) :
    PiLp 2 (fun _ : Fin 3 => Physical) :=
  annihilationEscapeFamily (fun j => generalizedAnnihilation (phaseMultiplicationKernel (fs j))
    (tailAnnihilationFieldInput (fs j) u))

lemma annihilationEscape_family_mul_bound {H : Type*} [NormedAddCommGroup H]
    (v : Fin 3 → H) (fs : Fin 3 → OneBoson) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ j, ‖v j‖ ≤ ‖fs j‖ * C) :
    ‖annihilationEscapeFamily v‖ ≤ annihilationEscapeAmplitude fs * C := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) hC)).mp
  rw [PiLp.norm_sq_eq_of_L2,mul_pow]
  change (∑ j : Fin 3, ‖v j‖^2) ≤ ‖annihilationEscapeFamily fs‖^2*C^2
  rw [PiLp.norm_sq_eq_of_L2,Finset.sum_mul]
  exact Finset.sum_le_sum (fun j _ => by
    change ‖v j‖^2 ≤ ‖fs j‖^2*C^2
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (h j) 2)

lemma annihilationEscape_high_family_amplitude (R : ℝ) (fs : Fin 3 → OneBoson) :
    annihilationEscapeAmplitude (fun j => annihilationEscapeHigh R (fs j)) ≤ annihilationEscapeAmplitude fs := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖annihilationEscapeFamily (fun j => annihilationEscapeHigh R (fs j))‖^2 ≤ ‖annihilationEscapeFamily fs‖^2
  rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (annihilationEscapeHigh_norm R (fs j)) 2)

lemma annihilationEscape_vector_split (R : ℝ) (fs : Fin 3 → OneBoson)
    (u : (physicalNumberPower (1/2)).domain) :
    annihilationEscapeVector fs u =
      annihilationEscapeVector (fun j => annihilationEscapeLow R (fs j)) u +
      annihilationEscapeVector (fun j => annihilationEscapeHigh R (fs j)) u := by
  apply PiLp.ext
  intro j
  have h := congrArg (fun f : OneBoson =>
    generalizedAnnihilation (phaseMultiplicationKernel f) (tailAnnihilationFieldInput f u))
    (annihilationEscape_coefficient_split R (fs j))
  exact h.trans (annihilationEscape_field_add _ _ u)

lemma annihilationEscape_vector_bound (fs : Fin 3 → OneBoson)
    (u : (physicalNumberPower (1/2)).domain) :
    ‖annihilationEscapeVector fs u‖ ≤ annihilationEscapeAmplitude fs * ‖physicalNumberPower (1/2) u‖ :=
  annihilationEscape_family_mul_bound _ fs _ (norm_nonneg _) (fun j => by
    simpa only [tailAnnihilationFieldInput,phaseMultiplicationKernel_norm] using
      generalizedAnnihilation_root_norm (phaseMultiplicationKernel (fs j)) u)

lemma annihilationEscape_outer_vector_bound (R : ℝ) (fs : Fin 3 → OneBoson)
    (u : (physicalNumberPower (1/2)).domain) :
    ‖annihilationEscapeVector (fun j => annihilationEscapeHigh R (fs j)) u‖ ≤
      annihilationEscapeAmplitude fs * ‖highMomentumNumberRoot R (tailAnnihilationRootInput R u)‖ := by
  have h := annihilationEscape_family_mul_bound _ (fun j => annihilationEscapeHigh R (fs j))
    ‖highMomentumNumberRoot R (tailAnnihilationRootInput R u)‖ (norm_nonneg _)
    (fun j => tailAnnihilation_full_bound R (annihilationEscapeHigh R (fs j))
      (annihilationEscapeHigh_supported R (fs j)) u)
  exact h.trans (mul_le_mul_of_nonneg_right (annihilationEscape_high_family_amplitude R fs) (norm_nonneg _))

lemma annihilationEscape_two_scale_bound (R : ℝ) (fs : Fin 3 → OneBoson)
    (u : (physicalNumberPower (1/2)).domain) :
    ‖annihilationEscapeVector fs u‖ ≤
      annihilationEscapeAmplitude (fun j => annihilationEscapeLow R (fs j)) * ‖physicalNumberPower (1/2) u‖ +
      annihilationEscapeAmplitude fs * ‖highMomentumNumberRoot R (tailAnnihilationRootInput R u)‖ := by
  have h := norm_add_le
    (annihilationEscapeVector (fun j => annihilationEscapeLow R (fs j)) u)
    (annihilationEscapeVector (fun j => annihilationEscapeHigh R (fs j)) u)
  exact (congrArg (fun z => ‖z‖) (annihilationEscape_vector_split R fs u)).le.trans
    (h.trans (add_le_add (annihilationEscape_vector_bound _ u) (annihilationEscape_outer_vector_bound R fs u)))

lemma annihilationEscape_normalized_bound (R : ℝ) (fs : Fin 3 → OneBoson)
    (hA : 0 < annihilationEscapeAmplitude fs) (u : (physicalNumberPower (1/2)).domain) :
    ‖annihilationEscapeVector fs u‖ / annihilationEscapeAmplitude fs ≤
      Real.sqrt ((annihilationEscapeAmplitude (fun j => annihilationEscapeLow R (fs j)))^2 /
        (annihilationEscapeAmplitude fs)^2) * ‖physicalNumberPower (1/2) u‖ +
      ‖highMomentumNumberRoot R (tailAnnihilationRootInput R u)‖ := by
  have h := div_le_div_of_nonneg_right (annihilationEscape_two_scale_bound R fs u) hA.le
  have hroot : Real.sqrt ((annihilationEscapeAmplitude (fun j => annihilationEscapeLow R (fs j)))^2 /
      (annihilationEscapeAmplitude fs)^2) =
      annihilationEscapeAmplitude (fun j => annihilationEscapeLow R (fs j)) / annihilationEscapeAmplitude fs := by
    rw [Real.sqrt_div (sq_nonneg _),Real.sqrt_sq_eq_abs,Real.sqrt_sq_eq_abs,
      abs_of_nonneg (show 0 ≤ annihilationEscapeAmplitude (fun j => annihilationEscapeLow R (fs j)) from norm_nonneg _),abs_of_pos hA]
  rw [hroot]
  exact h.trans_eq (by field_simp [ne_of_gt hA])

end GW.Fock

-- Compiled component Limit03
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Fock

def annihilationEscapeLowRatio (fs : ℕ → Fin 3 → OneBoson) (R : ℝ) (n : ℕ) : ℝ :=
  (annihilationEscapeAmplitude (fun j => annihilationEscapeLow R (fs n j)))^2 /
    (annihilationEscapeAmplitude (fs n))^2

def annihilationEscapeQuotient (fs : ℕ → Fin 3 → OneBoson)
    (u : (physicalNumberPower (1/2)).domain) (n : ℕ) : ℝ :=
  ‖annihilationEscapeVector (fs n) u‖ / annihilationEscapeAmplitude (fs n)

lemma annihilationEscapeAmplitude_eq (fs : Fin 3 → OneBoson) :
    annihilationEscapeAmplitude fs = Real.sqrt (∑ j : Fin 3, ‖fs j‖^2) :=
  annihilationEscapeFamily_norm fs

lemma annihilationEscapeLowRatio_eq (fs : ℕ → Fin 3 → OneBoson) (R : ℝ) (n : ℕ) :
    annihilationEscapeLowRatio fs R n =
      (∑ j : Fin 3, ‖annihilationEscapeLow R (fs n j)‖^2) /
        (annihilationEscapeAmplitude (fs n))^2 := by
  change ‖annihilationEscapeFamily (fun j => annihilationEscapeLow R (fs n j))‖^2 / _ = _
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

lemma annihilationEscapeQuotient_eq (fs : ℕ → Fin 3 → OneBoson)
    (u : (physicalNumberPower (1/2)).domain) (n : ℕ) :
    annihilationEscapeQuotient fs u n =
      Real.sqrt (∑ j : Fin 3, ‖generalizedAnnihilation (phaseMultiplicationKernel (fs n j))
        (tailAnnihilationFieldInput (fs n j) u)‖^2) / annihilationEscapeAmplitude (fs n) := by
  change ‖annihilationEscapeFamily _‖ / _ = _
  rw [annihilationEscapeFamily_norm]

lemma annihilationEscape_zero_amplitude (fs : ℕ → Fin 3 → OneBoson)
    (u : (physicalNumberPower (1/2)).domain) (n : ℕ) (h : annihilationEscapeAmplitude (fs n) = 0) :
    annihilationEscapeQuotient fs u n = 0 := by
  unfold annihilationEscapeQuotient
  rw [h,div_zero]

/-- The source escaping-coefficient conclusion for every fixed original number-half vector.
All quotients are total real quotients, hence zero at a zero amplitude. -/
theorem reg_annihilation_escape (fs : ℕ → Fin 3 → OneBoson)
    (hpos : ∀ᶠ n in atTop, 0 < annihilationEscapeAmplitude (fs n))
    (hescape : ∀ R : ℝ, 0 < R → Tendsto (annihilationEscapeLowRatio fs R) atTop (𝓝 0))
    (u : (physicalNumberPower (1/2)).domain) :
    Tendsto (annihilationEscapeQuotient fs u) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro η hη
  have hex : ∃ m : ℕ, ‖highMomentumNumberRoot ((m:ℝ)+1)
      (tailAnnihilationRootInput ((m:ℝ)+1) u)‖ < η/2 := by
    obtain ⟨m,hm⟩ := Metric.tendsto_atTop.mp (tailAnnihilation_full_sequence u) (η/2) (by linarith)
    exact ⟨m,by simpa only [dist_zero_right] using hm m le_rfl⟩
  let m := Nat.find hex
  have hm := Nat.find_spec hex
  let R : ℝ := (m:ℝ)+1
  have hR : 0 < R := by dsimp [R]; positivity
  let N := ‖physicalNumberPower (1/2) u‖
  let δ := η/(2*(N+1))
  have hN : 0 ≤ N := norm_nonneg _
  have hδ : 0 < δ := div_pos hη (mul_pos (by norm_num) (by linarith))
  have hs : Tendsto (fun n => Real.sqrt (annihilationEscapeLowRatio fs R n)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero,Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp (hescape R hR)
  have hd : ∀ᶠ n in atTop, Real.sqrt (annihilationEscapeLowRatio fs R n) < δ :=
    (tendsto_order.mp hs).2 δ hδ
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp (hpos.and hd)
  refine ⟨n₀,fun n hn => ?_⟩
  obtain ⟨hnA,hnδ⟩ := hn₀ n hn
  unfold annihilationEscapeQuotient
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (div_nonneg (norm_nonneg _) hnA.le)]
  have hbound := annihilationEscape_normalized_bound R (fs n) hnA u
  have hinner : Real.sqrt (annihilationEscapeLowRatio fs R n) * N ≤ η/2 := by
    have he : δ * (N+1) = η/2 := by
      dsimp [δ]
      field_simp [ne_of_gt (show 0 < N+1 by linarith)]
      <;> ring
    exact (mul_le_mul_of_nonneg_right hnδ.le hN).trans
      ((mul_le_mul_of_nonneg_left (by linarith : N ≤ N+1) hδ.le).trans_eq he)
  change Real.sqrt ((annihilationEscapeAmplitude (fun j => annihilationEscapeLow R (fs n j)))^2 / (annihilationEscapeAmplitude (fs n))^2) * ‖physicalNumberPower (1/2) u‖ ≤ η/2 at hinner
  change ‖highMomentumNumberRoot R (tailAnnihilationRootInput R u)‖ < η/2 at hm
  exact hbound.trans_lt (by linarith)

end GW.Fock
