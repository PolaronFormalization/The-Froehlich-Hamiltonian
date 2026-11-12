module
public import GW.Regularity.RegTailNumber
public import GW.Analysis.SeriesDomination
public import GW.Analysis.L2Domination
public import GW.Fock.FockGeneralizedBounds
public import GW.Fock.FockFrankSchlein
@[expose] public section

-- Compiled component Limits02
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Fock

lemma tailAnnihilation_count_antitone (n : ℕ) (k : Coordinates n) :
    Antitone (fun R : ℝ => highMomentumCount R n k) := by
  intro R S hRS
  apply Finset.sum_le_sum
  intro j _
  by_cases hS : S < ‖k j‖
  · simp only [ite_eq_left hS,ite_eq_left (lt_of_le_of_lt hRS hS),le_refl]
  · simp only [ite_eq_right hS]
    split <;> norm_num

lemma tailAnnihilation_count_eventually_zero (n : ℕ) (k : Coordinates n) :
    ∀ᶠ R : ℝ in atTop, highMomentumCount R n k = 0 := by
  classical
  refine eventually_atTop.mpr ⟨∑ j : Fin n, ‖k j‖,fun R hR => ?_⟩
  apply Finset.sum_eq_zero
  intro j _
  have hj : ‖k j‖ ≤ ∑ i : Fin n, ‖k i‖ :=
    Finset.single_le_sum (fun i _ => norm_nonneg (k i)) (Finset.mem_univ j)
  exact ite_eq_right (not_lt.mpr (hj.trans hR))

lemma tailAnnihilation_weight_sequence_zero (n : ℕ) (k : Coordinates n) :
    ∀ᶠ m : ℕ in atTop, tailWeight true ((m:ℝ)+1) n k = 0 := by
  have h := (show Tendsto (fun m : ℕ => (m:ℝ)+1) atTop atTop from
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).eventually
        (tailAnnihilation_count_eventually_zero n k)
  filter_upwards [h] with m hm
  simp only [tailWeight,ite_true,hm,Real.sqrt_zero]

lemma tailAnnihilation_ambient_sequence (n : ℕ) (u : AmbientSector n) :
    Tendsto (fun m : ℕ => tailAmbientMultiplier true ((m:ℝ)+1) n u) atTop (𝓝 0) := by
  let z (m : ℕ) := tailAmbientMultiplier true ((m:ℝ)+1) n u
  let C := Real.sqrt n
  let g (k : Coordinates n) := C * ‖u k‖
  have hz (m : ℕ) : z m =ᵐ[sectorMeasure n] fun k =>
      (tailWeight true ((m:ℝ)+1) n k : ℂ) • u k := tailAmbientMultiplier_ae true _ n u
  have hl : ∀ᵐ k ∂sectorMeasure n, Tendsto (fun m : ℕ => z m k) atTop (𝓝 (0:ℂ)) := by
    filter_upwards [ae_all_iff.mpr hz] with k hk
    apply tendsto_const_nhds.congr'
    filter_upwards [tailAnnihilation_weight_sequence_zero n k] with m hm
    rw [hk m,hm,Complex.ofReal_zero,zero_smul]
  have hg : Measurable g := measurable_const.mul (Lp.stronglyMeasurable u).norm.measurable
  have hi : Integrable (fun k => g k ^ 2) (sectorMeasure n) := by
    have h := ((Lp.memLp u).integrable_norm_pow (p := 2) (by norm_num)).const_mul (C^2)
    apply h.congr
    exact Eventually.of_forall (fun k => by change C^2 * ‖u k‖^2 = (C*‖u k‖)^2; ring)
  have hb (m : ℕ) : ∀ᵐ k ∂sectorMeasure n, ‖z m k‖ ≤ g k := by
    filter_upwards [hz m] with k hk
    rw [hk,norm_smul,Complex.norm_real,Real.norm_of_nonneg (tailWeight_nonneg true _ n k)]
    exact mul_le_mul_of_nonneg_right (tailWeight_le true _ n k) (norm_nonneg _)
  obtain ⟨hs,hf,ht⟩ := GW.Analysis.dominated_l2_convergence (𝕜 := ℂ)
    (fun m => Lp.aestronglyMeasurable (z m)) hl hg hi hb
  have he (m : ℕ) : (hs m).toLp (z m) = z m := Lp.ext (hs m).coeFn_toLp
  have he0 : hf.toLp (fun _ => (0:ℂ)) = 0 := by
    apply Lp.ext
    exact hf.coeFn_toLp.trans (Lp.coeFn_zero ℂ 2 (sectorMeasure n)).symm
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [he,he0] using ht

end GW.Fock

-- Compiled component Amplification01
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Fock

lemma tailAnnihilation_amplify_sequence {X E : Type*} [MeasurableSpace X]
    (μ : Measure X) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : ℕ → E →L[ℂ] E) (C : ℝ)
    (hA : ∀ m v, ‖A m v‖ ≤ C * ‖v‖)
    (hlim : ∀ v, Tendsto (fun m => A m v) atTop (𝓝 0)) (u : Lp E 2 μ) :
    Tendsto (fun m => amplify μ (A m) u) atTop (𝓝 0) := by
  let z (m : ℕ) := amplify μ (A m) u
  let g (x : X) := C * ‖u x‖
  have hz (m : ℕ) : z m =ᵐ[μ] fun x => A m (u x) := amplify_ae μ (A m) u
  have hl : ∀ᵐ x ∂μ, Tendsto (fun m : ℕ => z m x) atTop (𝓝 (0:E)) := by
    filter_upwards [ae_all_iff.mpr hz] with x hx
    exact (hlim (u x)).congr' (Eventually.of_forall (fun m => (hx m).symm))
  have hg : Measurable g := measurable_const.mul (Lp.stronglyMeasurable u).norm.measurable
  have hi : Integrable (fun x => g x ^ 2) μ := by
    have h := ((Lp.memLp u).integrable_norm_pow (p := 2) (by norm_num)).const_mul (C^2)
    apply h.congr
    exact Eventually.of_forall (fun x => by change C^2 * ‖u x‖^2 = (C*‖u x‖)^2; ring)
  have hb (m : ℕ) : ∀ᵐ x ∂μ, ‖z m x‖ ≤ g x := by
    filter_upwards [hz m] with x hx
    rw [hx]
    exact hA m (u x)
  obtain ⟨hs,hf,ht⟩ := GW.Analysis.dominated_l2_convergence (𝕜 := ℂ)
    (fun m => Lp.aestronglyMeasurable (z m)) hl hg hi hb
  have he (m : ℕ) : (hs m).toLp (z m) = z m := Lp.ext (hs m).coeFn_toLp
  have he0 : hf.toLp (fun _ => (0:E)) = 0 := by
    apply Lp.ext
    exact hf.coeFn_toLp.trans (Lp.coeFn_zero E 2 μ).symm
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [he,he0] using ht

lemma tailAnnihilation_sector_sequence (n : ℕ) (u : Sector n) :
    Tendsto (fun m : ℕ => tailSectorMultiplier true ((m:ℝ)+1) n u) atTop (𝓝 0) := by
  cases n with
  | zero =>
    simpa only [tailSectorMultiplier,ContinuousLinearMap.zero_apply] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : Sector 0)) atTop (𝓝 0))
  | succ n =>
    apply (sectorInclusion n).isometry.tendsto_nhds_iff.mpr
    simpa only [Function.comp_def,tailSectorMultiplier_value,map_zero] using
      tailAnnihilation_ambient_sequence (n+1) (sectorInclusion n u)

lemma tailAnnihilation_electron_sequence (n : ℕ) (u : ElectronSector n) :
    Tendsto (fun m : ℕ => tailElectronSectorMultiplier true ((m:ℝ)+1) n u) atTop (𝓝 0) :=
  tailAnnihilation_amplify_sequence (volume : Measure GW.Space)
    (fun m => tailSectorMultiplier true ((m:ℝ)+1) n) (tailWeightBound true n)
    (fun m v => tailSectorMultiplier_bound true _ n v) (tailAnnihilation_sector_sequence n) u

end GW.Fock

-- Compiled component FullSequence03
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Fock

def tailAnnihilationRootInput (R : ℝ) (u : (physicalNumberPower (1/2)).domain) :
    (highMomentumNumberRoot R).domain := ⟨u.val,highMomentumNumberRoot_domain R u.property⟩

lemma tailAnnihilation_number_majorant (u : (physicalNumberPower (1/2)).domain) (n : ℕ) :
    tailWeightBound true n * ‖electronBosonUnitary.symm u.val n‖ =
      ‖numberPower ElectronSector (1/2) (physicalRootNumberInput u) n‖ := by
  change Real.sqrt n * ‖electronBosonUnitary.symm u.val n‖ =
    ‖(numberPowerCoefficient (1/2) n : ℂ) • electronBosonUnitary.symm u.val n‖
  rw [rootNumberCoefficient,norm_smul,Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]

lemma tailAnnihilation_full_sequence (u : (physicalNumberPower (1/2)).domain) :
    Tendsto (fun m : ℕ => highMomentumNumberRoot ((m:ℝ)+1)
      (tailAnnihilationRootInput ((m:ℝ)+1) u)) atTop (𝓝 0) := by
  let z (m : ℕ) := electronBosonUnitary.symm
    (highMomentumNumberRoot ((m:ℝ)+1) (tailAnnihilationRootInput ((m:ℝ)+1) u))
  let b (n : ℕ) := ‖numberPower ElectronSector (1/2) (physicalRootNumberInput u) n‖
  have hb : Summable (fun n => b n ^ 2) :=
    (GW.Analysis.memℓp_two_iff_sq _).mp
      (lp.memℓp (numberPower ElectronSector (1/2) (physicalRootNumberInput u)))
  have hz (m n : ℕ) : ‖z m n‖ ≤ b n := by
    change ‖electronBosonUnitary.symm (highMomentumNumberRoot ((m:ℝ)+1)
      (tailAnnihilationRootInput ((m:ℝ)+1) u)) n‖ ≤ _
    rw [tailNumberOperator_action]
    exact (tailElectronSectorMultiplier_bound true ((m:ℝ)+1) n
      (electronBosonUnitary.symm u.val n)).trans_eq (tailAnnihilation_number_majorant u n)
  have hl (n : ℕ) : Tendsto (fun m => z m n) atTop (𝓝 ((0:ElectronBosonSum) n)) := by
    change Tendsto (fun m : ℕ => electronBosonUnitary.symm
      (highMomentumNumberRoot ((m:ℝ)+1) (tailAnnihilationRootInput ((m:ℝ)+1) u)) n)
      atTop (𝓝 ((0:ElectronBosonSum) n))
    simpa only [tailNumberOperator_action,tailAnnihilationRootInput,lp.coeFn_zero,Pi.zero_apply] using
      tailAnnihilation_electron_sequence n (electronBosonUnitary.symm u.val n)
  have h := GW.Analysis.dominated_lp_tendsto (v := (0:ElectronBosonSum)) hb hz hl
  apply electronBosonUnitary.symm.isometry.tendsto_nhds_iff.mpr
  simpa only [Function.comp_def,map_zero] using h

end GW.Fock

-- Compiled component RealLimit02
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Fock

lemma tailAnnihilation_ambient_norm_antitone (n : ℕ) (u : AmbientSector n) :
    Antitone (fun R : ℝ => ‖tailAmbientMultiplier true R n u‖) := by
  intro R S hRS
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [tailAmbientMultiplier_ae true S n u,tailAmbientMultiplier_ae true R n u] with k hS hR
  rw [hS,hR,norm_smul,norm_smul,Complex.norm_real,Complex.norm_real,
    Real.norm_of_nonneg (tailWeight_nonneg true S n k),
    Real.norm_of_nonneg (tailWeight_nonneg true R n k)]
  exact mul_le_mul_of_nonneg_right
    (Real.sqrt_le_sqrt (tailAnnihilation_count_antitone n k hRS)) (norm_nonneg _)

lemma tailAnnihilation_sector_norm_antitone (n : ℕ) (u : Sector n) :
    Antitone (fun R : ℝ => ‖tailSectorMultiplier true R n u‖) := by
  intro R S hRS
  cases n with
  | zero => exact le_rfl
  | succ n =>
    change ‖tailAmbientMultiplier true S (n+1) (sectorInclusion n u)‖ ≤
      ‖tailAmbientMultiplier true R (n+1) (sectorInclusion n u)‖
    exact tailAnnihilation_ambient_norm_antitone (n+1) (sectorInclusion n u) hRS

lemma tailAnnihilation_electron_norm_antitone (n : ℕ) (u : ElectronSector n) :
    Antitone (fun R : ℝ => ‖tailElectronSectorMultiplier true R n u‖) := by
  intro R S hRS
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [amplify_ae volume (tailSectorMultiplier true S n) u,
    amplify_ae volume (tailSectorMultiplier true R n) u] with x hS hR
  change ‖amplify volume (tailSectorMultiplier true S n) u x‖ ≤
    ‖amplify volume (tailSectorMultiplier true R n) u x‖
  rw [hS,hR]
  exact tailAnnihilation_sector_norm_antitone n (u x) hRS

lemma tailAnnihilation_lp_norm_mono {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
    (v w : lp E 2) (h : ∀ n, ‖v n‖ ≤ ‖w n‖) : ‖v‖ ≤ ‖w‖ := by
  apply (sq_le_sq₀ (norm_nonneg v) (norm_nonneg w)).mp
  rw [GW.Analysis.lp_norm_sq,GW.Analysis.lp_norm_sq]
  exact Summable.tsum_le_tsum (fun n => pow_le_pow_left₀ (norm_nonneg _) (h n) 2)
    ((GW.Analysis.memℓp_two_iff_sq _).mp (lp.memℓp v))
    ((GW.Analysis.memℓp_two_iff_sq _).mp (lp.memℓp w))

lemma tailAnnihilation_full_norm_antitone (u : (physicalNumberPower (1/2)).domain) :
    Antitone (fun R : ℝ => ‖highMomentumNumberRoot R (tailAnnihilationRootInput R u)‖) := by
  intro R S hRS
  have h := tailAnnihilation_lp_norm_mono
    (electronBosonUnitary.symm (highMomentumNumberRoot S (tailAnnihilationRootInput S u)))
    (electronBosonUnitary.symm (highMomentumNumberRoot R (tailAnnihilationRootInput R u)))
    (fun n => by
      rw [tailNumberOperator_action,tailNumberOperator_action]
      exact tailAnnihilation_electron_norm_antitone n (electronBosonUnitary.symm u.val n) hRS)
  exact (electronBosonUnitary.symm.norm_map _).symm.le.trans
    (h.trans (electronBosonUnitary.symm.norm_map _).le)

lemma tailAnnihilation_full_tendsto (u : (physicalNumberPower (1/2)).domain) :
    Tendsto (fun R : ℝ => highMomentumNumberRoot R (tailAnnihilationRootInput R u)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨m,hm⟩ := Metric.tendsto_atTop.mp (tailAnnihilation_full_sequence u) ε hε
  refine ⟨(m:ℝ)+1,fun R hR => ?_⟩
  rw [dist_zero_right]
  exact (tailAnnihilation_full_norm_antitone u hR).trans_lt
    (by simpa only [dist_zero_right] using hm m le_rfl)

end GW.Fock

-- Compiled component Projection01
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Fock

section Projection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def tailAnnihilationSymbol (R : ℝ) (k : GW.Space) : ℂ := if R < ‖k‖ then 1 else 0
lemma tailAnnihilationSymbol_measurable (R : ℝ) : Measurable (tailAnnihilationSymbol R) :=
  measurable_const.ite (measurableSet_lt measurable_const measurable_norm) measurable_const
lemma tailAnnihilationSymbol_bound (R : ℝ) (k : GW.Space) : ‖tailAnnihilationSymbol R k‖ ≤ 1 := by
  unfold tailAnnihilationSymbol
  split <;> norm_num

def tailAnnihilationProjection (R : ℝ) : Lp E 2 (volume : Measure GW.Space) →L[ℂ]
    Lp E 2 (volume : Measure GW.Space) :=
  GW.Analysis.boundedMultiplier (tailAnnihilationSymbol R) (tailAnnihilationSymbol_measurable R)
    (Eventually.of_forall (tailAnnihilationSymbol_bound R))
lemma tailAnnihilationProjection_ae (R : ℝ) (u : Lp E 2 (volume : Measure GW.Space)) :
    tailAnnihilationProjection R u =ᵐ[volume] fun k => tailAnnihilationSymbol R k • u k :=
  (GW.Analysis.boundedMultiplier_ae _ _ _ u).symm
lemma tailAnnihilationProjection_pairing (R : ℝ) (u v : Lp E 2 (volume : Measure GW.Space)) :
    ⟪tailAnnihilationProjection R u,v⟫_ℂ = ⟪u,tailAnnihilationProjection R v⟫_ℂ := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [tailAnnihilationProjection_ae R u,tailAnnihilationProjection_ae R v] with k hu hv
  rw [hu,hv]
  unfold tailAnnihilationSymbol
  split <;> simp only [one_smul,zero_smul,inner_zero_left,inner_zero_right]

variable [CompleteSpace E]
lemma tailAnnihilationProjection_adjoint (R : ℝ) :
    (tailAnnihilationProjection (E := E) R).adjoint = tailAnnihilationProjection R := by
  symm
  exact (ContinuousLinearMap.eq_adjoint_iff _ _).mpr (tailAnnihilationProjection_pairing R)

lemma tailAnnihilation_supported_adjoint (R : ℝ) (F : BosonKernel E)
    (hF : (tailAnnihilationProjection R).comp F = F) :
    F.adjoint.comp (tailAnnihilationProjection R) = F.adjoint := by
  have h := congrArg (fun T : E →L[ℂ] Lp E 2 (volume : Measure GW.Space) => T.adjoint) hF
  simpa only [ContinuousLinearMap.adjoint_comp,tailAnnihilationProjection_adjoint] using h

end Projection
end GW.Fock

-- Compiled component SupportedKernel01
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Fock

lemma tailAnnihilation_phaseKernel_supported (R : ℝ) (f : OneBoson)
    (hf : ∀ᵐ k ∂(volume : Measure GW.Space), ‖k‖ ≤ R → f k = 0) :
    (tailAnnihilationProjection R).comp (phaseMultiplicationKernel f) = phaseMultiplicationKernel f := by
  apply ContinuousLinearMap.ext
  intro u
  change tailAnnihilationProjection R (phaseMultiplicationKernel f u) = phaseMultiplicationKernel f u
  rw [frankSchlein_phaseKernel_Bochner]
  apply Lp.ext
  filter_upwards [tailAnnihilationProjection_ae R (frankSchleinPhaseBochner f u),
    frankSchleinPhaseBochner_ae f u,hf] with k hQ hB hF
  rw [hQ]
  by_cases hk : R < ‖k‖
  · simp only [tailAnnihilationSymbol,ite_eq_left hk,one_smul]
  · rw [hB,hF (le_of_not_gt hk)]
    simp only [zero_smul,smul_zero]

lemma tailAnnihilation_phaseKernel_adjoint (R : ℝ) (f : OneBoson)
    (hf : ∀ᵐ k ∂(volume : Measure GW.Space), ‖k‖ ≤ R → f k = 0) :
    (phaseMultiplicationKernel f).adjoint.comp (tailAnnihilationProjection R) =
      (phaseMultiplicationKernel f).adjoint :=
  tailAnnihilation_supported_adjoint R (phaseMultiplicationKernel f)
    (tailAnnihilation_phaseKernel_supported R f hf)

end GW.Fock

-- Compiled component RawBound01
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Fock
section RawBound
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def tailAnnihilationSplitProjection (R : ℝ) (n : ℕ) (u : KernelSector E (n+1)) :
    Lp (Lp E 2 (volume : Measure GW.Space)) 2 (sectorMeasure n) :=
  amplify (sectorMeasure n) (tailAnnihilationProjection R) (kernelSplit n u)

lemma tailAnnihilation_raw_factor (R : ℝ) (F : BosonKernel E)
    (hF : (tailAnnihilationProjection R).comp F = F) (n : ℕ) (u : KernelSector E (n+1)) :
    kernelAnnihilationRaw F n u =
      amplify (sectorMeasure n) F.adjoint (tailAnnihilationSplitProjection R n u) := by
  have h := frankSchlein_amplify_comp (sectorMeasure n) F.adjoint
    (tailAnnihilationProjection R) (kernelSplit n u)
  have he := congrArg (fun T : Lp E 2 (volume : Measure GW.Space) →L[ℂ] E =>
    amplify (sectorMeasure n) T (kernelSplit n u)) (tailAnnihilation_supported_adjoint R F hF)
  exact he.symm.trans h

lemma tailAnnihilation_raw_bound (R : ℝ) (F : BosonKernel E)
    (hF : (tailAnnihilationProjection R).comp F = F) (n : ℕ) (u : KernelSector E (n+1)) :
    ‖kernelAnnihilationRaw F n u‖ ≤ ‖F‖ * ‖tailAnnihilationSplitProjection R n u‖ := by
  rw [tailAnnihilation_raw_factor R F hF]
  have h := ((amplify (sectorMeasure n) F.adjoint).le_opNorm
    (tailAnnihilationSplitProjection R n u)).trans
      (mul_le_mul_of_nonneg_right (amplify_norm_le (sectorMeasure n) F.adjoint) (norm_nonneg _))
  simpa only [ContinuousLinearMap.adjoint.norm_map] using h

lemma tailAnnihilation_fixed_bound (R : ℝ) (F : BosonKernel E)
    (hF : (tailAnnihilationProjection R).comp F = F) (n : ℕ) (u : kernelFixed (E := E) (n+1)) :
    ‖kernelAnnihilation F n u‖ ≤ Real.sqrt (n+1 : ℕ) * ‖F‖ *
      ‖tailAnnihilationSplitProjection R n u.val‖ := by
  change ‖(kernelAnnihilation F n u : KernelSector E n)‖ ≤ _
  rw [kernelAnnihilation_value,norm_smul,Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _),mul_assoc]
  exact mul_le_mul_of_nonneg_left (tailAnnihilation_raw_bound R F hF n u.val) (Real.sqrt_nonneg _)

end RawBound
end GW.Fock

-- Compiled component CoordinateSquares02
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Fock
section CoordinateSquares
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def tailAnnihilationCoordinateProjection (R : ℝ) (n : ℕ) (j : Fin n) :
    KernelSector E n →L[ℂ] KernelSector E n :=
  GW.Analysis.boundedMultiplier (fun k : Coordinates n => tailAnnihilationSymbol R (k j))
    ((tailAnnihilationSymbol_measurable R).comp (measurable_pi_apply j))
    (Eventually.of_forall (fun k => tailAnnihilationSymbol_bound R (k j)))

lemma tailAnnihilationCoordinateProjection_ae (R : ℝ) (n : ℕ) (j : Fin n) (u : KernelSector E n) :
    tailAnnihilationCoordinateProjection R n j u =ᵐ[sectorMeasure n]
      fun k => if R < ‖k j‖ then u k else 0 := by
  have h := (GW.Analysis.boundedMultiplier_ae
    (fun k : Coordinates n => tailAnnihilationSymbol R (k j))
    ((tailAnnihilationSymbol_measurable R).comp (measurable_pi_apply j))
    (Eventually.of_forall (fun k => tailAnnihilationSymbol_bound R (k j))) u).symm
  filter_upwards [h] with k hk
  change tailAnnihilationCoordinateProjection R n j u k = tailAnnihilationSymbol R (k j) • u k at hk
  rw [hk]
  unfold tailAnnihilationSymbol
  split <;> simp only [one_smul,zero_smul]

lemma tailAnnihilationCoordinateProjection_sq_ae (R : ℝ) (n : ℕ) (j : Fin n) (u : KernelSector E n) :
    (fun k => ‖tailAnnihilationCoordinateProjection R n j u k‖^2) =ᵐ[sectorMeasure n]
      fun k => if R < ‖k j‖ then ‖u k‖^2 else 0 := by
  filter_upwards [tailAnnihilationCoordinateProjection_ae R n j u] with k hk
  rw [hk]
  split <;> simp only [norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0)]

lemma tailAnnihilation_coordinate_integrable (R : ℝ) (n : ℕ) (j : Fin n) (u : KernelSector E n) :
    Integrable (fun k => if R < ‖k j‖ then ‖u k‖^2 else 0) (sectorMeasure n) :=
  ((Lp.memLp (tailAnnihilationCoordinateProjection R n j u)).integrable_norm_pow
    (p := 2) (by norm_num)).congr (tailAnnihilationCoordinateProjection_sq_ae R n j u)

lemma tailAnnihilation_coordinate_norm_sq (R : ℝ) (n : ℕ) (j : Fin n) (u : KernelSector E n) :
    ‖tailAnnihilationCoordinateProjection R n j u‖^2 =
      ∫ k : Coordinates n, if R < ‖k j‖ then ‖u k‖^2 else 0 ∂sectorMeasure n := by
  rw [GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
  exact integral_congr_ae (tailAnnihilationCoordinateProjection_sq_ae R n j u)

def tailAnnihilationCountRoot (R : ℝ) (n : ℕ) : KernelSector E n →L[ℂ] KernelSector E n :=
  GW.Analysis.boundedMultiplier (fun k : Coordinates n => (tailWeight true R n k : ℂ))
    (Complex.continuous_ofReal.measurable.comp (tailWeight_measurable true R n))
    (C := tailWeightBound true n)
    (Eventually.of_forall (fun k => by
      rw [Complex.norm_real,Real.norm_of_nonneg (tailWeight_nonneg true R n k)]
      exact tailWeight_le true R n k))

lemma tailAnnihilationCountRoot_ae (R : ℝ) (n : ℕ) (u : KernelSector E n) :
    tailAnnihilationCountRoot R n u =ᵐ[sectorMeasure n] fun k => (tailWeight true R n k : ℂ) • u k :=
  (GW.Analysis.boundedMultiplier_ae _ _ _ u).symm

lemma tailAnnihilation_count_norm_sq (R : ℝ) (n : ℕ) (u : KernelSector E n) :
    ‖tailAnnihilationCountRoot R n u‖^2 =
      ∑ j : Fin n, ‖tailAnnihilationCoordinateProjection R n j u‖^2 := by
  rw [GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
  calc
    _ = ∫ k : Coordinates n, ∑ j : Fin n, if R < ‖k j‖ then ‖u k‖^2 else 0 ∂sectorMeasure n := by
      apply integral_congr_ae
      filter_upwards [tailAnnihilationCountRoot_ae R n u] with k hk
      rw [hk,norm_smul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,tailWeight_root_sq]
      change highMomentumCount R n k * ‖u k‖^2 = _
      unfold highMomentumCount
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      split <;> simp only [one_mul,zero_mul]
    _ = ∑ j : Fin n, ∫ k : Coordinates n, if R < ‖k j‖ then ‖u k‖^2 else 0 ∂sectorMeasure n :=
      integral_finsetSum Finset.univ (fun j _ => tailAnnihilation_coordinate_integrable R n j u)
    _ = _ := Finset.sum_congr rfl (fun j _ => (tailAnnihilation_coordinate_norm_sq R n j u).symm)

end CoordinateSquares
end GW.Fock

-- Compiled component Symmetry01
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Fock
section CoordinateSymmetry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

lemma tailAnnihilation_coordinate_permutation (R : ℝ) (n : ℕ) (j : Fin n)
    (τ : Equiv.Perm (Fin n)) (u : KernelSector E n) :
    kernelPermutation n τ (tailAnnihilationCoordinateProjection R n j u) =
      tailAnnihilationCoordinateProjection R n (τ j) (kernelPermutation n τ u) := by
  apply Lp.ext
  filter_upwards [kernelPermutation_ae n τ (tailAnnihilationCoordinateProjection R n j u),
    (coordinatePermutation_preserving n τ).quasiMeasurePreserving.ae
      (tailAnnihilationCoordinateProjection_ae R n j u),
    tailAnnihilationCoordinateProjection_ae R n (τ j) (kernelPermutation n τ u),
    kernelPermutation_ae n τ u] with k hP hQ hT hU
  rw [hP,hQ,hT,hU]
  simp only [coordinatePermutation_apply]

lemma tailAnnihilation_coordinate_norm_eq (R : ℝ) (n : ℕ)
    (u : kernelFixed (E := E) (n+1)) (j : Fin (n+1)) :
    ‖tailAnnihilationCoordinateProjection R (n+1) j u.val‖ =
      ‖tailAnnihilationCoordinateProjection R (n+1) 0 u.val‖ := by
  have h := congrArg (fun z : KernelSector E (n+1) => ‖z‖)
    (tailAnnihilation_coordinate_permutation R (n+1) 0 (swapZero n j) u.val)
  have hu := (mem_kernelFixed (n+1) u.val).mp u.property (swapZero n j)
  rw [swapZero_zero,hu] at h
  exact h.symm.trans ((kernelPermutation (E := E) (n+1) (swapZero n j)).norm_map _)

lemma tailAnnihilation_count_fixed_norm_sq (R : ℝ) (n : ℕ)
    (u : kernelFixed (E := E) (n+1)) :
    ‖tailAnnihilationCountRoot R (n+1) u.val‖^2 =
      (n+1 : ℕ) * ‖tailAnnihilationCoordinateProjection R (n+1) 0 u.val‖^2 := by
  rw [tailAnnihilation_count_norm_sq]
  simp_rw [tailAnnihilation_coordinate_norm_eq R n u]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

end CoordinateSymmetry
end GW.Fock

-- Compiled component ProductMultiplier01
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Fock
section ProductMultiplier
variable {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (a : Y → ℂ) (ha : Measurable a) {C : ℝ} (hb : ∀ᵐ y ∂ν, ‖a y‖ ≤ C)

def tailAnnihilationProductMultiplier : Lp E 2 (μ.prod ν) →L[ℂ] Lp E 2 (μ.prod ν) :=
  GW.Analysis.boundedMultiplier (fun p : X × Y => a p.2) (ha.comp measurable_snd)
    ((Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae hb)

lemma tailAnnihilation_product_multiplier_tensor (γ : Lp ℂ 2 μ) (v : Lp E 2 ν) :
    productFunction μ ν γ (GW.Analysis.boundedMultiplier a ha hb v) =
      tailAnnihilationProductMultiplier μ ν a ha hb (productFunction μ ν γ v) := by
  apply Lp.ext
  filter_upwards [productFunction_ae μ ν γ (GW.Analysis.boundedMultiplier a ha hb v),
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae
      (GW.Analysis.boundedMultiplier_ae a ha hb v),
    GW.Analysis.boundedMultiplier_ae (fun p : X × Y => a p.2) (ha.comp measurable_snd)
      ((Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae hb) (productFunction μ ν γ v),
    productFunction_ae μ ν γ v] with p hP hA hM hQ
  change a p.2 • productFunction μ ν γ v p =
    tailAnnihilationProductMultiplier μ ν a ha hb (productFunction μ ν γ v) p at hM
  rw [hP,← hM,hQ,← hA]
  exact smul_comm (γ p.1) (a p.2) (v p.2)

lemma tailAnnihilation_product_multiplier (u : Lp (Lp E 2 ν) 2 μ) :
    productUnitary μ ν (amplify μ (GW.Analysis.boundedMultiplier a ha hb) u) =
      tailAnnihilationProductMultiplier μ ν a ha hb (productUnitary μ ν u) := by
  let A := (productUnitary (E := E) μ ν).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (amplify μ (GW.Analysis.boundedMultiplier a ha hb))
  let B := (tailAnnihilationProductMultiplier μ ν a ha hb).comp
    (productUnitary (E := E) μ ν).toContinuousLinearEquiv.toContinuousLinearMap
  change A u = B u
  apply Lp.induction (p := 2) (μ := μ) (by norm_num)
    (fun u => A u = B u) ?_ ?_ (isClosed_eq A.continuous B.continuous) u
  · intro v S hS hSf
    let γ := indicatorConstLp 2 hS hSf.ne (1:ℂ)
    have h := tailAnnihilation_product_multiplier_tensor μ ν a ha hb γ v
    have hA : A (tensorEmbedding μ γ v) = productFunction μ ν γ (GW.Analysis.boundedMultiplier a ha hb v) := by
      change productUnitary μ ν (amplify μ (GW.Analysis.boundedMultiplier a ha hb) (tensorEmbedding μ γ v)) = _
      rw [amplify_tensor,productUnitary_tensor]
    have hB : B (tensorEmbedding μ γ v) = tailAnnihilationProductMultiplier μ ν a ha hb (productFunction μ ν γ v) :=
      congrArg (tailAnnihilationProductMultiplier μ ν a ha hb) (productUnitary_tensor μ ν γ v)
    have he := hA.trans (h.trans hB.symm)
    simpa only [γ,tensorEmbedding_apply,compLp_indicatorConst,
      ContinuousLinearMap.toSpanSingleton_apply,one_smul,Lp.simpleFunc.coe_indicatorConst] using he
  · intro f g hf hg _ h₁ h₂
    exact (A.map_add (hf.toLp f) (hg.toLp g)).trans
      ((congrArg₂ (fun x y => x+y) h₁ h₂).trans (B.map_add (hf.toLp f) (hg.toLp g)).symm)

end ProductMultiplier
end GW.Fock

-- Compiled component SplitProjection02
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Fock
section SplitProjection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def tailAnnihilationSplitProduct (n : ℕ) : KernelSector E (n+1) ≃ₗᵢ[ℂ]
    Lp E 2 ((sectorMeasure n).prod (volume : Measure GW.Space)) :=
  (vectorPullback (splitCoordinates n 0).symm (splitCoordinates_inverse_preserving n 0)).trans
    (swapProduct volume (sectorMeasure n))

lemma tailAnnihilationSplitProduct_ae (n : ℕ) (u : KernelSector E (n+1)) :
    tailAnnihilationSplitProduct n u =ᵐ[(sectorMeasure n).prod (volume : Measure GW.Space)]
      fun p => u ((splitCoordinates n 0).symm (p.2,p.1)) := by
  filter_upwards [swapProduct_ae volume (sectorMeasure n)
      (vectorPullback (splitCoordinates n 0).symm (splitCoordinates_inverse_preserving n 0) u),
    (Measure.measurePreserving_swap (μ := sectorMeasure n) (ν := (volume : Measure GW.Space))).quasiMeasurePreserving.ae
      (vectorPullback_ae (splitCoordinates n 0).symm (splitCoordinates_inverse_preserving n 0) u)] with p hS hV
  exact hS.trans hV

lemma tailAnnihilation_split_product_projection (R : ℝ) (n : ℕ) (u : KernelSector E (n+1)) :
    tailAnnihilationSplitProduct n (tailAnnihilationCoordinateProjection R (n+1) 0 u) =
      tailAnnihilationProductMultiplier (sectorMeasure n) (volume : Measure GW.Space)
        (tailAnnihilationSymbol R) (tailAnnihilationSymbol_measurable R)
        (Eventually.of_forall (tailAnnihilationSymbol_bound R)) (tailAnnihilationSplitProduct n u) := by
  have hp := (splitCoordinates_inverse_preserving n 0).comp
    (Measure.measurePreserving_swap (μ := sectorMeasure n) (ν := (volume : Measure GW.Space)))
  apply Lp.ext
  filter_upwards [tailAnnihilationSplitProduct_ae n (tailAnnihilationCoordinateProjection R (n+1) 0 u),
    hp.quasiMeasurePreserving.ae (tailAnnihilationCoordinateProjection_ae R (n+1) 0 u),
    GW.Analysis.boundedMultiplier_ae
      (fun p : Coordinates n × GW.Space => tailAnnihilationSymbol R p.2)
      ((tailAnnihilationSymbol_measurable R).comp measurable_snd)
      ((Measure.quasiMeasurePreserving_snd (μ := sectorMeasure n) (ν := (volume : Measure GW.Space))).ae
        (Eventually.of_forall (tailAnnihilationSymbol_bound R))) (tailAnnihilationSplitProduct n u),
    tailAnnihilationSplitProduct_ae n u] with p hT hQ hM hU
  change tailAnnihilationCoordinateProjection R (n+1) 0 u ((splitCoordinates n 0).symm (p.2,p.1)) =
    (if R < ‖(splitCoordinates n 0).symm (p.2,p.1) 0‖ then u ((splitCoordinates n 0).symm (p.2,p.1)) else 0) at hQ
  change tailAnnihilationSymbol R p.2 • tailAnnihilationSplitProduct n u p =
    tailAnnihilationProductMultiplier (sectorMeasure n) (volume : Measure GW.Space)
      (tailAnnihilationSymbol R) (tailAnnihilationSymbol_measurable R)
      (Eventually.of_forall (tailAnnihilationSymbol_bound R)) (tailAnnihilationSplitProduct n u) p at hM
  rw [hT,hQ,← hM,hU,insertCoordinate_same]
  unfold tailAnnihilationSymbol
  split <;> simp only [one_smul,zero_smul]

lemma tailAnnihilation_split_projection (R : ℝ) (n : ℕ) (u : KernelSector E (n+1)) :
    kernelSplit n (tailAnnihilationCoordinateProjection R (n+1) 0 u) =
      tailAnnihilationSplitProjection R n u := by
  let P := productUnitary (E := E) (sectorMeasure n) (volume : Measure GW.Space)
  let T := tailAnnihilationSplitProduct (E := E) n
  let M := tailAnnihilationProductMultiplier (E := E) (sectorMeasure n) (volume : Measure GW.Space)
    (tailAnnihilationSymbol R) (tailAnnihilationSymbol_measurable R)
    (Eventually.of_forall (tailAnnihilationSymbol_bound R))
  apply P.injective
  have h₁ : P (kernelSplit n (tailAnnihilationCoordinateProjection R (n+1) 0 u)) =
      T (tailAnnihilationCoordinateProjection R (n+1) 0 u) := P.apply_symm_apply _
  have h₂ := tailAnnihilation_product_multiplier (E := E) (sectorMeasure n) (volume : Measure GW.Space)
    (tailAnnihilationSymbol R) (tailAnnihilationSymbol_measurable R)
    (Eventually.of_forall (tailAnnihilationSymbol_bound R)) (kernelSplit n u)
  have h₃ : P (kernelSplit n u) = T u := P.apply_symm_apply _
  have h₄ := tailAnnihilation_split_product_projection R n u
  exact h₁.trans (h₄.trans ((congrArg M h₃).symm.trans h₂.symm))

lemma tailAnnihilation_split_projection_norm (R : ℝ) (n : ℕ) (u : KernelSector E (n+1)) :
    ‖tailAnnihilationSplitProjection R n u‖ =
      ‖tailAnnihilationCoordinateProjection R (n+1) 0 u‖ :=
  (congrArg (fun z => ‖z‖) (tailAnnihilation_split_projection R n u)).symm.trans
    ((kernelSplit (E := E) n).norm_map _)

end SplitProjection
end GW.Fock

-- Compiled component SharpKernel01
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Fock
section SharpKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

lemma tailAnnihilation_count_fixed_norm (R : ℝ) (n : ℕ)
    (u : kernelFixed (E := E) (n+1)) :
    Real.sqrt (n+1 : ℕ) * ‖tailAnnihilationSplitProjection R n u.val‖ =
      ‖tailAnnihilationCountRoot R (n+1) u.val‖ := by
  apply (sq_eq_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) (norm_nonneg _)).mp
  rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _),tailAnnihilation_split_projection_norm]
  exact (tailAnnihilation_count_fixed_norm_sq R n u).symm

lemma tailAnnihilation_sharp_kernel_bound (R : ℝ) (F : BosonKernel E)
    (hF : (tailAnnihilationProjection R).comp F = F) (n : ℕ) (u : kernelFixed (E := E) (n+1)) :
    ‖kernelAnnihilation F n u‖ ≤ ‖F‖ * ‖tailAnnihilationCountRoot R (n+1) u.val‖ := by
  calc
    _ ≤ Real.sqrt (n+1 : ℕ) * ‖F‖ * ‖tailAnnihilationSplitProjection R n u.val‖ :=
      tailAnnihilation_fixed_bound R F hF n u
    _ = ‖F‖ * (Real.sqrt (n+1 : ℕ) * ‖tailAnnihilationSplitProjection R n u.val‖) := by ring
    _ = _ := congrArg (‖F‖ * ·) (tailAnnihilation_count_fixed_norm R n u)

end SharpKernel

lemma tailAnnihilation_sharp_phase_kernel_bound (R : ℝ) (f : OneBoson)
    (hf : ∀ᵐ k ∂(volume : Measure GW.Space), ‖k‖ ≤ R → f k = 0)
    (n : ℕ) (u : kernelFixed (E := ElectronL2) (n+1)) :
    ‖kernelAnnihilation (phaseMultiplicationKernel f) n u‖ ≤
      ‖f‖ * ‖tailAnnihilationCountRoot R (n+1) u.val‖ := by
  simpa only [phaseMultiplicationKernel_norm] using
    tailAnnihilation_sharp_kernel_bound R (phaseMultiplicationKernel f)
      (tailAnnihilation_phaseKernel_supported R f hf) n u

end GW.Fock

-- Compiled component PhysicalTransport01
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Fock

lemma tailAnnihilation_count_tensor (R : ℝ) (n : ℕ) (v : AmbientSector n) (γ : ElectronL2) :
    tailAnnihilationCountRoot R n (tensorEmbedding (sectorMeasure n) v γ) =
      tensorEmbedding (sectorMeasure n) (tailAmbientMultiplier true R n v) γ := by
  apply Lp.ext
  filter_upwards [tailAnnihilationCountRoot_ae R n (tensorEmbedding (sectorMeasure n) v γ),
    tensorEmbedding_ae (sectorMeasure n) v γ,
    tensorEmbedding_ae (sectorMeasure n) (tailAmbientMultiplier true R n v) γ,
    tailAmbientMultiplier_ae true R n v] with k hC hV hT hM
  rw [hC,hV,hT,hM,smul_smul]
  rfl

lemma tailAnnihilation_ordinary_positive (R : ℝ) (n : ℕ) (v : Sector (n+1)) :
    (ordinarySectorKernel (n+1) (tailSectorMultiplier true R (n+1) v) : KernelSector ℂ (n+1)) =
      tailAmbientMultiplier true R (n+1) (ordinarySectorKernel (n+1) v : KernelSector ℂ (n+1)) := rfl

lemma tailAnnihilation_physical_tensor (R : ℝ) (n : ℕ) (γ : ElectronL2) (v : Sector (n+1)) :
    (physicalSectorKernel (n+1) (tailElectronSectorMultiplier true R (n+1)
      (tensorEmbedding volume γ v)) : KernelSector ElectronL2 (n+1)) =
    tailAnnihilationCountRoot R (n+1)
      (physicalSectorKernel (n+1) (tensorEmbedding volume γ v) : KernelSector ElectronL2 (n+1)) := by
  have h₁ := congrArg (fun z : ElectronSector (n+1) =>
    (physicalSectorKernel (n+1) z : KernelSector ElectronL2 (n+1)))
    (amplify_tensor (volume : Measure GW.Space) (tailSectorMultiplier true R (n+1)) γ v)
  have h₂ := fiberPhysicalSectorKernel_tensor (n+1) γ (tailSectorMultiplier true R (n+1) v)
  have h₃ := congrArg (fun b : AmbientSector (n+1) => tensorEmbedding (sectorMeasure (n+1)) b γ)
    (tailAnnihilation_ordinary_positive R n v)
  have h₄ := (tailAnnihilation_count_tensor R (n+1)
    (ordinarySectorKernel (n+1) v : KernelSector ℂ (n+1)) γ).symm
  have h₅ := congrArg (tailAnnihilationCountRoot (E := ElectronL2) R (n+1))
    (fiberPhysicalSectorKernel_tensor (n+1) γ v).symm
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

lemma tailAnnihilation_fixedInclusion_value {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (n : ℕ) (u : kernelFixed (E := E) n) :
    (kernelFixedInclusion (E := E) n).toContinuousLinearMap u = (u : KernelSector E n) := rfl

lemma tailAnnihilation_physical_transport (R : ℝ) (n : ℕ) (u : ElectronSector (n+1)) :
    (physicalSectorKernel (n+1) (tailElectronSectorMultiplier true R (n+1) u) : KernelSector ElectronL2 (n+1)) =
      tailAnnihilationCountRoot R (n+1) (physicalSectorKernel (n+1) u : KernelSector ElectronL2 (n+1)) := by
  let I := (kernelFixedInclusion (E := ElectronL2) (n+1)).toContinuousLinearMap
  let P := (physicalSectorKernel (n+1)).toContinuousLinearEquiv.toContinuousLinearMap
  let A := (I.comp P).comp (tailElectronSectorMultiplier true R (n+1))
  let B := (tailAnnihilationCountRoot (E := ElectronL2) R (n+1)).comp (I.comp P)
  change A u = B u
  apply Lp.induction (p := 2) (μ := (volume : Measure GW.Space)) (by norm_num)
    (fun u => A u = B u) ?_ ?_ (isClosed_eq A.continuous B.continuous) u
  · intro v S hS hSf
    have h := tailAnnihilation_physical_tensor R n (indicatorConstLp 2 hS hSf.ne (1:ℂ)) v
    simpa only [A,B,I,P,ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe,tailAnnihilation_fixedInclusion_value,tensorEmbedding_apply,
      compLp_indicatorConst,ContinuousLinearMap.toSpanSingleton_apply,one_smul,
      Lp.simpleFunc.coe_indicatorConst] using h
  · intro f g hf hg _ h₁ h₂
    exact (A.map_add (hf.toLp f) (hg.toLp g)).trans
      ((congrArg₂ (fun x y => x+y) h₁ h₂).trans (B.map_add (hf.toLp f) (hg.toLp g)).symm)

end GW.Fock

-- Compiled component FullBound01
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Fock

lemma tailAnnihilation_sharp_sector_bound (R : ℝ) (f : OneBoson)
    (hf : ∀ᵐ k ∂(volume : Measure GW.Space), ‖k‖ ≤ R → f k = 0)
    (n : ℕ) (u : ElectronSector (n+1)) :
    ‖generalizedAnnihilationSector (phaseMultiplicationKernel f) n u‖ ≤
      ‖f‖ * ‖tailElectronSectorMultiplier true R (n+1) u‖ := by
  have h₁ : ‖generalizedAnnihilationSector (phaseMultiplicationKernel f) n u‖ =
      ‖kernelAnnihilation (phaseMultiplicationKernel f) n (physicalSectorKernel (n+1) u)‖ :=
    (physicalSectorKernel n).symm.norm_map _
  have h₂ := tailAnnihilation_sharp_phase_kernel_bound R f hf n (physicalSectorKernel (n+1) u)
  have h₃ := congrArg (fun z : KernelSector ElectronL2 (n+1) => ‖z‖)
    (tailAnnihilation_physical_transport R n u).symm
  have h₄ := (physicalSectorKernel (n+1)).norm_map (tailElectronSectorMultiplier true R (n+1) u)
  exact h₁.le.trans (h₂.trans_eq (congrArg (‖f‖ * ·) (h₃.trans h₄)))

lemma tailAnnihilation_shift_norm {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
    (v w : lp E 2) (C : ℝ) (hC : 0 ≤ C) (hw0 : w 0 = 0)
    (h : ∀ n, ‖v n‖ ≤ C * ‖w (n+1)‖) : ‖v‖ ≤ C * ‖w‖ := by
  apply (sq_le_sq₀ (norm_nonneg v) (mul_nonneg hC (norm_nonneg w))).mp
  have hv : Summable (fun n => ‖v n‖^2) := (GW.Analysis.memℓp_two_iff_sq _).mp v.property
  have hw : Summable (fun n => ‖w n‖^2) := (GW.Analysis.memℓp_two_iff_sq _).mp w.property
  have hw' : Summable (fun n => ‖w (n+1)‖^2) := (summable_nat_add_iff 1).mpr hw
  rw [GW.Analysis.lp_norm_sq,mul_pow,GW.Analysis.lp_norm_sq,hw.tsum_eq_zero_add,
    hw0,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),zero_add,← tsum_mul_left]
  apply Summable.tsum_le_tsum _ hv (hw'.mul_left _)
  intro n
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (h n) 2

def tailAnnihilationFieldInput (f : OneBoson) (u : (physicalNumberPower (1/2)).domain) :
    (generalizedAnnihilation (phaseMultiplicationKernel f)).domain :=
  ⟨u.val,generalizedAnnihilation_mem_root (phaseMultiplicationKernel f) u⟩

lemma tailAnnihilation_full_bound (R : ℝ) (f : OneBoson)
    (hf : ∀ᵐ k ∂(volume : Measure GW.Space), ‖k‖ ≤ R → f k = 0)
    (u : (physicalNumberPower (1/2)).domain) :
    ‖generalizedAnnihilation (phaseMultiplicationKernel f) (tailAnnihilationFieldInput f u)‖ ≤
      ‖f‖ * ‖highMomentumNumberRoot R (tailAnnihilationRootInput R u)‖ := by
  let v := electronBosonUnitary.symm
    (generalizedAnnihilation (phaseMultiplicationKernel f) (tailAnnihilationFieldInput f u))
  let w := electronBosonUnitary.symm (highMomentumNumberRoot R (tailAnnihilationRootInput R u))
  have hw0 : w 0 = 0 := tailNumberOperator_action_vacuum true R (tailAnnihilationRootInput R u)
  have h (n : ℕ) : ‖v n‖ ≤ ‖f‖ * ‖w (n+1)‖ := by
    change ‖electronBosonUnitary.symm
      (generalizedAnnihilation (phaseMultiplicationKernel f) (tailAnnihilationFieldInput f u)) n‖ ≤
      ‖f‖ * ‖electronBosonUnitary.symm (highMomentumNumberRoot R (tailAnnihilationRootInput R u)) (n+1)‖
    rw [generalizedAnnihilation_apply,tailNumberOperator_action]
    exact tailAnnihilation_sharp_sector_bound R f hf n (electronBosonUnitary.symm u.val (n+1))
  have ht := tailAnnihilation_shift_norm v w ‖f‖ (norm_nonneg f) hw0 h
  exact (electronBosonUnitary.symm.norm_map _).symm.le.trans
    (ht.trans_eq (congrArg (‖f‖ * ·) (electronBosonUnitary.symm.norm_map _)))

/-- The source high-momentum annihilation estimate and full real-radius tail limit,
on the original number-half domain and with the original field and count operators. -/
theorem reg_tail_annihilation (R : ℝ) (_hR : 0 < R) (f : OneBoson)
    (hf : ∀ᵐ k ∂(volume : Measure GW.Space), ‖k‖ ≤ R → f k = 0)
    (u : (physicalNumberPower (1/2)).domain) :
    ‖generalizedAnnihilation (phaseMultiplicationKernel f) (tailAnnihilationFieldInput f u)‖ ≤
      ‖f‖ * ‖highMomentumNumberRoot R (tailAnnihilationRootInput R u)‖ ∧
    Tendsto (fun S : ℝ => ‖highMomentumNumberRoot S (tailAnnihilationRootInput S u)‖)
      atTop (𝓝 0) :=
  ⟨tailAnnihilation_full_bound R f hf u,by simpa only [norm_zero] using (tailAnnihilation_full_tendsto u).norm⟩

end GW.Fock
