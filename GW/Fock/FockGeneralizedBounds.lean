module
public import GW.Fock.FockGeneralized
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ENNReal
namespace GW.Fock
section NumberBounds

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {G : ℕ → Type*} [∀ n, NormedAddCommGroup (G n)] [∀ n, InnerProductSpace ℂ (G n)]
  (R : ∀ n, G n ≃ₗᵢ[ℂ] kernelFixed (E := E) n) (F : BosonKernel E)

lemma rootNumberCoefficient (n : ℕ) : numberPowerCoefficient (1/2) n = Real.sqrt n := by
  simp [numberPowerCoefficient,Real.sqrt_eq_rpow]

lemma sectorCreation_rootBound (u : (shiftedNumberPower G (1/2)).domain) (n : ℕ) :
    ‖sectorCreation R F n ((u : lp G 2) n)‖ ≤ ‖F‖ * ‖shiftedNumberPower G (1/2) u n‖ := by
  calc
    _ ≤ (Real.sqrt (n+1 : ℕ) * ‖F‖) * ‖(u : lp G 2) n‖ :=
      ((sectorCreation R F n).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (sectorCreation_norm R F n) (norm_nonneg _))
    _ = _ := by
      rw [shiftedNumberPower_apply,norm_smul,Complex.norm_real,← Real.sqrt_eq_rpow,
        Real.norm_of_nonneg (Real.sqrt_nonneg _),Nat.cast_add,Nat.cast_one]
      ring

lemma sectorAnnihilation_rootBound (u : (numberPower G (1/2)).domain) (n : ℕ) :
    ‖sectorAnnihilation R F n ((u : lp G 2) (n+1))‖ ≤ ‖F‖ * ‖numberPower G (1/2) u (n+1)‖ := by
  calc
    _ ≤ (Real.sqrt (n+1 : ℕ) * ‖F‖) * ‖(u : lp G 2) (n+1)‖ :=
      ((sectorAnnihilation R F n).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (sectorAnnihilation_norm R F n) (norm_nonneg _))
    _ = _ := by
      change _ = ‖F‖ * ‖(numberPowerCoefficient (1/2) (n+1) : ℂ) • (u : lp G 2) (n+1)‖
      rw [rootNumberCoefficient,norm_smul,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      ring

lemma creation_mem_shiftedRoot (u : (shiftedNumberPower G (1/2)).domain) :
    (u : lp G 2) ∈ (maximalSectorCreation (sectorCreation R F)).domain := by
  let w := shiftedNumberPower G (1/2) u
  have hs : Summable (fun n => ‖w n‖^2) := (GW.Analysis.memℓp_two_iff_sq _).mp w.property
  apply (maximalSectorCreation_domain _ _).mpr
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ (hs.mul_left (‖F‖^2))
  intro n
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (sectorCreation_rootBound R F u n) 2

lemma annihilation_mem_root (u : (numberPower G (1/2)).domain) :
    (u : lp G 2) ∈ (maximalSectorAnnihilation (sectorAnnihilation R F)).domain := by
  let w := numberPower G (1/2) u
  have hs : Summable (fun n => ‖w n‖^2) := (GW.Analysis.memℓp_two_iff_sq _).mp w.property
  have hs' : Summable (fun n => ‖w (n+1)‖^2) := (summable_nat_add_iff 1).mpr hs
  apply (maximalSectorAnnihilation_domain _ _).mpr
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ (hs'.mul_left (‖F‖^2))
  intro n
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (sectorAnnihilation_rootBound R F u n) 2

lemma creation_root_norm (u : (shiftedNumberPower G (1/2)).domain) :
    ‖maximalSectorCreation (sectorCreation R F) ⟨u,creation_mem_shiftedRoot R F u⟩‖ ≤
      ‖F‖ * ‖shiftedNumberPower G (1/2) u‖ := by
  let v := maximalSectorCreation (sectorCreation R F) ⟨u,creation_mem_shiftedRoot R F u⟩
  let w := shiftedNumberPower G (1/2) u
  change ‖v‖ ≤ ‖F‖ * ‖w‖
  apply (sq_le_sq₀ (norm_nonneg v) (mul_nonneg F.opNorm_nonneg (norm_nonneg w))).mp
  have hv : Summable (fun n => ‖v n‖^2) := (GW.Analysis.memℓp_two_iff_sq _).mp v.property
  have hv' : Summable (fun n => ‖v (n+1)‖^2) := (summable_nat_add_iff 1).mpr hv
  have hw : Summable (fun n => ‖w n‖^2) := (GW.Analysis.memℓp_two_iff_sq _).mp w.property
  rw [GW.Analysis.lp_norm_sq,mul_pow,GW.Analysis.lp_norm_sq,hv.tsum_eq_zero_add,
    show v 0 = 0 from maximalSectorCreation_zero _ _,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),
    zero_add,← tsum_mul_left]
  apply Summable.tsum_le_tsum _ hv' (hw.mul_left _)
  intro n
  rw [← mul_pow]
  have he : v (n+1) = sectorCreation R F n ((u : lp G 2) n) := maximalSectorCreation_succ _ _ n
  rw [he]
  exact pow_le_pow_left₀ (norm_nonneg _) (sectorCreation_rootBound R F u n) 2

lemma annihilation_root_norm (u : (numberPower G (1/2)).domain) :
    ‖maximalSectorAnnihilation (sectorAnnihilation R F) ⟨u,annihilation_mem_root R F u⟩‖ ≤
      ‖F‖ * ‖numberPower G (1/2) u‖ := by
  let v := maximalSectorAnnihilation (sectorAnnihilation R F) ⟨u,annihilation_mem_root R F u⟩
  let w := numberPower G (1/2) u
  change ‖v‖ ≤ ‖F‖ * ‖w‖
  apply (sq_le_sq₀ (norm_nonneg v) (mul_nonneg F.opNorm_nonneg (norm_nonneg w))).mp
  have hv : Summable (fun n => ‖v n‖^2) := (GW.Analysis.memℓp_two_iff_sq _).mp v.property
  have hw : Summable (fun n => ‖w n‖^2) := (GW.Analysis.memℓp_two_iff_sq _).mp w.property
  have hw' : Summable (fun n => ‖w (n+1)‖^2) := (summable_nat_add_iff 1).mpr hw
  have hw₀ : w 0 = 0 := by
    change (numberPowerCoefficient (1/2) 0 : ℂ) • (u : lp G 2) 0 = 0
    rw [rootNumberCoefficient,Nat.cast_zero,Real.sqrt_zero,Complex.ofReal_zero,zero_smul]
  rw [GW.Analysis.lp_norm_sq,mul_pow,GW.Analysis.lp_norm_sq,hw.tsum_eq_zero_add,
    hw₀,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),zero_add,← tsum_mul_left]
  apply Summable.tsum_le_tsum _ hv (hw'.mul_left _)
  intro n
  rw [← mul_pow]
  have he : v n = sectorAnnihilation R F n ((u : lp G 2) (n+1)) := maximalSectorAnnihilation_apply _ _ n
  rw [he]
  exact pow_le_pow_left₀ (norm_nonneg _) (sectorAnnihilation_rootBound R F u n) 2

end NumberBounds
section PhysicalNumberBounds

def physicalRootNumberInput (u : (physicalNumberPower (1/2)).domain) :
    (numberPower ElectronSector (1/2)).domain :=
  ⟨electronBosonUnitary.symm (u : Physical),u.property⟩

def physicalShiftedRootNumberInput (u : (physicalNumberPower (1/2)).domain) :
    (physicalShiftedNumberPower (1/2)).domain :=
  ⟨u,(shiftedNumberInput ElectronSector (1/2) (by norm_num) (physicalRootNumberInput u)).property⟩

lemma generalizedCreation_mem_root (F : BosonKernel ElectronL2) (u : (physicalNumberPower (1/2)).domain) :
    (u : Physical) ∈ (generalizedCreation F).domain :=
  creation_mem_shiftedRoot physicalSectorKernel F
    (shiftedNumberInput ElectronSector (1/2) (by norm_num) (physicalRootNumberInput u))

lemma generalizedAnnihilation_mem_root (F : BosonKernel ElectronL2) (u : (physicalNumberPower (1/2)).domain) :
    (u : Physical) ∈ (generalizedAnnihilation F).domain :=
  annihilation_mem_root physicalSectorKernel F (physicalRootNumberInput u)

lemma transportedAction_norm {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] (U : H ≃ₗᵢ[ℂ] K) (T : K →ₗ.[ℂ] K)
    (u : (representationTransport U T).domain) (w : T.domain) (hw : U (u : H) = (w : K)) :
    ‖representationTransport U T u‖ = ‖T w‖ := by
  rw [representationTransport_apply,LinearIsometryEquiv.norm_map]
  exact congrArg (fun z : T.domain => ‖T z‖) (Subtype.ext hw)

lemma bochnerDiagonal_norm_eq (a : ℕ → ℝ) (u : (bochnerDiagonal (volume : Measure GW.Space) Sector a).domain)
    (w : (scalarDiagonal ElectronSector a).domain) (hw : electronBosonUnitary.symm (u : Physical) = (w : ElectronBosonSum)) :
    ‖bochnerDiagonal (volume : Measure GW.Space) Sector a u‖ = ‖scalarDiagonal ElectronSector a w‖ := by
  let v := bochnerDiagonalInput (volume : Measure GW.Space) Sector a u
  have he : v = w := Subtype.ext hw
  calc
    _ = ‖scalarDiagonal ElectronSector a v‖ := electronBosonUnitary.norm_map _
    _ = _ := congrArg (fun z : (scalarDiagonal ElectronSector a).domain =>
      ‖scalarDiagonal ElectronSector a z‖) he

lemma sector_norm_from_shifted_bounds {G : ℕ → Type*} [∀ n, NormedAddCommGroup (G n)]
    [∀ n, InnerProductSpace ℂ (G n)] (v w : lp G 2) {C : ℝ} (hC : 0 ≤ C)
    (hv₀ : v 0 = 0) (hb : ∀ n, ‖v (n+1)‖ ≤ C * ‖w n‖) :
    ‖v‖ ≤ C * ‖w‖ := by
  apply (sq_le_sq₀ (norm_nonneg v) (mul_nonneg hC (norm_nonneg w))).mp
  have hv : Summable (fun n => ‖v n‖^2) := (GW.Analysis.memℓp_two_iff_sq _).mp v.property
  have hv' : Summable (fun n => ‖v (n+1)‖^2) := (summable_nat_add_iff 1).mpr hv
  have hw : Summable (fun n => ‖w n‖^2) := (GW.Analysis.memℓp_two_iff_sq _).mp w.property
  rw [GW.Analysis.lp_norm_sq,mul_pow,GW.Analysis.lp_norm_sq,hv.tsum_eq_zero_add,
    hv₀,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),zero_add,← tsum_mul_left]
  apply Summable.tsum_le_tsum _ hv' (hw.mul_left _)
  intro n
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hb n) 2

def generalizedCreationRootInput (F : BosonKernel ElectronL2) (u : (physicalNumberPower (1/2)).domain) :
    (generalizedCreation F).domain := ⟨u,generalizedCreation_mem_root F u⟩

def physicalShiftedRootSectorInput (u : (physicalShiftedNumberPower (1/2)).domain) :
    (shiftedNumberPower ElectronSector (1/2)).domain :=
  ⟨electronBosonUnitary.symm (u : Physical),u.property⟩

def generalizedCreationShiftedInput (F : BosonKernel ElectronL2) (u : (physicalShiftedNumberPower (1/2)).domain) :
    (generalizedCreation F).domain :=
  ⟨u,creation_mem_shiftedRoot physicalSectorKernel F (physicalShiftedRootSectorInput u)⟩

lemma generalizedCreation_shifted_norm (F : BosonKernel ElectronL2)
    (u : (physicalShiftedNumberPower (1/2)).domain) :
    ‖generalizedCreation F (generalizedCreationShiftedInput F u)‖ ≤
      ‖F‖ * ‖physicalShiftedNumberPower (1/2) u‖ := by
  let w := physicalShiftedRootSectorInput u
  let C := sectorCreation physicalSectorKernel F
  let T := maximalSectorCreation C
  let x : (representationTransport electronBosonUnitary.symm T).domain := generalizedCreationShiftedInput F u
  let y : T.domain := ⟨w,creation_mem_shiftedRoot physicalSectorKernel F w⟩
  have h₁ := transportedAction_norm electronBosonUnitary.symm T x y rfl
  have h₂ := bochnerDiagonal_norm_eq (fun n => ((n:ℝ)+1)^(1/2:ℝ)) u w rfl
  exact h₁.le.trans ((creation_root_norm physicalSectorKernel F w).trans
    (congrArg (‖F‖ * ·) h₂.symm).le)

lemma physicalRootNumber_domains_eq :
    (physicalNumberPower (1/2)).domain = (physicalShiftedNumberPower (1/2)).domain := by
  rw [physicalNumberPower_domain_map,physicalShiftedNumberPower_domain_map]
  exact congrArg (fun V : Submodule ℂ ElectronBosonSum => V.map electronBosonUnitary.toLinearMap)
    (numberPower_domain_eq ElectronSector (1/2) (by norm_num))

lemma generalizedCreationShiftedInput_val (F : BosonKernel ElectronL2)
    (u : (physicalShiftedNumberPower (1/2)).domain) :
    (generalizedCreationShiftedInput F u).val = u.val := rfl

lemma generalizedAnnihilation_root_norm (F : BosonKernel ElectronL2) (u : (physicalNumberPower (1/2)).domain) :
    ‖generalizedAnnihilation F ⟨u,generalizedAnnihilation_mem_root F u⟩‖ ≤
      ‖F‖ * ‖physicalNumberPower (1/2) u‖ := by
  let w := physicalRootNumberInput u
  let A := sectorAnnihilation physicalSectorKernel F
  let T := maximalSectorAnnihilation A
  let x : (representationTransport electronBosonUnitary.symm T).domain :=
    ⟨u,generalizedAnnihilation_mem_root F u⟩
  let y : T.domain := ⟨w,annihilation_mem_root physicalSectorKernel F w⟩
  have h₁ := transportedAction_norm electronBosonUnitary.symm T x y rfl
  have h₂ := bochnerDiagonal_norm_eq (numberPowerCoefficient (1/2)) u w rfl
  exact h₁.le.trans ((annihilation_root_norm physicalSectorKernel F w).trans
    (congrArg (‖F‖ * ·) h₂.symm).le)

end PhysicalNumberBounds
section MultiplicationKernels

abbrev ElectronBosonProduct := Lp ℂ 2 ((volume : Measure GW.Space).prod (volume : Measure GW.Space))

def kernelSectionSq (b : GW.Space × GW.Space → ℂ) (x : GW.Space) : ℝ≥0∞ :=
  ∫⁻ k, ENNReal.ofReal (‖b (x,k)‖^2) ∂(volume : Measure GW.Space)

def kernelRep (b : GW.Space × GW.Space → ℂ) (u : ElectronL2) (p : GW.Space × GW.Space) : ℂ :=
  b p * u p.1

lemma kernelRep_measurable (b : GW.Space × GW.Space → ℂ) (hb : Measurable b) (u : ElectronL2) :
    Measurable (kernelRep b u) :=
  hb.mul ((Lp.stronglyMeasurable u).measurable.comp measurable_fst)

lemma kernelRep_lintegral (b : GW.Space × GW.Space → ℂ) (hb : Measurable b) (u : ElectronL2) :
    (∫⁻ p, ENNReal.ofReal (‖kernelRep b u p‖^2) ∂((volume : Measure GW.Space).prod (volume : Measure GW.Space))) =
      ∫⁻ x, ENNReal.ofReal (‖u x‖^2) * kernelSectionSq b x ∂(volume : Measure GW.Space) := by
  rw [lintegral_prod _ ((kernelRep_measurable b hb u).norm.pow_const 2).ennreal_ofReal.aemeasurable]
  apply lintegral_congr
  intro x
  change (∫⁻ k, ENNReal.ofReal (‖b (x,k) * u x‖^2) ∂(volume : Measure GW.Space)) = _
  have h (k : GW.Space) : ENNReal.ofReal (‖b (x,k)*u x‖^2) =
      ENNReal.ofReal (‖u x‖^2) * ENNReal.ofReal (‖b (x,k)‖^2) := by
    rw [norm_mul,mul_pow,mul_comm,ENNReal.ofReal_mul (sq_nonneg _)]
  simp_rw [h]
  have hm : Measurable (fun k : GW.Space => ENNReal.ofReal (‖b (x,k)‖^2)) :=
    ((hb.comp (measurable_const.prodMk measurable_id)).norm.pow_const 2).ennreal_ofReal
  exact lintegral_const_mul (ENNReal.ofReal (‖u x‖^2)) hm

lemma electron_norm_sq_lintegral (u : ElectronL2) :
    ENNReal.ofReal (‖u‖^2) = ∫⁻ x, ENNReal.ofReal (‖u x‖^2) ∂(volume : Measure GW.Space) := by
  rw [GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
  exact ofReal_integral_eq_lintegral_ofReal ((Lp.memLp u).integrable_norm_pow (p := 2) (by norm_num))
    (Eventually.of_forall (fun _ => sq_nonneg _))

lemma kernelRep_lintegral_le (b : GW.Space × GW.Space → ℂ) (hb : Measurable b)
    {C : ℝ} (hC : ∀ᵐ x ∂(volume : Measure GW.Space), kernelSectionSq b x ≤ ENNReal.ofReal (C^2))
    (u : ElectronL2) :
    (∫⁻ p, ENNReal.ofReal (‖kernelRep b u p‖^2) ∂((volume : Measure GW.Space).prod (volume : Measure GW.Space))) ≤
      ENNReal.ofReal (C^2 * ‖u‖^2) := by
  rw [kernelRep_lintegral b hb]
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (C^2) * ENNReal.ofReal (‖u x‖^2) ∂(volume : Measure GW.Space) := by
      apply lintegral_mono_ae
      filter_upwards [hC] with x hx
      rw [mul_comm]
      gcongr
    _ = _ := by
      rw [lintegral_const_mul _ (((Lp.stronglyMeasurable u).measurable.norm.pow_const 2).ennreal_ofReal),
        ← electron_norm_sq_lintegral u,← ENNReal.ofReal_mul (sq_nonneg C)]

lemma kernelRep_memLp (b : GW.Space × GW.Space → ℂ) (hb : Measurable b)
    {C : ℝ} (hC : ∀ᵐ x ∂(volume : Measure GW.Space), kernelSectionSq b x ≤ ENNReal.ofReal (C^2))
    (u : ElectronL2) :
    MemLp (kernelRep b u) 2 ((volume : Measure GW.Space).prod (volume : Measure GW.Space)) := by
  have hm : AEStronglyMeasurable (kernelRep b u) ((volume : Measure GW.Space).prod (volume : Measure GW.Space)) :=
    (kernelRep_measurable b hb u).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  refine ⟨hm.norm.pow 2,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun _ => sq_nonneg _))).mpr
  exact (kernelRep_lintegral_le b hb hC u).trans_lt ENNReal.ofReal_lt_top

def kernelProductClass (b : GW.Space × GW.Space → ℂ) (hb : Measurable b)
    {C : ℝ} (hC : ∀ᵐ x ∂(volume : Measure GW.Space), kernelSectionSq b x ≤ ENNReal.ofReal (C^2))
    (u : ElectronL2) : ElectronBosonProduct :=
  (kernelRep_memLp b hb hC u).toLp _

lemma kernelProductClass_ae (b : GW.Space × GW.Space → ℂ) (hb : Measurable b)
    {C : ℝ} (hC : ∀ᵐ x ∂(volume : Measure GW.Space), kernelSectionSq b x ≤ ENNReal.ofReal (C^2))
    (u : ElectronL2) :
    kernelProductClass b hb hC u =ᵐ[(volume : Measure GW.Space).prod volume] kernelRep b u :=
  MemLp.coeFn_toLp _

lemma kernelProductClass_sq (b : GW.Space × GW.Space → ℂ) (hb : Measurable b)
    {C : ℝ} (hC : ∀ᵐ x ∂(volume : Measure GW.Space), kernelSectionSq b x ≤ ENNReal.ofReal (C^2))
    (u : ElectronL2) :
    ENNReal.ofReal (‖kernelProductClass b hb hC u‖^2) =
      ∫⁻ x, ENNReal.ofReal (‖u x‖^2) * kernelSectionSq b x ∂(volume : Measure GW.Space) := by
  rw [GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
  rw [ofReal_integral_eq_lintegral_ofReal
    ((Lp.memLp (kernelProductClass b hb hC u)).integrable_norm_pow (p := 2) (by norm_num))
    (Eventually.of_forall (fun _ => sq_nonneg _))]
  refine (lintegral_congr_ae ((kernelProductClass_ae b hb hC u).mono
    (fun p hp => congrArg (fun z : ℂ => ENNReal.ofReal (‖z‖^2)) hp))).trans ?_
  exact kernelRep_lintegral b hb u

lemma kernelProductClass_norm (b : GW.Space × GW.Space → ℂ) (hb : Measurable b)
    {C : ℝ} (hC₀ : 0 ≤ C)
    (hC : ∀ᵐ x ∂(volume : Measure GW.Space), kernelSectionSq b x ≤ ENNReal.ofReal (C^2))
    (u : ElectronL2) :
    ‖kernelProductClass b hb hC u‖ ≤ C * ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC₀ (norm_nonneg _))).mp
  rw [mul_pow]
  have he := kernelProductClass_sq b hb hC u
  rw [← kernelRep_lintegral b hb u] at he
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg _) (sq_nonneg _))).mp
  exact he.symm ▸ kernelRep_lintegral_le b hb hC u

def kernelProductLinear (b : GW.Space × GW.Space → ℂ) (hb : Measurable b)
    {C : ℝ} (hC : ∀ᵐ x ∂(volume : Measure GW.Space), kernelSectionSq b x ≤ ENNReal.ofReal (C^2)) :
    ElectronL2 →ₗ[ℂ] ElectronBosonProduct where
  toFun := kernelProductClass b hb hC
  map_add' u v := by
    apply Lp.ext
    filter_upwards [kernelProductClass_ae b hb hC (u+v),kernelProductClass_ae b hb hC u,
      kernelProductClass_ae b hb hC v,Lp.coeFn_add (kernelProductClass b hb hC u) (kernelProductClass b hb hC v),
      (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure GW.Space)) (ν := volume)).ae (Lp.coeFn_add u v)]
      with p h₁ h₂ h₃ h₄ h₅
    rw [h₁,h₄,Pi.add_apply,h₂,h₃]
    change b p * (u+v) p.1 = b p * u p.1 + b p * v p.1
    rw [show (u+v) p.1 = u p.1+v p.1 from h₅,mul_add]
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [kernelProductClass_ae b hb hC (c • u),kernelProductClass_ae b hb hC u,
      Lp.coeFn_smul c (kernelProductClass b hb hC u),
      (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure GW.Space)) (ν := volume)).ae (Lp.coeFn_smul c u)]
      with p h₁ h₂ h₃ h₄
    change kernelProductClass b hb hC (c • u) p = (c • kernelProductClass b hb hC u) p
    rw [h₁,h₃,Pi.smul_apply,h₂]
    change b p * (c • u) p.1 = c * (b p * u p.1)
    rw [show (c • u) p.1 = c * u p.1 from h₄]
    ring

def kernelProductIdentification : Lp ElectronL2 2 (volume : Measure GW.Space) ≃ₗᵢ[ℂ] ElectronBosonProduct :=
  (productUnitary volume volume).trans (swapProduct volume volume)

def multiplicationKernel (b : GW.Space × GW.Space → ℂ) (hb : Measurable b)
    {C : ℝ} (hC₀ : 0 ≤ C)
    (hC : ∀ᵐ x ∂(volume : Measure GW.Space), kernelSectionSq b x ≤ ENNReal.ofReal (C^2)) :
    BosonKernel ElectronL2 :=
  kernelProductIdentification.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((kernelProductLinear b hb hC).mkContinuous C (kernelProductClass_norm b hb hC₀ hC))

lemma multiplicationKernel_product (b : GW.Space × GW.Space → ℂ) (hb : Measurable b)
    {C : ℝ} (hC₀ : 0 ≤ C)
    (hC : ∀ᵐ x ∂(volume : Measure GW.Space), kernelSectionSq b x ≤ ENNReal.ofReal (C^2))
    (u : ElectronL2) :
    kernelProductIdentification (multiplicationKernel b hb hC₀ hC u) = kernelProductClass b hb hC u :=
  kernelProductIdentification.apply_symm_apply _

lemma multiplicationKernel_norm (b : GW.Space × GW.Space → ℂ) (hb : Measurable b)
    {C : ℝ} (hC₀ : 0 ≤ C)
    (hC : ∀ᵐ x ∂(volume : Measure GW.Space), kernelSectionSq b x ≤ ENNReal.ofReal (C^2)) :
    ‖multiplicationKernel b hb hC₀ hC‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC₀
  intro u
  rw [← kernelProductIdentification.norm_map (multiplicationKernel b hb hC₀ hC u),
    multiplicationKernel_product]
  exact kernelProductClass_norm b hb hC₀ hC u

def kernelEssSectionSq (b : GW.Space × GW.Space → ℂ) : ℝ≥0∞ :=
  essSup (kernelSectionSq b) (volume : Measure GW.Space)

def kernelEssSectionNorm (b : GW.Space × GW.Space → ℂ) : ℝ :=
  Real.sqrt (kernelEssSectionSq b).toReal

lemma kernelEssSectionNorm_bound (b : GW.Space × GW.Space → ℂ)
    (h : kernelEssSectionSq b ≠ ∞) :
    ∀ᵐ x ∂(volume : Measure GW.Space),
      kernelSectionSq b x ≤ ENNReal.ofReal (kernelEssSectionNorm b ^ 2) := by
  have he : ENNReal.ofReal (kernelEssSectionNorm b ^ 2) = kernelEssSectionSq b := by
    rw [kernelEssSectionNorm,Real.sq_sqrt ENNReal.toReal_nonneg,ENNReal.ofReal_toReal h]
  rw [he]
  exact ENNReal.ae_le_essSup (kernelSectionSq b)

def essentialMultiplicationKernel (b : GW.Space × GW.Space → ℂ) (hb : Measurable b)
    (h : kernelEssSectionSq b ≠ ∞) : BosonKernel ElectronL2 :=
  multiplicationKernel b hb (Real.sqrt_nonneg _) (kernelEssSectionNorm_bound b h)

lemma essentialMultiplicationKernel_norm (b : GW.Space × GW.Space → ℂ) (hb : Measurable b)
    (h : kernelEssSectionSq b ≠ ∞) :
    ‖essentialMultiplicationKernel b hb h‖ ≤ kernelEssSectionNorm b :=
  multiplicationKernel_norm b hb (Real.sqrt_nonneg _) (kernelEssSectionNorm_bound b h)

def phaseKernelRep (f : OneBoson) (p : GW.Space × GW.Space) : ℂ :=
  GW.Analysis.physicalPhase p.2 p.1 * f p.2

lemma phaseKernelRep_measurable (f : OneBoson) : Measurable (phaseKernelRep f) := by
  apply Measurable.mul
  · apply Continuous.measurable
    unfold GW.Analysis.physicalPhase
    fun_prop
  · exact (Lp.stronglyMeasurable f).measurable.comp measurable_snd

lemma phaseKernelRep_sectionSq (f : OneBoson) (x : GW.Space) :
    kernelSectionSq (phaseKernelRep f) x = ENNReal.ofReal (‖f‖^2) := by
  unfold kernelSectionSq
  simp only [phaseKernelRep,norm_mul,GW.Analysis.physicalPhase_norm,one_mul]
  exact (electron_norm_sq_lintegral f).symm

lemma phaseKernelRep_bound (f : OneBoson) :
    ∀ᵐ x ∂(volume : Measure GW.Space), kernelSectionSq (phaseKernelRep f) x ≤ ENNReal.ofReal (‖f‖^2) :=
  Eventually.of_forall (fun x => (phaseKernelRep_sectionSq f x).le)

def phaseMultiplicationKernel (f : OneBoson) : BosonKernel ElectronL2 :=
  multiplicationKernel (phaseKernelRep f) (phaseKernelRep_measurable f) (norm_nonneg f) (phaseKernelRep_bound f)

lemma phaseMultiplicationKernel_apply_norm (f : OneBoson) (u : ElectronL2) :
    ‖phaseMultiplicationKernel f u‖ = ‖f‖ * ‖u‖ := by
  let b := phaseKernelRep f
  let hb := phaseKernelRep_measurable f
  let h := phaseKernelRep_bound f
  rw [← kernelProductIdentification.norm_map (phaseMultiplicationKernel f u)]
  change ‖kernelProductIdentification (multiplicationKernel b hb (norm_nonneg f) h u)‖ = _
  rw [multiplicationKernel_product]
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  apply (ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _) (sq_nonneg _)).mp
  rw [kernelProductClass_sq]
  simp_rw [show ∀ x, kernelSectionSq b x = ENNReal.ofReal (‖f‖^2) from phaseKernelRep_sectionSq f]
  simp_rw [mul_comm _ (ENNReal.ofReal (‖f‖^2))]
  rw [lintegral_const_mul _ (((Lp.stronglyMeasurable u).measurable.norm.pow_const 2).ennreal_ofReal),
    ← electron_norm_sq_lintegral u,← ENNReal.ofReal_mul (sq_nonneg _),mul_pow]

lemma phaseMultiplicationKernel_norm (f : OneBoson) :
    ‖phaseMultiplicationKernel f‖ = ‖f‖ := by
  apply le_antisymm (multiplicationKernel_norm _ _ (norm_nonneg f) _)
  let A := Metric.ball (0 : GW.Space) 1
  have hA : MeasurableSet A := measurableSet_ball
  have hf : (volume : Measure GW.Space) A ≠ ∞ := measure_ball_lt_top.ne
  let u : ElectronL2 := indicatorConstLp 2 hA hf (1:ℂ)
  have hu : 0 < ‖u‖ := by
    change 0 < ‖indicatorConstLp 2 hA hf (1:ℂ)‖
    rw [norm_indicatorConstLp (by norm_num : (2:ℝ≥0∞) ≠ 0) (by norm_num : (2:ℝ≥0∞) ≠ ∞)]
    have hpos := Metric.measure_ball_pos (μ := (volume : Measure GW.Space)) (0 : GW.Space) zero_lt_one
    have hV : 0 < (volume : Measure GW.Space).real A := ENNReal.toReal_pos hpos.ne' hf
    simp only [norm_one,one_mul]
    exact Real.rpow_pos_of_pos hV _
  apply le_of_mul_le_mul_right _ hu
  calc
    ‖f‖ * ‖u‖ = ‖phaseMultiplicationKernel f u‖ := (phaseMultiplicationKernel_apply_norm f u).symm
    _ ≤ ‖phaseMultiplicationKernel f‖ * ‖u‖ := (phaseMultiplicationKernel f).le_opNorm u

end MultiplicationKernels
end GW.Fock
