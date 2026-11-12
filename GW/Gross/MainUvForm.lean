module
public import GW.Gross.MainGrossForm
public import GW.Operators.Polarization

/-! Source main:uv-form, manuscript5815–5863.
Actual cutoff fields, exact finite shell/tail differences, original commutators,
sharp diagonal form-core extension and Hermitian mixed bound, including alpha0. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Gross
open GW.Model GW.Fock GW.Analysis

/- Source argument component Pairings02. -/
lemma uvFormalAdjoint_graph_pairing {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T S : H →ₗ.[ℂ] H) (h : T.IsFormalAdjoint S) (u v a b : H)
    (ha : (u,a) ∈ T.graph) (hb : (v,b) ∈ S.graph) : ⟪a,v⟫_ℂ = ⟪u,b⟫_ℂ := by
  obtain ⟨x,hx,hax⟩ := T.mem_graph_iff.mp ha
  obtain ⟨y,hy,hby⟩ := S.mem_graph_iff.mp hb
  dsimp only [Prod.fst,Prod.snd] at hx hax hy hby
  have hp := h x y
  rw [hx,hy,hax,hby] at hp
  exact hp

lemma uvCreatorAnnihilator_formal (F : BosonKernel ElectronL2) :
    (generalizedCreation F).IsFormalAdjoint (generalizedAnnihilation F) := by
  have hd : Dense ((generalizedCreation F).domain : Set Physical) :=
    representationTransport_dense electronBosonUnitary.symm _
      (maximalSectorCreation_dense (generalizedCreationSector F))
  have h := (LinearPMap.adjoint_isFormalAdjoint hd).symm
  exact (congrArg (fun A : Physical →ₗ.[ℂ] Physical => (generalizedCreation F).IsFormalAdjoint A)
    (generalizedCreation_adjoint_eq F)).mp h

lemma uvPhase_pairing (f : OneBoson) (u v : FiberPhysicalRoot) :
    ⟪commutatorPhaseCreatorMap f u,(fiberPhysicalRootInput v).val⟫_ℂ =
      ⟪(fiberPhysicalRootInput u).val,commutatorPhaseAnnihilatorMap f v⟫_ℂ :=
  uvFormalAdjoint_graph_pairing _ _ (uvCreatorAnnihilator_formal (phaseMultiplicationKernel f)) _ _ _ _
    (commutatorPhaseCreatorMap_graph f u) (commutatorPhaseAnnihilatorMap_graph f v)

lemma uvPhase_field_diagonal (f : OneBoson) (u : FiberPhysicalRoot) :
    ⟪(fiberPhysicalRootInput u).val,grossFormFieldMap f u⟫_ℂ =
      ⟪(fiberPhysicalRootInput u).val,commutatorPhaseAnnihilatorMap f u⟫_ℂ+
      star ⟪(fiberPhysicalRootInput u).val,commutatorPhaseAnnihilatorMap f u⟫_ℂ := by
  change ⟪(fiberPhysicalRootInput u).val,commutatorPhaseAnnihilatorMap f u+commutatorPhaseCreatorMap f u⟫_ℂ = _
  have hc : ⟪(fiberPhysicalRootInput u).val,commutatorPhaseCreatorMap f u⟫_ℂ =
      star ⟪(fiberPhysicalRootInput u).val,commutatorPhaseAnnihilatorMap f u⟫_ℂ :=
    (inner_conj_symm _ _).symm.trans (congrArg star (uvPhase_pairing f u u))
  rw [inner_add_right,hc]

lemma uvMomentum_formal (j : Fin 3) :
    (electronMomentumCoordinate j).IsFormalAdjoint (electronMomentumCoordinate j) := by
  have h := physicalSectorMultiplier_selfadjoint (fun _ => electronCoordinate_measurable j)
  have hform := (LinearPMap.adjoint_isFormalAdjoint h.1).symm
  exact (congrArg (fun A : Physical →ₗ.[ℂ] Physical => (electronMomentumCoordinate j).IsFormalAdjoint A)
    h.2).mp hform

/- Source argument component Shell02. -/
def uvShellCoefficient (α L₁ L₂ : ℝ) (hα : 0 ≤ α) (h₁ : 0 < L₁) (h₂ : 0 < L₂) : OneBoson :=
  cutoffL2 α L₁ hα h₁-cutoffL2 α L₂ hα h₂

def uvShellRaw (α L₁ L₂ : ℝ) (k : GW.Space) : ℂ := (GW.Model.cutoff α L₁ k:ℂ)-(GW.Model.cutoff α L₂ k:ℂ)

lemma uvShellCoefficient_ae (α L₁ L₂ : ℝ) (hα : 0 ≤ α) (h₁ : 0 < L₁) (h₂ : 0 < L₂) :
    uvShellCoefficient α L₁ L₂ hα h₁ h₂ =ᵐ[volume] uvShellRaw α L₁ L₂ := by
  filter_upwards [Lp.coeFn_sub (cutoffL2 α L₁ hα h₁) (cutoffL2 α L₂ hα h₂),
    cutoffL2_ae α L₁ hα h₁,cutoffL2_ae α L₂ hα h₂] with k hs hA hB
  change (cutoffL2 α L₁ hα h₁-cutoffL2 α L₂ hα h₂) k = _
  rw [hs]
  change cutoffL2 α L₁ hα h₁ k-cutoffL2 α L₂ hα h₂ k = _
  rw [hA,hB]
  rfl

lemma uvShellRaw_measurable (α L₁ L₂ : ℝ) : Measurable (uvShellRaw α L₁ L₂) :=
  (Complex.continuous_ofReal.measurable.comp (cutoff_measurable α L₁)).sub
    (Complex.continuous_ofReal.measurable.comp (cutoff_measurable α L₂))

lemma uvShellRaw_memLp (α L₁ L₂ : ℝ) (hα : 0 ≤ α) (h₁ : 0 < L₁) (h₂ : 0 < L₂) :
    MemLp (uvShellRaw α L₁ L₂) 2 (volume : Measure GW.Space) :=
  (cutoff_memLp α L₁ hα h₁).sub (cutoff_memLp α L₂ hα h₂)

lemma uvShellRaw_low_zero (α L₁ L₂ : ℝ) (k : GW.Space) (hk : ‖k‖ ≤ min L₁ L₂) :
    uvShellRaw α L₁ L₂ k = 0 := by
  rw [uvShellRaw,GW.Model.cutoff,if_pos (hk.trans (min_le_left _ _)),GW.Model.cutoff,if_pos (hk.trans (min_le_right _ _)),sub_self]

def uvShellARaw (α L₁ L₂ : ℝ) (j : Fin 3) (k : GW.Space) : ℂ :=
  ((k j:ℂ)/((‖k‖^2:ℝ):ℂ))*uvShellRaw α L₁ L₂ k

lemma uvShellARaw_measurable (α L₁ L₂ : ℝ) (j : Fin 3) : Measurable (uvShellARaw α L₁ L₂ j) :=
  ((Complex.continuous_ofReal.measurable.comp (electronCoordinate_measurable j)).div
    (Complex.continuous_ofReal.measurable.comp (measurable_norm.pow_const 2))).mul (uvShellRaw_measurable α L₁ L₂)

lemma uvShellARaw_bound (α L₁ L₂ : ℝ) (h₁ : 0 < L₁) (h₂ : 0 < L₂) (j : Fin 3) (k : GW.Space) :
    ‖uvShellARaw α L₁ L₂ j k‖ ≤ (min L₁ L₂)⁻¹*‖uvShellRaw α L₁ L₂ k‖ := by
  by_cases hk : ‖k‖ ≤ min L₁ L₂
  · rw [uvShellARaw,uvShellRaw_low_zero α L₁ L₂ k hk,mul_zero,norm_zero,mul_zero]
  · have hmin : 0 < min L₁ L₂ := lt_min h₁ h₂
    have hkm : min L₁ L₂ ≤ ‖k‖ := (lt_of_not_ge hk).le
    have hkn : 0 < ‖k‖ := hmin.trans_le hkm
    rw [uvShellARaw,norm_mul,norm_div,Complex.norm_real,Complex.norm_real,
      Real.norm_eq_abs,Real.norm_of_nonneg (sq_nonneg _)]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply (div_le_iff₀ (sq_pos_of_pos hkn)).mpr
    have hprod : (min L₁ L₂)*‖k‖ ≤ ‖k‖^2 := by nlinarith
    have hs : ‖k‖ ≤ (min L₁ L₂)⁻¹*‖k‖^2 := by
      calc
        _ ≤ ‖k‖^2/(min L₁ L₂) := (le_div_iff₀ hmin).mpr (by nlinarith)
        _ = _ := by rw [div_eq_mul_inv,mul_comm]
    exact (electronCoordinate_abs_le k j).trans hs

lemma uvShellARaw_memLp (α L₁ L₂ : ℝ) (hα : 0 ≤ α) (h₁ : 0 < L₁) (h₂ : 0 < L₂) (j : Fin 3) :
    MemLp (uvShellARaw α L₁ L₂ j) 2 (volume : Measure GW.Space) :=
  (uvShellRaw_memLp α L₁ L₂ hα h₁ h₂).of_le_mul
    (uvShellARaw_measurable α L₁ L₂ j).aestronglyMeasurable
    (Eventually.of_forall (uvShellARaw_bound α L₁ L₂ h₁ h₂ j))

/- Source argument component Coefficients02. -/
def uvShellA (α L₁ L₂ : ℝ) (hα : 0 ≤ α) (h₁ : 0 < L₁) (h₂ : 0 < L₂) (j : Fin 3) : OneBoson :=
  (uvShellARaw_memLp α L₁ L₂ hα h₁ h₂ j).toLp _
lemma uvShellA_ae (α L₁ L₂ : ℝ) (hα : 0 ≤ α) (h₁ : 0 < L₁) (h₂ : 0 < L₂) (j : Fin 3) :
    uvShellA α L₁ L₂ hα h₁ h₂ j =ᵐ[volume] uvShellARaw α L₁ L₂ j := MemLp.coeFn_toLp _

lemma uvShellARaw_moment_bound (α L₁ L₂ : ℝ) (i j : Fin 3) (k : GW.Space) :
    ‖(k i : ℂ)*uvShellARaw α L₁ L₂ j k‖ ≤ ‖uvShellRaw α L₁ L₂ k‖ := by
  by_cases hk : k = 0
  · subst k
    simp only [PiLp.zero_apply,Complex.ofReal_zero,zero_mul,norm_zero]
    exact norm_nonneg _
  · have hkn : 0 < ‖k‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hk)
    have hp : |k i| * |k j| ≤ ‖k‖^2 := by
      simpa only [pow_two] using mul_le_mul (electronCoordinate_abs_le k i)
        (electronCoordinate_abs_le k j) (abs_nonneg _) (norm_nonneg _)
    have hd : |k i| * |k j|/‖k‖^2 ≤ 1 := (div_le_one hkn).mpr hp
    simp only [uvShellARaw,norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs]
    rw [abs_of_nonneg (sq_nonneg ‖k‖)]
    calc
      _ = (|k i| * |k j|/‖k‖^2)*‖uvShellRaw α L₁ L₂ k‖ := by ring
      _ ≤ 1*‖uvShellRaw α L₁ L₂ k‖ := mul_le_mul_of_nonneg_right hd (norm_nonneg _)
      _ = _ := one_mul _

lemma uvShellARaw_moment_memLp (α L₁ L₂ : ℝ) (hα : 0 ≤ α) (h₁ : 0 < L₁) (h₂ : 0 < L₂)
    (i j : Fin 3) : MemLp (fun k => (k i : ℂ)*uvShellARaw α L₁ L₂ j k) 2 (volume : Measure GW.Space) := by
  apply (uvShellRaw_memLp α L₁ L₂ hα h₁ h₂).of_le_mul (c := 1)
    (((Complex.continuous_ofReal.measurable.comp (electronCoordinate_measurable i)).mul
      (uvShellARaw_measurable α L₁ L₂ j)).aestronglyMeasurable)
  apply Eventually.of_forall
  intro k
  change ‖(k i : ℂ)*uvShellARaw α L₁ L₂ j k‖ ≤ 1*‖uvShellRaw α L₁ L₂ k‖
  simpa only [one_mul] using uvShellARaw_moment_bound α L₁ L₂ i j k

lemma uvShellA_moment_memLp (α L₁ L₂ : ℝ) (hα : 0 ≤ α) (h₁ : 0 < L₁) (h₂ : 0 < L₂)
    (i j : Fin 3) : MemLp (fun k => (k i : ℂ)*uvShellA α L₁ L₂ hα h₁ h₂ j k) 2 (volume : Measure GW.Space) := by
  apply (memLp_congr_ae _).mp (uvShellARaw_moment_memLp α L₁ L₂ hα h₁ h₂ i j)
  filter_upwards [uvShellA_ae α L₁ L₂ hα h₁ h₂ j] with k hk
  rw [hk]

lemma uvShellA_moment_sum (α L₁ L₂ : ℝ) (hα : 0 ≤ α) (h₁ : 0 < L₁) (h₂ : 0 < L₂) :
    (∑ j : Fin 3,weylMomentumCoefficient (uvShellA α L₁ L₂ hα h₁ h₂ j) j
      (uvShellA_moment_memLp α L₁ L₂ hα h₁ h₂ j j)) = uvShellCoefficient α L₁ L₂ hα h₁ h₂ := by
  let A := uvShellA α L₁ L₂ hα h₁ h₂
  let ms := fun j : Fin 3 => weylMomentumCoefficient (A j) j (uvShellA_moment_memLp α L₁ L₂ hα h₁ h₂ j j)
  have hA (j : Fin 3) := uvShellA_ae α L₁ L₂ hα h₁ h₂ j
  have hm (j : Fin 3) := weylMomentumCoefficient_ae (A j) j (uvShellA_moment_memLp α L₁ L₂ hα h₁ h₂ j j)
  apply Lp.ext
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ ms,ae_all_iff.mpr hA,ae_all_iff.mpr hm,
    uvShellCoefficient_ae α L₁ L₂ hα h₁ h₂] with k hs hAk hmk hg
  change (∑ j : Fin 3,ms j) k = _
  rw [hs,hg]
  change (∑ j : Fin 3,ms j k) = _
  have he (j : Fin 3) : ms j k = (k j : ℂ)*uvShellARaw α L₁ L₂ j k :=
    (hmk j).trans (congrArg (fun z : ℂ => (k j : ℂ)*z) (hAk j))
  simp_rw [he]
  by_cases hk : k = 0
  · subst k
    simp [uvShellARaw,uvShellRaw,GW.Model.cutoff,v]
  · have hd : ((‖k‖^2:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr hk)))
    have hsq : (∑ j : Fin 3,(k j : ℂ)^2) = ((‖k‖^2:ℝ):ℂ) := by
      rw [EuclideanSpace.real_norm_sq_eq,Complex.ofReal_sum]
      simp only [Complex.ofReal_pow]
    simp only [uvShellARaw]
    calc
      _ = (∑ j : Fin 3,(k j:ℂ)^2)/((‖k‖^2:ℝ):ℂ)*uvShellRaw α L₁ L₂ k := by
        rw [Finset.sum_div,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [hsq,div_self hd,one_mul]

/- Source argument component Commutator02. -/
lemma uvCommutator_inner (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) (u : FreeGraphDomain) :
    ⟪freeGraphDomainInclusion u,commutatorPhaseAnnihilatorMap (weylMomentumCoefficient f j hj) (commutatorGraphRootMap u)⟫_ℂ =
      ⟪electronMomentumCoordinate j (commutatorMomentumInput u j),commutatorPhaseAnnihilatorMap f (commutatorGraphRootMap u)⟫_ℂ-
      ⟪commutatorPhaseCreatorMap f (commutatorGraphRootMap u),electronMomentumCoordinate j (commutatorMomentumInput u j)⟫_ℂ := by
  have hp := (electronMomentumCoordinate j).mem_graph (commutatorMomentumInput u j)
  have hU : (commutatorMomentumInput u j).val = freeGraphDomainInclusion u :=
    (freeGraphDomainInclusion_apply u).symm
  rw [hU] at hp
  have hA := commutatorAnnihilator_graph_all f j hj u
  change (commutatorPhaseAnnihilatorMap f (commutatorGraphRootMap u),
    commutatorPhaseAnnihilatorMap f (commutatorGraphMomentumRootMap j u)+
      commutatorPhaseAnnihilatorMap (weylMomentumCoefficient f j hj) (commutatorGraphRootMap u)) ∈ _ at hA
  have hpair := uvFormalAdjoint_graph_pairing _ _ (uvMomentum_formal j) _ _ _ _ hp hA
  rw [inner_add_right] at hpair
  have hca := uvPhase_pairing f (commutatorGraphRootMap u) (commutatorGraphMomentumRootMap j u)
  rw [commutatorGraphRootMap_value,commutatorGraphMomentumRootMap_value] at hca
  rw [← hca] at hpair
  apply (eq_sub_iff_add_eq).mpr
  exact (add_comm _ _).trans hpair.symm

lemma uvShell_commutator_inner (α L₁ L₂ : ℝ) (hα : 0 ≤ α) (h₁ : 0 < L₁) (h₂ : 0 < L₂)
    (u : FreeGraphDomain) :
    ⟪freeGraphDomainInclusion u,commutatorPhaseAnnihilatorMap (uvShellCoefficient α L₁ L₂ hα h₁ h₂)
      (commutatorGraphRootMap u)⟫_ℂ =
      ∑ j : Fin 3, (⟪electronMomentumCoordinate j (commutatorMomentumInput u j),
        commutatorPhaseAnnihilatorMap (uvShellA α L₁ L₂ hα h₁ h₂ j) (commutatorGraphRootMap u)⟫_ℂ-
      ⟪commutatorPhaseCreatorMap (uvShellA α L₁ L₂ hα h₁ h₂ j) (commutatorGraphRootMap u),
        electronMomentumCoordinate j (commutatorMomentumInput u j)⟫_ℂ) := by
  rw [← uvShellA_moment_sum α L₁ L₂ hα h₁ h₂,grossFormAnnihilator_sum,inner_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact uvCommutator_inner _ j (uvShellA_moment_memLp α L₁ L₂ hα h₁ h₂ j j) u

/- Source argument component Density03. -/
def uvTailDensity (α R : ℝ) : GW.Space → ℝ :=
  (highRegion R).indicator (fun k => (v α k)^2/‖k‖^2)
def uvShellDensity (α L₁ L₂ : ℝ) (k : GW.Space) : ℝ :=
  ‖uvShellRaw α L₁ L₂ k‖^2/‖k‖^2

lemma uvTailDensity_integrable (α R : ℝ) (hα : 0 ≤ α) (hR : 0 < R) :
    Integrable (uvTailDensity α R) (volume : Measure GW.Space) := by
  have hi : IntegrableOn (fun k : GW.Space => (v α k)^2/‖k‖^2) (highRegion R) (volume : Measure GW.Space) := (nonnegative_realIntegral_of_lintegral (μ := (volume : Measure GW.Space).restrict (highRegion R))
    (((v_measurable α).pow_const 2).div (measurable_norm.pow_const 2))
    (fun k => div_nonneg (sq_nonneg _) (sq_nonneg _)) (coefficientDTailENN_finite α R hα hR)).1
  exact hi.integrable_indicator (highRegion_measurable R)

lemma uvTailDensity_integral (α R : ℝ) (hα : 0 ≤ α) (hR : 0 < R) :
    (∫ k, uvTailDensity α R k ∂(volume : Measure GW.Space)) = coefficientDTail α R := by
  rw [uvTailDensity,integral_indicator (highRegion_measurable R)]
  exact (coefficientDTail_eq_integral α R hα hR).symm

lemma uvShellDensity_split (α L₁ L₂ : ℝ) (hL : L₁ ≤ L₂) (k : GW.Space) :
    uvTailDensity α L₁ k = uvShellDensity α L₁ L₂ k+uvTailDensity α L₂ k := by
  by_cases h₁ : ‖k‖ ≤ L₁
  · have h₂ := h₁.trans hL
    simp [uvTailDensity,highRegion,uvShellDensity,uvShellRaw,GW.Model.cutoff,h₁,h₂,not_lt.mpr h₁,not_lt.mpr h₂]
  · have h₁' : L₁ < ‖k‖ := lt_of_not_ge h₁
    by_cases h₂ : ‖k‖ ≤ L₂
    · simp [uvTailDensity,highRegion,uvShellDensity,uvShellRaw,GW.Model.cutoff,h₁,h₂,h₁',not_lt.mpr h₂,
        Complex.norm_real,Real.norm_eq_abs,sq_abs]
    · have h₂' : L₂ < ‖k‖ := lt_of_not_ge h₂
      simp [uvTailDensity,highRegion,uvShellDensity,uvShellRaw,GW.Model.cutoff,h₁,h₂,h₁',h₂']

lemma uvShellDensity_integrable_ordered (α L₁ L₂ : ℝ) (hα : 0 ≤ α) (h₁ : 0 < L₁) (h₂ : 0 < L₂)
    (hL : L₁ ≤ L₂) : Integrable (uvShellDensity α L₁ L₂) (volume : Measure GW.Space) := by
  have he : uvShellDensity α L₁ L₂ = uvTailDensity α L₁-uvTailDensity α L₂ := by
    funext k
    have h := uvShellDensity_split α L₁ L₂ hL k
    change _ = uvTailDensity α L₁ k-uvTailDensity α L₂ k
    linarith
  rw [he]
  exact (uvTailDensity_integrable α L₁ hα h₁).sub (uvTailDensity_integrable α L₂ hα h₂)

lemma uvShellDensity_integral_ordered (α L₁ L₂ : ℝ) (hα : 0 ≤ α) (h₁ : 0 < L₁) (h₂ : 0 < L₂)
    (hL : L₁ ≤ L₂) :
    (∫ k, uvShellDensity α L₁ L₂ k ∂(volume : Measure GW.Space)) = coefficientDTail α L₁-coefficientDTail α L₂ := by
  have h := integral_add (uvShellDensity_integrable_ordered α L₁ L₂ hα h₁ h₂ hL)
    (uvTailDensity_integrable α L₂ hα h₂)
  have he : uvTailDensity α L₁ = uvShellDensity α L₁ L₂+uvTailDensity α L₂ :=
    funext (uvShellDensity_split α L₁ L₂ hL)
  have hD : coefficientDTail α L₁ =
      (∫ k, uvShellDensity α L₁ L₂ k ∂(volume : Measure GW.Space))+coefficientDTail α L₂ := by
    rw [← uvTailDensity_integral α L₁ hα h₁,he]
    exact h.trans (congrArg₂ (·+·) rfl (uvTailDensity_integral α L₂ hα h₂))
  linarith

/- Source argument component DensitySymm01. -/
lemma uvShellDensity_swap (α L₁ L₂ : ℝ) : uvShellDensity α L₁ L₂ = uvShellDensity α L₂ L₁ := by
  funext k
  have he : uvShellRaw α L₁ L₂ k = -uvShellRaw α L₂ L₁ k := by unfold uvShellRaw; abel
  rw [uvShellDensity,uvShellDensity,he,norm_neg]

lemma uvShellDensity_integrable (α L₁ L₂ : ℝ) (hα : 0 ≤ α) (h₁ : 0 < L₁) (h₂ : 0 < L₂) :
    Integrable (uvShellDensity α L₁ L₂) (volume : Measure GW.Space) := by
  rcases le_total L₁ L₂ with h|h
  · exact uvShellDensity_integrable_ordered α L₁ L₂ hα h₁ h₂ h
  · rw [uvShellDensity_swap]
    exact uvShellDensity_integrable_ordered α L₂ L₁ hα h₂ h₁ h

lemma uvShellDensity_integral (α L₁ L₂ : ℝ) (hα : 0 ≤ α) (h₁ : 0 < L₁) (h₂ : 0 < L₂) :
    (∫ k, uvShellDensity α L₁ L₂ k ∂(volume : Measure GW.Space)) =
      |coefficientDTail α L₁-coefficientDTail α L₂| := by
  rcases le_total L₁ L₂ with h|h
  · rw [abs_of_nonneg (sub_nonneg.mpr (coefficientDTail_antitone α hα h₁ h))]
    exact uvShellDensity_integral_ordered α L₁ L₂ hα h₁ h₂ h
  · rw [uvShellDensity_swap,abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr (coefficientDTail_antitone α hα h₂ h))]
    exact uvShellDensity_integral_ordered α L₂ L₁ hα h₂ h₁ h

/- Source argument component Norms02. -/
lemma uvShellARaw_density_sum (α L₁ L₂ : ℝ) (k : GW.Space) :
    (∑ j : Fin 3, ‖uvShellARaw α L₁ L₂ j k‖^2) = uvShellDensity α L₁ L₂ k := by
  by_cases hk : k = 0
  · subst k
    simp [uvShellARaw,uvShellDensity]
  · have hr : ‖k‖^2 ≠ 0 := ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr hk))
    have he (j : Fin 3) : ‖uvShellARaw α L₁ L₂ j k‖^2 =
        (k j)^2/(‖k‖^2)^2*‖uvShellRaw α L₁ L₂ k‖^2 := by
      simp only [uvShellARaw,norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,mul_pow,div_pow,sq_abs]
    simp_rw [he]
    calc
      _ = (∑ j : Fin 3,(k j)^2)/(‖k‖^2)^2*‖uvShellRaw α L₁ L₂ k‖^2 := by
        rw [Finset.sum_div,Finset.sum_mul]
      _ = ‖k‖^2/(‖k‖^2)^2*‖uvShellRaw α L₁ L₂ k‖^2 := by rw [← EuclideanSpace.real_norm_sq_eq]
      _ = _ := by unfold uvShellDensity; field_simp [hr] <;> ring

lemma uvShellA_norm_sq (α L₁ L₂ : ℝ) (hα : 0 ≤ α) (h₁ : 0 < L₁) (h₂ : 0 < L₂) :
    (∑ j : Fin 3, ‖uvShellA α L₁ L₂ hα h₁ h₂ j‖^2) =
      |coefficientDTail α L₁-coefficientDTail α L₂| := by
  have hn (j : Fin 3) : ‖uvShellA α L₁ L₂ hα h₁ h₂ j‖^2 =
      ∫ k, ‖uvShellARaw α L₁ L₂ j k‖^2 ∂(volume : Measure GW.Space) := by
    rw [GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
    apply integral_congr_ae
    exact (uvShellA_ae α L₁ L₂ hα h₁ h₂ j).mono fun k hk => congrArg (fun z : ℂ => ‖z‖^2) hk
  calc
    _ = ∑ j : Fin 3, ∫ k, ‖uvShellARaw α L₁ L₂ j k‖^2 ∂(volume : Measure GW.Space) :=
      Finset.sum_congr rfl (fun j _ => hn j)
    _ = ∫ k, (∑ j : Fin 3, ‖uvShellARaw α L₁ L₂ j k‖^2) ∂(volume : Measure GW.Space) :=
      (integral_finsetSum Finset.univ (fun j _ => (uvShellARaw_memLp α L₁ L₂ hα h₁ h₂ j).integrable_norm_pow
        (p := 2) (by norm_num))).symm
    _ = ∫ k, uvShellDensity α L₁ L₂ k ∂(volume : Measure GW.Space) :=
      integral_congr_ae (Eventually.of_forall (uvShellARaw_density_sum α L₁ L₂))
    _ = _ := uvShellDensity_integral α L₁ L₂ hα h₁ h₂

/- Source argument component FiniteCS02. -/
lemma uvFinite_inner_commutator_bound (p a c : Fin 3 → Physical) (g : Fin 3 → ℝ) (R : ℝ)
    (hR : 0 ≤ R) (hg : ∀ j, 0 ≤ g j)
    (ha : ∀ j, ‖a j‖ ≤ g j*R) (hc : ∀ j, ‖c j‖ ≤ g j*R) :
    ‖∑ j : Fin 3, (⟪p j,a j⟫_ℂ-⟪c j,p j⟫_ℂ)‖ ≤
      2*Real.sqrt (∑ j : Fin 3,‖p j‖^2)*Real.sqrt (∑ j : Fin 3,(g j)^2)*R := by
  have hb (j : Fin 3) : ‖⟪p j,a j⟫_ℂ-⟪c j,p j⟫_ℂ‖ ≤ 2*(‖p j‖*g j)*R := by
    have hA := (norm_inner_le_norm (𝕜 := ℂ) (p j) (a j)).trans (mul_le_mul_of_nonneg_left (ha j) (norm_nonneg _))
    have hC := (norm_inner_le_norm (𝕜 := ℂ) (c j) (p j)).trans (mul_le_mul_of_nonneg_right (hc j) (norm_nonneg _))
    exact (norm_sub_le _ _).trans ((add_le_add hA hC).trans_eq (by ring))
  calc
    _ ≤ ∑ j : Fin 3, ‖⟪p j,a j⟫_ℂ-⟪c j,p j⟫_ℂ‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin 3, 2*(‖p j‖*g j)*R := Finset.sum_le_sum (fun j _ => hb j)
    _ = 2*(∑ j : Fin 3, ‖p j‖*g j)*R := by rw [Finset.mul_sum,Finset.sum_mul]
    _ ≤ _ := by
      have hs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun j : Fin 3 => ‖p j‖) g
      have h2 : 2*(∑ j : Fin 3,‖p j‖*g j) ≤
          2*(Real.sqrt (∑ j : Fin 3,‖p j‖^2)*Real.sqrt (∑ j : Fin 3,(g j)^2)) :=
        mul_le_mul_of_nonneg_left hs (by norm_num)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right h2 hR

/- Source argument component Diagonal05. -/
lemma uvGraph_form_norm_split (u : FreeGraphDomain) :
    ‖smoothProductGraphToFormMap u‖^2 = ‖commutatorGraphRootMap u‖^2+
      ∑ j : Fin 3,‖electronMomentumCoordinate j (commutatorMomentumInput u j)‖^2 := by
  rw [grossForm_norm_coordinates,grossGraph_to_form_root]
  congr 1

lemma uvShell_diagonal_graph_bound (α L₁ L₂ : ℝ) (hα : 0 ≤ α) (h₁ : 0 < L₁) (h₂ : 0 < L₂)
    (u : FreeGraphDomain) :
    ‖⟪freeGraphDomainInclusion u,grossFormFieldMap (uvShellCoefficient α L₁ L₂ hα h₁ h₂)
      (commutatorGraphRootMap u)⟫_ℂ‖ ≤
      2*Real.sqrt |coefficientDTail α L₁-coefficientDTail α L₂| * ‖smoothProductGraphToFormMap u‖^2 := by
  let p := fun j : Fin 3 => electronMomentumCoordinate j (commutatorMomentumInput u j)
  let A := uvShellA α L₁ L₂ hα h₁ h₂
  let R := ‖commutatorGraphRootMap u‖
  let P := Real.sqrt (∑ j : Fin 3, ‖p j‖^2)
  let rho := Real.sqrt |coefficientDTail α L₁-coefficientDTail α L₂|
  let z := ⟪freeGraphDomainInclusion u,
    commutatorPhaseAnnihilatorMap (uvShellCoefficient α L₁ L₂ hα h₁ h₂) (commutatorGraphRootMap u)⟫_ℂ
  have hz : ‖z‖ ≤ 2*P*rho*R := by
    dsimp only [z]
    rw [uvShell_commutator_inner]
    have h := uvFinite_inner_commutator_bound p
      (fun j => commutatorPhaseAnnihilatorMap (A j) (commutatorGraphRootMap u))
      (fun j => commutatorPhaseCreatorMap (A j) (commutatorGraphRootMap u))
      (fun j => ‖A j‖) R (norm_nonneg _) (fun j => norm_nonneg _)
      (fun j => commutatorPhaseAnnihilatorMap_bound (A j) (commutatorGraphRootMap u))
      (fun j => commutatorPhaseCreatorMap_bound (A j) (commutatorGraphRootMap u))
    rw [uvShellA_norm_sq] at h
    exact h
  have hphi := uvPhase_field_diagonal (uvShellCoefficient α L₁ L₂ hα h₁ h₂) (commutatorGraphRootMap u)
  rw [commutatorGraphRootMap_value] at hphi
  have hP : P^2 = ∑ j : Fin 3,‖p j‖^2 := Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hQ : ‖smoothProductGraphToFormMap u‖^2 = R^2+P^2 := by
    rw [hP]
    exact uvGraph_form_norm_split u
  have hpr : 2*P*R ≤ P^2+R^2 := by nlinarith [sq_nonneg (P-R)]
  have hscalar : 4*rho*P*R ≤ 2*rho*‖smoothProductGraphToFormMap u‖^2 := by
    have h : (2*rho)*(2*P*R) ≤ (2*rho)*(P^2+R^2) :=
      mul_le_mul_of_nonneg_left hpr (mul_nonneg (by norm_num : (0:ℝ) ≤ 2)
        (Real.sqrt_nonneg |coefficientDTail α L₁-coefficientDTail α L₂|))
    rw [hQ]
    nlinarith
  rw [hphi]
  change ‖z+star z‖ ≤ _
  have hs := norm_add_le z (star z)
  rw [norm_star] at hs
  exact hs.trans (((add_le_add hz hz).trans_eq (by ring)).trans hscalar)

/- Source argument component Form01. -/
def uvFieldLinear (f : OneBoson) : FreeFormDomain →L[ℂ] Physical := (grossFormFieldMap f).comp grossFormRootMap

def uvFieldForm (f : OneBoson) : GW.Operators.AlgebraicForm FreeFormDomain where
  toFun u :=
    { toFun w := ⟪freeFormDomainInclusion u,uvFieldLinear f w⟫_ℂ
      map_add' w z := by rw [map_add,inner_add_right]
      map_smul' c w := by simp only [map_smul,inner_smul_right,smul_eq_mul,RingHom.id_apply] }
  map_add' u v := by
    ext w
    change ⟪freeFormDomainInclusion (u+v),uvFieldLinear f w⟫_ℂ =
      ⟪freeFormDomainInclusion u,uvFieldLinear f w⟫_ℂ+⟪freeFormDomainInclusion v,uvFieldLinear f w⟫_ℂ
    rw [map_add,inner_add_left]
  map_smul' c u := by
    ext w
    change ⟪freeFormDomainInclusion (c • u),uvFieldLinear f w⟫_ℂ =
      (starRingEnd ℂ c) • ⟪freeFormDomainInclusion u,uvFieldLinear f w⟫_ℂ
    simp only [map_smul,inner_smul_left,smul_eq_mul]

lemma uvFieldForm_apply (f : OneBoson) (u w : FreeFormDomain) :
    uvFieldForm f u w = ⟪freeFormDomainInclusion u,grossFormFieldMap f (grossFormRootMap w)⟫_ℂ := rfl

lemma uvFieldLinear_graph (f : OneBoson) (u : FreeFormDomain) :
    (freeFormDomainInclusion u,uvFieldLinear f u) ∈ (generalizedField (phaseMultiplicationKernel f)).graph := by
  have h := grossFormFieldMap_graph f (grossFormRootMap u)
  rw [grossFormRootMap_value] at h
  exact h

lemma uvFieldLinear_pairing (f : OneBoson) (u w : FreeFormDomain) :
    ⟪uvFieldLinear f u,freeFormDomainInclusion w⟫_ℂ = ⟪freeFormDomainInclusion u,uvFieldLinear f w⟫_ℂ :=
  uvFormalAdjoint_graph_pairing _ _ (generalizedField_symmetric (phaseMultiplicationKernel f)) _ _ _ _
    (uvFieldLinear_graph f u) (uvFieldLinear_graph f w)

lemma uvFieldForm_hermitian (f : OneBoson) (u w : FreeFormDomain) :
    uvFieldForm f u w = star (uvFieldForm f w u) :=
  (inner_conj_symm _ _).symm.trans (congrArg star (uvFieldLinear_pairing f w u))

lemma uvFieldForm_diagonal_continuous (f : OneBoson) : Continuous (fun u : FreeFormDomain => ‖uvFieldForm f u u‖) :=
  (freeFormDomainInclusion.continuous.inner (𝕜 := ℂ) (uvFieldLinear f).continuous).norm

/- Source argument component Extension03. -/
lemma uvShell_diagonal_core_bound (α L₁ L₂ : ℝ) (hα : 0 ≤ α) (h₁ : 0 < L₁) (h₂ : 0 < L₂)
    (u : FreeFormDomain) (hu : u ∈ smoothFiniteFormCore) :
    ‖uvFieldForm (uvShellCoefficient α L₁ L₂ hα h₁ h₂) u u‖ ≤
      2*Real.sqrt |coefficientDTail α L₁-coefficientDTail α L₂| * ‖u‖^2 := by
  have hs : freeFormDomainInclusion u ∈ smoothFiniteProductCore := hu
  let x : freeHamiltonian.domain := ⟨freeFormDomainInclusion u,smoothFiniteProductCore_le_H0 hs⟩
  let v := commutatorSourceGraphInput x
  have hv : smoothProductGraphToFormMap v = u := by
    apply grossFormDomainInclusion_injective
    exact (smoothProductGraphToForm_inclusion v).trans (commutatorSourceGraphInput_value x)
  have he : uvFieldForm (uvShellCoefficient α L₁ L₂ hα h₁ h₂)
      (smoothProductGraphToFormMap v) (smoothProductGraphToFormMap v) =
      ⟪freeGraphDomainInclusion v,grossFormFieldMap (uvShellCoefficient α L₁ L₂ hα h₁ h₂)
        (commutatorGraphRootMap v)⟫_ℂ := by
    rw [uvFieldForm_apply,smoothProductGraphToForm_inclusion,grossGraph_to_form_root]
  have hb := uvShell_diagonal_graph_bound α L₁ L₂ hα h₁ h₂ v
  rw [← he,hv] at hb
  exact hb

lemma uvShell_diagonal_bound (α L₁ L₂ : ℝ) (hα : 0 ≤ α) (h₁ : 0 < L₁) (h₂ : 0 < L₂)
    (u : FreeFormDomain) :
    ‖uvFieldForm (uvShellCoefficient α L₁ L₂ hα h₁ h₂) u u‖ ≤
      2*Real.sqrt |coefficientDTail α L₁-coefficientDTail α L₂| * ‖u‖^2 := by
  obtain ⟨cs,hcs,ht⟩ := smoothFiniteFormCore_sequence u
  have hl := ((uvFieldForm_diagonal_continuous (uvShellCoefficient α L₁ L₂ hα h₁ h₂)).tendsto u).comp ht
  have hr := (ht.norm.pow 2).const_mul (2*Real.sqrt |coefficientDTail α L₁-coefficientDTail α L₂|)
  exact le_of_tendsto_of_tendsto hl hr (Eventually.of_forall fun n =>
    uvShell_diagonal_core_bound α L₁ L₂ hα h₁ h₂ (cs n) (hcs n))

lemma uvShell_mixed_bound (α L₁ L₂ : ℝ) (hα : 0 ≤ α) (h₁ : 0 < L₁) (h₂ : 0 < L₂)
    (u w : FreeFormDomain) :
    ‖uvFieldForm (uvShellCoefficient α L₁ L₂ hα h₁ h₂) u w‖ ≤
      2*Real.sqrt |coefficientDTail α L₁-coefficientDTail α L₂| * ‖u‖*‖w‖ :=
  GW.Operators.hermitian_mixed_bound (uvFieldForm (uvShellCoefficient α L₁ L₂ hα h₁ h₂))
    (uvFieldForm_hermitian _) (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (Real.sqrt_nonneg |coefficientDTail α L₁-coefficientDTail α L₂|))
    (uvShell_diagonal_bound α L₁ L₂ hα h₁ h₂) u w

/- Source argument component Public02. -/
lemma uvFieldForm_sub (f g : OneBoson) (u w : FreeFormDomain) :
    uvFieldForm (f-g) u w = uvFieldForm f u w-uvFieldForm g u w := by
  change ⟪freeFormDomainInclusion u,grossFormFieldMap (f-g) (grossFormRootMap w)⟫_ℂ =
    ⟪freeFormDomainInclusion u,grossFormFieldMap f (grossFormRootMap w)⟫_ℂ-
      ⟪freeFormDomainInclusion u,grossFormFieldMap g (grossFormRootMap w)⟫_ℂ
  rw [grossFormFieldMap_sub,inner_sub_right]

def uvCutoffForm (α L : ℝ) (hα : 0 ≤ α) (hL : 0 < L) : GW.Operators.AlgebraicForm FreeFormDomain :=
  uvFieldForm (cutoffL2 α L hα hL)

lemma main_uv_form_bound (α L₁ L₂ : ℝ) (hα : 0 ≤ α) (h₁ : 0 < L₁) (h₂ : 0 < L₂)
    (u w : FreeFormDomain) :
    ‖uvCutoffForm α L₁ hα h₁ u w-uvCutoffForm α L₂ hα h₂ u w‖ ≤
      2*Real.sqrt |coefficientDTail α L₁-coefficientDTail α L₂| * ‖u‖*‖w‖ := by
  have h := uvShell_mixed_bound α L₁ L₂ hα h₁ h₂ u w
  change ‖uvFieldForm (cutoffL2 α L₁ hα h₁-cutoffL2 α L₂ hα h₂) u w‖ ≤ _ at h
  rw [uvFieldForm_sub] at h
  exact h

lemma uvFieldForm_original (f : OneBoson) (u w : FreeFormDomain) :
    ∃ a : (generalizedField (phaseMultiplicationKernel f)).domain,
      a.val = freeFormDomainInclusion w ∧
      uvFieldForm f u w = ⟪freeFormDomainInclusion u,generalizedField (phaseMultiplicationKernel f) a⟫_ℂ := by
  obtain ⟨a,ha,hout⟩ := (generalizedField (phaseMultiplicationKernel f)).mem_graph_iff.mp (uvFieldLinear_graph f w)
  dsimp only [Prod.fst,Prod.snd] at ha hout
  refine ⟨a,ha,?_⟩
  exact congrArg (fun z : Physical => ⟪freeFormDomainInclusion u,z⟫_ℂ) hout.symm

lemma main_uv_form_original (α L₁ L₂ : ℝ) (hα : 0 ≤ α) (h₁ : 0 < L₁) (h₂ : 0 < L₂)
    (u w : FreeFormDomain) :
    ∃ a₁ : (generalizedField (grossCutoffKernel α L₁ hα h₁)).domain,
      a₁.val = freeFormDomainInclusion w ∧
    ∃ a₂ : (generalizedField (grossCutoffKernel α L₂ hα h₂)).domain,
      a₂.val = freeFormDomainInclusion w ∧
      ‖⟪freeFormDomainInclusion u,generalizedField (grossCutoffKernel α L₁ hα h₁) a₁⟫_ℂ-
        ⟪freeFormDomainInclusion u,generalizedField (grossCutoffKernel α L₂ hα h₂) a₂⟫_ℂ‖ ≤
      2*Real.sqrt |coefficientDTail α L₁-coefficientDTail α L₂| * ‖u‖*‖w‖ := by
  obtain ⟨a₁,ha₁,hv₁⟩ := uvFieldForm_original (cutoffL2 α L₁ hα h₁) u w
  obtain ⟨a₂,ha₂,hv₂⟩ := uvFieldForm_original (cutoffL2 α L₂ hα h₂) u w
  refine ⟨a₁,ha₁,a₂,ha₂,?_⟩
  have h := main_uv_form_bound α L₁ L₂ hα h₁ h₂ u w
  change ‖uvFieldForm (cutoffL2 α L₁ hα h₁) u w-uvFieldForm (cutoffL2 α L₂ hα h₂) u w‖ ≤ _ at h
  rw [hv₁,hv₂] at h
  exact h

/- Source argument component Bounded01. -/
lemma uvFieldForm_physical_bound (f : OneBoson) (u w : FreeFormDomain) :
    ‖uvFieldForm f u w‖ ≤ 2*‖f‖*‖freeFormDomainInclusion u‖*‖grossFormRootMap w‖ := by
  have h := (norm_inner_le_norm (𝕜 := ℂ) (freeFormDomainInclusion u)
    (grossFormFieldMap f (grossFormRootMap w))).trans
    (mul_le_mul_of_nonneg_left (grossFormFieldMap_bound f (grossFormRootMap w)) (norm_nonneg _))
  exact h.trans_eq (by ring)

lemma uvFieldForm_bound (f : OneBoson) (u w : FreeFormDomain) :
    ‖uvFieldForm f u w‖ ≤ 2*‖f‖*‖u‖*‖w‖ :=
  (uvFieldForm_physical_bound f u w).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left (freeFormDomain_embedding u) (by positivity))
      (grossFormRootMap_norm w) (norm_nonneg _) (by positivity))

def uvFieldBoundedForm (f : OneBoson) : BoundedForm FreeFormDomain :=
  GW.Operators.boundedAlgebraicForm (uvFieldForm f) (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (norm_nonneg f))
    (uvFieldForm_bound f)

lemma uvFieldBoundedForm_apply (f : OneBoson) (u w : FreeFormDomain) :
    uvFieldBoundedForm f u w = uvFieldForm f u w := rfl

def uvCutoffBoundedForm (α L : ℝ) (hα : 0 ≤ α) (hL : 0 < L) : BoundedForm FreeFormDomain :=
  uvFieldBoundedForm (cutoffL2 α L hα hL)

lemma uvCutoffBoundedForm_apply (α L : ℝ) (hα : 0 ≤ α) (hL : 0 < L) (u w : FreeFormDomain) :
    uvCutoffBoundedForm α L hα hL u w = uvCutoffForm α L hα hL u w := rfl

lemma main_uv_form_opNorm_bound (α L₁ L₂ : ℝ) (hα : 0 ≤ α) (h₁ : 0 < L₁) (h₂ : 0 < L₂) :
    ‖uvCutoffBoundedForm α L₁ hα h₁-uvCutoffBoundedForm α L₂ hα h₂‖ ≤
      2*Real.sqrt |coefficientDTail α L₁-coefficientDTail α L₂| := by
  apply (form_norm_le_iff _ (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (Real.sqrt_nonneg _))).mpr
  intro u w
  change ‖uvCutoffForm α L₁ hα h₁ u w-uvCutoffForm α L₂ hα h₂ u w‖ ≤ _
  exact main_uv_form_bound α L₁ L₂ hα h₁ h₂ u w

end GW.Gross
