module
public import GW.Gross.MainUvForm
public import GW.Model.ModelCutoffWitness

/-! Source main:uniform-form-bound, manuscript5870–5913.
Sharp bare-number annihilation expectation, actual cutoff shell split and Young,
exact free energy, source constants and form inequalities on original Q. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Gross
open GW.Model GW.Fock GW.Analysis

/- Source argument component Root01. -/
def uniformRootInput (u : FreeFormDomain) : (physicalNumberPower (1/2)).domain :=
  ⟨(show freeFormOperator.domain from u).val,
    (congrArg (fun T : Physical →ₗ.[ℂ] Physical => (show freeFormOperator.domain from u).val ∈ T.domain)
      freeRootNumber_eq).mp (freeForm_rootNumber_mem u)⟩

lemma uniformRootInput_val (u : FreeFormDomain) : (uniformRootInput u).val = freeFormDomainInclusion u :=
  (freeFormDomainInclusion_apply u).symm

lemma uniformRootInput_action (u : FreeFormDomain) :
    physicalNumberPower (1/2) (uniformRootInput u) =
      freeRootNumber ⟨(show freeFormOperator.domain from u).val,freeForm_rootNumber_mem u⟩ := by
  let v := freeRootNumber ⟨(show freeFormOperator.domain from u).val,freeForm_rootNumber_mem u⟩
  have hg : ((show freeFormOperator.domain from u).val,v) ∈ (physicalNumberPower (1/2)).graph :=
    (congrArg (fun T : Physical →ₗ.[ℂ] Physical => ((show freeFormOperator.domain from u).val,v) ∈ T.graph)
      freeRootNumber_eq).mp (freeRootNumber.mem_graph ⟨_,freeForm_rootNumber_mem u⟩)
  exact (physicalNumberPower (1/2)).mem_graph_snd_inj
    ((physicalNumberPower (1/2)).mem_graph (uniformRootInput u)) hg rfl

def uniformFreeEnergy (u : FreeFormDomain) : ℝ :=
  ‖freeMomentumModulus ⟨(show freeFormOperator.domain from u).val,freeForm_momentum_mem u⟩‖^2+
    ‖physicalNumberPower (1/2) (uniformRootInput u)‖^2

lemma uniformFreeEnergy_nonneg (u : FreeFormDomain) : 0 ≤ uniformFreeEnergy u := add_nonneg (sq_nonneg _) (sq_nonneg _)

lemma uniformFreeEnergy_root_le (u : FreeFormDomain) :
    ‖physicalNumberPower (1/2) (uniformRootInput u)‖^2 ≤ uniformFreeEnergy u := le_add_of_nonneg_left (sq_nonneg _)

lemma uniformFreeEnergy_norm (u : FreeFormDomain) : ‖u‖^2 = uniformFreeEnergy u+‖freeFormDomainInclusion u‖^2 := by
  have h := freeForm_norm_identity u
  rw [freeFormDomainInclusion_apply,uniformFreeEnergy,uniformRootInput_action]
  exact h.trans (by ring)

lemma uniformAnnihilator_bound (f : OneBoson) (u : FreeFormDomain) :
    ‖commutatorPhaseAnnihilatorMap f (grossFormRootMap u)‖ ≤
      ‖f‖*‖physicalNumberPower (1/2) (uniformRootInput u)‖ := by
  let F := phaseMultiplicationKernel f
  let y : (generalizedAnnihilation F).domain :=
    ⟨(uniformRootInput u).val,generalizedAnnihilation_mem_root F (uniformRootInput u)⟩
  have hy : y.val = freeFormDomainInclusion u := uniformRootInput_val u
  have hg := (generalizedAnnihilation F).mem_graph y
  rw [hy] at hg
  have hA := commutatorPhaseAnnihilatorMap_graph f (grossFormRootMap u)
  rw [grossFormRootMap_value] at hA
  have he := (generalizedAnnihilation F).mem_graph_snd_inj hA hg rfl
  rw [he]
  have hb := generalizedAnnihilation_root_norm F (uniformRootInput u)
  simpa only [phaseMultiplicationKernel_norm,F] using hb

lemma uniformField_diagonal_bound (f : OneBoson) (u : FreeFormDomain) :
    ‖uvFieldForm f u u‖ ≤ 2*‖f‖*‖freeFormDomainInclusion u‖*‖physicalNumberPower (1/2) (uniformRootInput u)‖ := by
  have hp := uvPhase_field_diagonal f (grossFormRootMap u)
  rw [grossFormRootMap_value] at hp
  change ‖⟪freeFormDomainInclusion u,grossFormFieldMap f (grossFormRootMap u)⟫_ℂ‖ ≤ _
  rw [hp]
  have hz := (norm_inner_le_norm (𝕜 := ℂ) (freeFormDomainInclusion u)
    (commutatorPhaseAnnihilatorMap f (grossFormRootMap u))).trans
    (mul_le_mul_of_nonneg_left (uniformAnnihilator_bound f u) (norm_nonneg _))
  have hs := norm_add_le ⟪freeFormDomainInclusion u,commutatorPhaseAnnihilatorMap f (grossFormRootMap u)⟫_ℂ
    (star ⟪freeFormDomainInclusion u,commutatorPhaseAnnihilatorMap f (grossFormRootMap u)⟫_ℂ)
  rw [norm_star] at hs
  exact hs.trans ((add_le_add hz hz).trans_eq (by ring))

/- Source argument component Cutoffs02. -/
lemma uniformCutoff_norm_mono (α r R : ℝ) (hα : 0 ≤ α) (hr : 0 < r) (hR : 0 < R) (hrR : r ≤ R) :
    ‖cutoffL2 α r hα hr‖ ≤ ‖cutoffL2 α R hα hR‖ := by
  calc
    _ ≤ (1:ℝ)*‖cutoffL2 α R hα hR‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [cutoffL2_ae α r hα hr,cutoffL2_ae α R hα hR] with k h₁ h₂
      rw [h₁,h₂,one_mul]
      by_cases hk : ‖k‖ ≤ r
      · rw [GW.Model.cutoff,if_pos hk,GW.Model.cutoff,if_pos (hk.trans hrR)]
      · rw [GW.Model.cutoff,if_neg hk,Complex.ofReal_zero,norm_zero]
        exact norm_nonneg _
    _ = _ := one_mul _

lemma uniformYoung (g a r ε : ℝ) (hε : 0 < ε) :
    2*g*a*r ≤ (ε/2)*r^2+(2*g^2/ε)*a^2 := by
  apply (mul_le_mul_iff_right₀ (show (0:ℝ) < 2*ε by positivity)).mp
  have he : (2*ε)*((ε/2)*r^2+(2*g^2/ε)*a^2) = ε^2*r^2+4*g^2*a^2 := by
    field_simp [ne_of_gt hε]
    <;> ring
  rw [he]
  nlinarith [sq_nonneg (ε*r-2*g*a)]

lemma uniformShell_bound (α K L : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (hL : 0 < L)
    (u : FreeFormDomain) :
    ‖uvCutoffForm α L hα hL u u‖ ≤
      2*Real.sqrt (coefficientDTail α K)*‖u‖^2+
        2*‖cutoffL2 α K hα hK‖*‖freeFormDomainInclusion u‖*‖physicalNumberPower (1/2) (uniformRootInput u)‖ := by
  by_cases hLK : L ≤ K
  · have hl := uniformField_diagonal_bound (cutoffL2 α L hα hL) u
    have hc := uniformCutoff_norm_mono α L K hα hL hK hLK
    have hlow : ‖uvCutoffForm α L hα hL u u‖ ≤
        2*‖cutoffL2 α K hα hK‖*‖freeFormDomainInclusion u‖*‖physicalNumberPower (1/2) (uniformRootInput u)‖ := by
      apply hl.trans
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hc (by norm_num)) (norm_nonneg _)) (norm_nonneg _)
    exact hlow.trans (le_add_of_nonneg_left (mul_nonneg
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (sq_nonneg _)))
  · have hKL : K ≤ L := (lt_of_not_ge hLK).le
    have hD : |coefficientDTail α L-coefficientDTail α K| ≤ coefficientDTail α K := by
      rw [abs_of_nonpos (sub_nonpos.mpr (coefficientDTail_antitone α hα hK hKL))]
      have hn : 0 ≤ coefficientDTail α L := ENNReal.toReal_nonneg
      linarith
    have hd := main_uv_form_bound α L K hα hL hK u u
    have hshell : ‖uvCutoffForm α L hα hL u u-uvCutoffForm α K hα hK u u‖ ≤
        2*Real.sqrt (coefficientDTail α K)*‖u‖^2 := by
      apply hd.trans
      have hs := Real.sqrt_le_sqrt hD
      nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ) ≤ 2)) (sq_nonneg ‖u‖)]
    have hl := uniformField_diagonal_bound (cutoffL2 α K hα hK) u
    calc
      _ = ‖(uvCutoffForm α L hα hL u u-uvCutoffForm α K hα hK u u)+uvCutoffForm α K hα hK u u‖ :=
        congrArg norm (sub_add_cancel _ _).symm
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add hshell hl)

/- Source argument component Constant02. -/
lemma uniformFormCutoff_pos (α ε : ℝ) (hα : 0 ≤ α) : 0 < formCutoffWitness α ε :=
  zero_lt_one.trans_le (formCutoffWitness_ge_one α ε hα)

def uniformFormConstantNorm (α ε : ℝ) (hα : 0 ≤ α) : ℝ :=
  ε/2+2*‖cutoffL2 α (formCutoffWitness α ε) hα (uniformFormCutoff_pos α ε hα)‖^2/ε

def uniformFormConstant (α ε : ℝ) : ℝ := ε/2+14*unitBallVolume*α*formCutoffWitness α ε/ε

lemma uniformFormConstantNorm_nonneg (α ε : ℝ) (hα : 0 ≤ α) (hε : 0 < ε) :
    0 ≤ uniformFormConstantNorm α ε hα := by unfold uniformFormConstantNorm; positivity

lemma uniformFormConstantNorm_le (α ε : ℝ) (hα : 0 ≤ α) (hε : 0 < ε) :
    uniformFormConstantNorm α ε hα ≤ uniformFormConstant α ε := by
  have hb := cutoffL2_norm_sq α (formCutoffWitness α ε) hα (uniformFormCutoff_pos α ε hα)
  unfold uniformFormConstantNorm uniformFormConstant
  apply add_le_add le_rfl
  exact div_le_div_of_nonneg_right (by nlinarith [hb]) hε.le

lemma uniformFormConstant_nonneg (α ε : ℝ) (hα : 0 ≤ α) (hε : 0 < ε) :
    0 ≤ uniformFormConstant α ε := (uniformFormConstantNorm_nonneg α ε hα hε).trans (uniformFormConstantNorm_le α ε hα hε)

lemma uniform_form_bound_norm (α ε L : ℝ) (hα : 0 ≤ α) (hε : 0 < ε) (hL : 0 < L)
    (u : FreeFormDomain) :
    ‖uvCutoffForm α L hα hL u u‖ ≤ ε*uniformFreeEnergy u+uniformFormConstantNorm α ε hα*‖freeFormDomainInclusion u‖^2 := by
  let K := formCutoffWitness α ε
  let g := ‖cutoffL2 α K hα (uniformFormCutoff_pos α ε hα)‖
  let U := ‖freeFormDomainInclusion u‖
  let R := ‖physicalNumberPower (1/2) (uniformRootInput u)‖
  have hs := uniformShell_bound α K L hα (uniformFormCutoff_pos α ε hα) hL u
  have hK := formCutoffWitness_bound α ε K hα hε le_rfl
  have hs' := mul_le_mul_of_nonneg_right hK (sq_nonneg ‖u‖)
  have hy := uniformYoung g U R ε hε
  have hR : R^2 ≤ uniformFreeEnergy u := uniformFreeEnergy_root_le u
  have hE := mul_le_mul_of_nonneg_left hR (show 0 ≤ ε/2 by positivity)
  have hQ : ‖u‖^2 = uniformFreeEnergy u+U^2 := uniformFreeEnergy_norm u
  apply hs.trans
  change 2*Real.sqrt (coefficientDTail α K)*‖u‖^2+2*g*U*R ≤ _
  have ht := add_le_add hs' hy
  unfold uniformFormConstantNorm
  change _ ≤ ε*uniformFreeEnergy u+(ε/2+2*g^2/ε)*U^2
  rw [hQ] at ht
  nlinarith [ht,hE]

lemma main_uniform_form_bound (α ε L : ℝ) (hα : 0 ≤ α) (hε : 0 < ε) (hL : 0 < L)
    (u : FreeFormDomain) :
    ‖uvCutoffForm α L hα hL u u‖ ≤ ε*uniformFreeEnergy u+uniformFormConstant α ε*‖freeFormDomainInclusion u‖^2 :=
  (uniform_form_bound_norm α ε L hα hε hL u).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right (uniformFormConstantNorm_le α ε hα hε) (sq_nonneg _)))

/- Source argument component Base03. -/
def uniformBaseForm : GW.Operators.AlgebraicForm FreeFormDomain :=
  innerₛₗ ℂ-GW.Operators.embeddingForm freeFormDomainInclusion

lemma uniformBaseForm_apply (u w : FreeFormDomain) :
    uniformBaseForm u w = ⟪u,w⟫_ℂ-⟪freeFormDomainInclusion u,freeFormDomainInclusion w⟫_ℂ := rfl

lemma uniformBaseForm_hermitian (u w : FreeFormDomain) : uniformBaseForm u w = star (uniformBaseForm w u) := by
  simp only [uniformBaseForm_apply,star_sub,Complex.star_def,inner_conj_symm]

lemma uniformBaseForm_continuous : Continuous (fun p : FreeFormDomain × FreeFormDomain => uniformBaseForm p.1 p.2) :=
  (continuous_fst.inner (𝕜 := ℂ) continuous_snd).sub
    ((freeFormDomainInclusion.continuous.comp continuous_fst).inner (𝕜 := ℂ)
      (freeFormDomainInclusion.continuous.comp continuous_snd))

lemma uniformBaseForm_energy (u : FreeFormDomain) : (uniformBaseForm u u).re = uniformFreeEnergy u := by
  have hQ := uniformFreeEnergy_norm u
  rw [uniformBaseForm_apply,Complex.sub_re]
  have h₁ : ‖u‖^2 = (⟪u,u⟫_ℂ).re := norm_sq_eq_re_inner (𝕜 := ℂ) _
  have h₂ : ‖freeFormDomainInclusion u‖^2 = (⟪freeFormDomainInclusion u,freeFormDomainInclusion u⟫_ℂ).re := norm_sq_eq_re_inner (𝕜 := ℂ) _
  linarith

lemma uniformBaseForm_nonneg (u : FreeFormDomain) : 0 ≤ (uniformBaseForm u u).re := by
  rw [uniformBaseForm_energy]
  exact uniformFreeEnergy_nonneg u

lemma uniformBaseForm_norm (u : FreeFormDomain) : ‖u‖^2 = (uniformBaseForm u u).re+‖freeFormDomainInclusion u‖^2 := by
  rw [uniformBaseForm_energy]
  exact uniformFreeEnergy_norm u

lemma uniformCanonicalEmbedding (u : FreeFormDomain) :
    GW.Operators.canonicalEmbedding freeNonnegativeData (freeCanonicalFormEquiv.symm u) = freeFormDomainInclusion u := by
  have h := freeCanonicalFormEquiv_embedding (freeCanonicalFormEquiv.symm u)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h.symm

lemma uniformBaseForm_canonical (u w : FreeFormDomain) :
    uniformBaseForm u w = GW.Operators.canonicalForm freeNonnegativeData (freeCanonicalFormEquiv.symm u) (freeCanonicalFormEquiv.symm w) := by
  rw [uniformBaseForm_apply,GW.Operators.canonicalForm_apply,freeCanonicalFormEquiv.symm.inner_map_map,
    uniformCanonicalEmbedding,uniformCanonicalEmbedding]

/- Source argument component Public01. -/
lemma main_uniform_form_original (α ε L : ℝ) (hα : 0 ≤ α) (hε : 0 < ε) (hL : 0 < L)
    (u : FreeFormDomain) :
    ∃ a : (generalizedField (grossCutoffKernel α L hα hL)).domain,
      a.val = freeFormDomainInclusion u ∧
      ‖⟪freeFormDomainInclusion u,generalizedField (grossCutoffKernel α L hα hL) a⟫_ℂ‖ ≤
        ε*uniformFreeEnergy u+uniformFormConstant α ε*‖freeFormDomainInclusion u‖^2 := by
  obtain ⟨a,ha,hv⟩ := uvFieldForm_original (cutoffL2 α L hα hL) u u
  refine ⟨a,ha,?_⟩
  have h := main_uniform_form_bound α ε L hα hε hL u
  change ‖uvFieldForm (cutoffL2 α L hα hL) u u‖ ≤ _ at h
  rw [hv] at h
  exact h

def uniformCutoffTotalForm (α L : ℝ) (hα : 0 ≤ α) (hL : 0 < L) : GW.Operators.AlgebraicForm FreeFormDomain :=
  uniformBaseForm+uvCutoffForm α L hα hL

lemma uniformCutoffTotalForm_apply (α L : ℝ) (hα : 0 ≤ α) (hL : 0 < L) (u w : FreeFormDomain) :
    uniformCutoffTotalForm α L hα hL u w = uniformBaseForm u w+uvCutoffForm α L hα hL u w := rfl

lemma main_uniform_form_inequalities (α ε L : ℝ) (hα : 0 ≤ α) (hε : 0 < ε) (hL : 0 < L)
    (u : FreeFormDomain) :
    (1-ε)*(uniformBaseForm u u).re-uniformFormConstant α ε*‖freeFormDomainInclusion u‖^2 ≤
        (uniformCutoffTotalForm α L hα hL u u).re ∧
    (uniformCutoffTotalForm α L hα hL u u).re ≤
      (1+ε)*(uniformBaseForm u u).re+uniformFormConstant α ε*‖freeFormDomainInclusion u‖^2 := by
  have h := main_uniform_form_bound α ε L hα hε hL u
  have ha := (Complex.abs_re_le_norm (uvCutoffForm α L hα hL u u)).trans h
  obtain ⟨hl,hu⟩ := abs_le.mp ha
  rw [uniformCutoffTotalForm_apply,Complex.add_re,uniformBaseForm_energy]
  constructor <;> nlinarith

lemma main_uniform_form_exists (α ε : ℝ) (hα : 0 ≤ α) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ) (hL : 0 < L) (u : FreeFormDomain),
      ‖uvCutoffForm α L hα hL u u‖ ≤ ε*uniformFreeEnergy u+C*‖freeFormDomainInclusion u‖^2 :=
  ⟨uniformFormConstant α ε,uniformFormConstant_nonneg α ε hα hε,
    fun L hL u => main_uniform_form_bound α ε L hα hε hL u⟩

end GW.Gross
