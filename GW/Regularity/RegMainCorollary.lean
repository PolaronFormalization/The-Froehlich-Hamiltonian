module
public import GW.Regularity.RegPositive
public import GW.Gross.MainDomain
@[expose] public section

-- Compiled component Basics02
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
namespace GW.Regularity
open GW.Fock GW.Gross GW.Analysis GW.Model

/-- The actual real power of the nonnegative electron Laplacian multiplier. -/
def electronLaplacianPower (t : ℝ) : Physical →ₗ.[ℂ] Physical :=
  physicalSectorMultiplier (fun _ q => (‖q‖^2)^t)

lemma electronLaplacianPower_eq_radial (t : ℝ) : electronLaplacianPower t = electronRadialPower (2*t) := by
  unfold electronLaplacianPower electronRadialPower
  congr 1
  funext n q
  rw [Real.rpow_mul (norm_nonneg q),Real.rpow_two]

lemma electronLaplacianPower_one : electronLaplacianPower 1 = freeMomentumSquare := by
  simp only [electronLaplacianPower,Real.rpow_one,freeMomentumSquare]

lemma electronRadialPower_two : electronRadialPower 2 = freeMomentumSquare := by
  simp only [electronRadialPower,Real.rpow_two,freeMomentumSquare]

lemma regRadial_domain_mono (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    (electronRadialPower b).domain ≤ (electronRadialPower a).domain := by
  intro v hv
  have hplus : v ∈ (physicalSectorMultiplier (fun _ q => 1+‖q‖^b)).domain := by
    apply (physicalSectorMultiplier_domain _ v).mpr
    rw [sumWeightDomain_add_one]
    exact (physicalSectorMultiplier_domain _ v).mp hv
  exact (physicalSectorMultiplier_domination (fun _ q => ‖q‖^a) (fun _ q => 1+‖q‖^b)
    (fun _ => continuous_norm.measurable.pow_const _) zero_le_one (fun n q => by
      rw [abs_of_nonneg (Real.rpow_nonneg (norm_nonneg q) _),
        abs_of_nonneg (by positivity : 0 ≤ 1+‖q‖^b),one_mul]
      exact nonnegative_rpow_le_one_add (norm_nonneg q) ha hab) ⟨v,hplus⟩).choose

lemma regHamiltonian_domain (α : ℝ) (hα : 0 ≤ α) :
    (constructionHamiltonian α hα).domain =
      freeHamiltonian.domain.map
        (grossWeylCoefficient (GW.Gross.grossDressingCoefficient α (standardGrossCutoff α) hα
          (dressed_standard_cutoff_pos α (standardGrossCutoff α) hα le_rfl))).toLinearMap := by
  have h := domainHamiltonian_domain α (standardGrossCutoff α) hα
    (dressed_standard_cutoff_pos α (standardGrossCutoff α) hα le_rfl) le_rfl
  simpa only [domainGrossUnitary,LinearIsometryEquiv.symm_symm] using h

lemma regHamiltonian_number (α : ℝ) (hα : 0 ≤ α) :
    (constructionHamiltonian α hα).domain ≤ physicalNumberOperator.domain := by
  rw [regHamiltonian_domain]
  exact le_trans (reg_positive α (standardGrossCutoff α) 1 hα
    (dressed_standard_cutoff_pos α (standardGrossCutoff α) hα le_rfl) le_rfl (by norm_num)).1 inf_le_right

lemma regHamiltonian_radial (α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) (hcrit : s < 3/2) :
    (constructionHamiltonian α hα).domain ≤ (electronRadialPower s).domain := by
  by_cases hsmall : s ≤ 1
  · have h1 : (constructionHamiltonian α hα).domain ≤ (electronRadialPower 1).domain := by
      rw [regHamiltonian_domain]
      exact le_trans (reg_positive α (standardGrossCutoff α) 1 hα
        (dressed_standard_cutoff_pos α (standardGrossCutoff α) hα le_rfl) le_rfl (by norm_num)).1 inf_le_left
    exact h1.trans (regRadial_domain_mono s 1 hs hsmall)
  · rw [regHamiltonian_domain]
    exact le_trans (reg_positive α (standardGrossCutoff α) s hα
      (dressed_standard_cutoff_pos α (standardGrossCutoff α) hα le_rfl) (le_of_not_ge hsmall) hcrit).1 inf_le_left

lemma regHamiltonian_critical (α : ℝ) (hα : 0 < α) :
    (constructionHamiltonian α hα.le).domain ⊓ (electronRadialPower (3/2)).domain = ⊥ := by
  rw [regHamiltonian_domain]
  exact reg_negative α (standardGrossCutoff α) hα
    (dressed_standard_cutoff_pos α (standardGrossCutoff α) hα.le le_rfl)

lemma regHamiltonian_higher (α s : ℝ) (hα : 0 < α) (hs : 3/2 ≤ s) :
    (constructionHamiltonian α hα.le).domain ⊓ (electronRadialPower s).domain = ⊥ := by
  apply le_antisymm _ bot_le
  calc
    _ ≤ (constructionHamiltonian α hα.le).domain ⊓ (electronRadialPower (3/2)).domain :=
      inf_le_inf_left _ (regRadial_domain_mono (3/2) s (by norm_num) hs)
    _ = ⊥ := regHamiltonian_critical α hα

end GW.Regularity

-- Compiled component Main03
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
namespace GW.Regularity
open GW.Fock GW.Gross GW.Analysis GW.Model

lemma regHamiltonian_free_disjoint (α : ℝ) (hα : 0 < α) :
    (constructionHamiltonian α hα.le).domain ⊓ freeHamiltonian.domain = ⊥ := by
  apply le_antisymm _ bot_le
  calc
    _ ≤ (constructionHamiltonian α hα.le).domain ⊓ (electronRadialPower 2).domain :=
      inf_le_inf_left _ (fun v hv => by
        rw [electronRadialPower_two]
        exact freeHamiltonian_momentum_mem ⟨v,hv⟩)
    _ = ⊥ := regHamiltonian_higher α 2 hα (by norm_num)

lemma regHamiltonian_zero_critical :
    (constructionHamiltonian 0 le_rfl).domain ⊓ (electronRadialPower (3/2)).domain = freeHamiltonian.domain := by
  rw [constructionHamiltonian_zero]
  apply inf_eq_left.mpr
  intro ψ hψ
  let u := commutatorSourceGraphInput (⟨ψ,hψ⟩ : freeHamiltonian.domain)
  obtain ⟨hp,hb⟩ := regFree_radial_mem_bound (3/2) (by norm_num) (by norm_num) u
  rw [commutatorSourceGraphInput_value] at hp
  exact hp

lemma regZero_power_identities :
    electronRadialPower 0 = (LinearMap.id : Physical →ₗ[ℂ] Physical).toPMap ⊤ ∧
    electronLaplacianPower 0 = (LinearMap.id : Physical →ₗ[ℂ] Physical).toPMap ⊤ := by
  refine ⟨radialPower_zero,?_⟩
  rw [electronLaplacianPower_eq_radial,mul_zero]
  exact radialPower_zero

/-- Sharp regularity for the same original Fröhlich Hamiltonian, with all real exponents. -/
theorem reg_main_corollary (α : ℝ) (hα : 0 ≤ α) :
    ((constructionHamiltonian α hα).domain ≤ physicalNumberOperator.domain ⊓
      (⨅ (s : ℝ) (_ : 0 ≤ s) (_ : s < 3/2), (electronRadialPower s).domain : Submodule ℂ Physical)) ∧
    ((constructionHamiltonian α hα).domain ≤ physicalNumberOperator.domain ⊓
      (⨅ (t : ℝ) (_ : 0 ≤ t) (_ : t < 3/4), (electronLaplacianPower t).domain : Submodule ℂ Physical)) ∧
    (0 < α →
      ((constructionHamiltonian α hα).domain ⊓ (electronRadialPower (3/2)).domain = ⊥) ∧
      ((constructionHamiltonian α hα).domain ⊓ (electronLaplacianPower (3/4)).domain = ⊥) ∧
      ((constructionHamiltonian α hα).domain ⊓ freeMomentumSquare.domain = ⊥) ∧
      ((constructionHamiltonian α hα).domain ⊓ freeHamiltonian.domain = ⊥) ∧
      (∀ s : ℝ, 3/2 ≤ s → (constructionHamiltonian α hα).domain ⊓ (electronRadialPower s).domain = ⊥)) ∧
    (constructionHamiltonian 0 le_rfl = freeHamiltonian) ∧
    ((constructionHamiltonian 0 le_rfl).domain = freeHamiltonian.domain) ∧
    ((constructionHamiltonian 0 le_rfl).domain = freeMomentumSquare.domain ⊓ physicalNumberOperator.domain) ∧
    (electronRadialPower 0 = (LinearMap.id : Physical →ₗ[ℂ] Physical).toPMap ⊤) ∧
    (electronLaplacianPower 0 = (LinearMap.id : Physical →ₗ[ℂ] Physical).toPMap ⊤) := by
  refine ⟨?_,?_,?_,constructionHamiltonian_zero,?_,?_,regZero_power_identities⟩
  · intro ψ hψ
    refine ⟨regHamiltonian_number α hα hψ,?_⟩
    refine (Submodule.mem_iInf (fun s : ℝ => ⨅ (_ : 0 ≤ s) (_ : s < 3/2), (electronRadialPower s).domain)).mpr ?_
    intro s
    refine (Submodule.mem_iInf (fun _ : 0 ≤ s => ⨅ (_ : s < 3/2), (electronRadialPower s).domain)).mpr ?_
    intro hs
    refine (Submodule.mem_iInf (fun _ : s < 3/2 => (electronRadialPower s).domain)).mpr ?_
    intro hc
    exact regHamiltonian_radial α s hα hs hc hψ
  · intro ψ hψ
    refine ⟨regHamiltonian_number α hα hψ,?_⟩
    refine (Submodule.mem_iInf (fun t : ℝ => ⨅ (_ : 0 ≤ t) (_ : t < 3/4), (electronLaplacianPower t).domain)).mpr ?_
    intro t
    refine (Submodule.mem_iInf (fun _ : 0 ≤ t => ⨅ (_ : t < 3/4), (electronLaplacianPower t).domain)).mpr ?_
    intro ht
    refine (Submodule.mem_iInf (fun _ : t < 3/4 => (electronLaplacianPower t).domain)).mpr ?_
    intro hc
    rw [electronLaplacianPower_eq_radial]
    exact regHamiltonian_radial α (2*t) hα (by positivity) (by linarith) hψ
  · intro hp
    have h2 := regHamiltonian_higher α 2 hp (by norm_num)
    rw [electronRadialPower_two] at h2
    refine ⟨regHamiltonian_critical α hp,?_,h2,
      regHamiltonian_free_disjoint α hp,fun s hs => regHamiltonian_higher α s hp hs⟩
    rw [electronLaplacianPower_eq_radial,show (2:ℝ)*(3/4)=3/2 by norm_num]
    exact regHamiltonian_critical α hp
  · exact congrArg (fun A : Physical →ₗ.[ℂ] Physical => A.domain) constructionHamiltonian_zero
  · exact (congrArg (fun A : Physical →ₗ.[ℂ] Physical => A.domain) constructionHamiltonian_zero).trans freeHamiltonian_domain_intersection

end GW.Regularity
