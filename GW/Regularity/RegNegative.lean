module
public import GW.Regularity.RegSingularField
public import GW.Regularity.RegMomentEquivalence
public import GW.Regularity.RegInvariance
@[expose] public section

-- Compiled component Coefficients01
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
namespace GW.Regularity
open GW.Fock GW.Gross GW.Analysis GW.Model

def regPhysicalCoefficients (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (j : Fin 3) : OneBoson :=
  weylMomentumCoefficient (GW.Gross.grossDressingCoefficient α K hα hK) j (grossForm_momentum_memLp α K hα hK j)

lemma regCoefficient_raw_eq_b (α K : ℝ) (k : GW.Space) :
    GW.Regularity.grossDressingCoefficient α K k = GW.Model.b α K k := by
  by_cases hk : K < ‖k‖
  · rw [GW.Regularity.grossDressingCoefficient,GW.Model.b,if_pos hk,indicator_of_mem hk]
  · rw [GW.Regularity.grossDressingCoefficient,GW.Model.b,if_neg hk,indicator_of_notMem hk,neg_zero,zero_div]

lemma regPhysicalCoefficients_ae (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (j : Fin 3) :
    regPhysicalCoefficients α K hα hK j =ᵐ[(volume : Measure GW.Space)]
      fun k => (grossMomentumCoefficient α K j k : ℂ) := by
  filter_upwards [weylMomentumCoefficient_ae (GW.Gross.grossDressingCoefficient α K hα hK) j
    (grossForm_momentum_memLp α K hα hK j),GW.Gross.grossDressingCoefficient_ae α K hα hK]
    with k hm hb
  change regPhysicalCoefficients α K hα hK j k = (k j : ℂ)*GW.Gross.grossDressingCoefficient α K hα hK k at hm
  rw [hm,hb,grossMomentumCoefficient,regCoefficient_raw_eq_b,Complex.ofReal_mul]

lemma regPhysicalCoefficients_moment_mass (α K r : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    singularFieldMomentMass r (regPhysicalCoefficients α K hα hK) = grossMomentTail α K (1+r) := by
  rw [grossMomentTail_eq_component_sum α K (1+r) hK]
  unfold singularFieldMomentMass grossMomentumCoefficientMoment
  apply Finset.sum_congr rfl
  intro j _
  apply lintegral_congr_ae
  filter_upwards [regPhysicalCoefficients_ae α K hα hK j] with k hk
  rw [singularFieldDensity_source,hk,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  congr 2
  ring

lemma regPhysicalCoefficients_critical_mass (α K : ℝ) (hα : 0 < α) (hK : 0 < K) :
    singularFieldMomentMass (1/2) (regPhysicalCoefficients α K hα.le hK) = ∞ := by
  rw [regPhysicalCoefficients_moment_mass,show (1:ℝ)+1/2=3/2 by norm_num]
  exact grossMomentTail_critical α K hα

end GW.Regularity

-- Compiled component Domains02
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
namespace GW.Regularity
open GW.Fock GW.Gross GW.Analysis GW.Model

lemma regFree_radial_mem_bound (s : ℝ) (hs : 0 ≤ s) (hs2 : s ≤ 2) (u : FreeGraphDomain) :
    ∃ hm : freeGraphDomainInclusion u ∈ (electronRadialPower s).domain,
      ‖electronRadialPower s ⟨freeGraphDomainInclusion u,hm⟩‖ ≤ ‖u‖ := by
  have h := physicalSectorMultiplier_domination (fun _ q => ‖q‖^s) freeGraphWeight
    (fun _ => continuous_norm.measurable.pow_const s) zero_le_one (fun n q => by
      rw [abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
        abs_of_nonneg (zero_le_one.trans (freeGraphWeight_one n q)),one_mul]
      have hp := nonnegative_rpow_le_one_add (norm_nonneg q) hs hs2
      rw [Real.rpow_two] at hp
      exact hp.trans (by unfold freeGraphWeight freeEnergySymbol; nlinarith [Nat.cast_nonneg (α := ℝ) n]))
    (show freeGraphOperator.domain from u)
  obtain ⟨hm,hb⟩ := h
  have hi := freeGraphDomainInclusion_apply u
  have hm' : freeGraphDomainInclusion u ∈ (electronRadialPower s).domain := hi.symm ▸ hm
  refine ⟨hm',?_⟩
  rw [freeGraphDomain_norm]
  have he : (⟨freeGraphDomainInclusion u,hm'⟩ : (electronRadialPower s).domain) =
      ⟨(show freeGraphOperator.domain from u).val,hm⟩ := Subtype.ext hi
  rw [he]
  simpa only [electronRadialPower,freeGraphOperator,one_mul] using hb

lemma regFree_coordinate_radial_mem (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (u : FreeGraphDomain) (j : Fin 3)
    (hj : freeGraphDomainInclusion u ∈ (electronMomentumCoordinate j).domain) :
    electronMomentumCoordinate j ⟨freeGraphDomainInclusion u,hj⟩ ∈ (electronRadialPower r).domain := by
  obtain ⟨hm,hb⟩ := regFree_radial_mem_bound (1+r) (by linarith) (by linarith) u
  obtain ⟨hj',hp⟩ := radial_coordinate_forward r hr (freeGraphDomainInclusion u) hm j
  have he : (⟨freeGraphDomainInclusion u,hj'⟩ : (electronMomentumCoordinate j).domain) =
      ⟨freeGraphDomainInclusion u,hj⟩ := Subtype.ext rfl
  exact hp

lemma regNegative_transformed_coordinate (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (χ : Physical) (hp : χ ∈ (electronRadialPower (3/2)).domain) (hN : χ ∈ physicalNumberOperator.domain)
    (j : Fin 3) (hj : χ ∈ (electronMomentumCoordinate j).domain) :
    (GW.Gross.grossDressingCoefficient α K hα hK |> grossWeylCoefficient).symm
      (electronMomentumCoordinate j ⟨χ,hj⟩) ∈ (electronRadialPower (1/2)).domain := by
  obtain ⟨hj',hq⟩ := fractional_coordinate_transfer (3/2) (by norm_num) (by norm_num) χ hp hN j
  rw [show (3/2:ℝ)-1=1/2 by norm_num] at hq
  have he : (⟨χ,hj'⟩ : (electronMomentumCoordinate j).domain) = ⟨χ,hj⟩ := Subtype.ext rfl
  rw [he] at hq
  have hQ : electronMomentumCoordinate j ⟨χ,hj⟩ ∈ regGrossQsigma (1/2) := hq
  have hW : grossWeylSide false (GW.Gross.grossDressingCoefficient α K hα hK)
      (electronMomentumCoordinate j ⟨χ,hj⟩) ∈ regGrossQsigma (1/2) := by
    have hh := Set.mem_image_of_mem (grossWeylSide false (GW.Gross.grossDressingCoefficient α K hα hK)) hQ
    rw [main_gross_fractional_domain_image false α K hα hK (1/2) (by norm_num) (by norm_num)] at hh
    exact hh
  exact hW.1

end GW.Regularity

-- Compiled component Main01
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
namespace GW.Regularity
open GW.Fock GW.Gross GW.Analysis GW.Model

lemma regPhysical_momentum_identity (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (u : FreeGraphDomain) (j : Fin 3) :
    ∃ hp : freeGraphDomainInclusion u ∈ (electronMomentumCoordinate j).domain,
    ∃ hW : grossWeylCoefficient (GW.Gross.grossDressingCoefficient α K hα hK)
      (freeGraphDomainInclusion u) ∈ (electronMomentumCoordinate j).domain,
    (grossWeylCoefficient (GW.Gross.grossDressingCoefficient α K hα hK)).symm
      (electronMomentumCoordinate j ⟨grossWeylCoefficient (GW.Gross.grossDressingCoefficient α K hα hK)
        (freeGraphDomainInclusion u),hW⟩) =
      electronMomentumCoordinate j ⟨freeGraphDomainInclusion u,hp⟩-
        regularFieldGraphMap (regPhysicalCoefficients α K hα hK j) u := by
  have hf : freeGraphDomainInclusion u ∈ freeFormOperator.domain :=
    (freeGraphDomainInclusion_apply u).symm ▸ freeHamiltonian_mem_form (freeGraphH0Input u)
  let v : FreeFormDomain := ⟨freeGraphDomainInclusion u,hf⟩
  have hv : freeFormDomainInclusion v = freeGraphDomainInclusion u := freeFormDomainInclusion_apply v
  have h := main_gross_infinite_momentum α K hα hK v j
  rw [hv] at h
  obtain ⟨hp,a,ha,hW,he⟩ := h
  have hfield : generalizedField (phaseMultiplicationKernel (regPhysicalCoefficients α K hα hK j)) a =
      regularFieldGraphMap (regPhysicalCoefficients α K hα hK j) u :=
    (generalizedField (phaseMultiplicationKernel (regPhysicalCoefficients α K hα hK j))).mem_graph_snd_inj
      ((generalizedField (phaseMultiplicationKernel (regPhysicalCoefficients α K hα hK j))).mem_graph a)
      (regularFieldGraphMap_graph _ u) ha
  change electronMomentumCoordinate j _ =
    grossWeylCoefficient (GW.Gross.grossDressingCoefficient α K hα hK)
      (electronMomentumCoordinate j _-generalizedField (phaseMultiplicationKernel (regPhysicalCoefficients α K hα hK j)) a) at he
  rw [hfield] at he
  refine ⟨hp,hW,?_⟩
  have hh := congrArg (grossWeylCoefficient (GW.Gross.grossDressingCoefficient α K hα hK)).symm he
  simpa only [LinearIsometryEquiv.symm_apply_apply] using hh

lemma regNegative_free_zero (α K : ℝ) (hα : 0 < α) (hK : 0 < K)
    (u : FreeGraphDomain)
    (hχ : grossWeylCoefficient (GW.Gross.grossDressingCoefficient α K hα.le hK)
      (freeGraphDomainInclusion u) ∈ (electronRadialPower (3/2)).domain) :
    freeGraphDomainInclusion u = 0 := by
  apply reg_singular_field (1/2) (by norm_num) (by norm_num)
    (regPhysicalCoefficients α K hα.le hK) (regPhysicalCoefficients_critical_mass α K hα hK) u
  intro j
  obtain ⟨hp,hW,he⟩ := regPhysical_momentum_identity α K hα.le hK u j
  have hN := grossGraphWeyl_number_mem (GW.Gross.grossDressingCoefficient α K hα.le hK) u
  have ht := regNegative_transformed_coordinate α K hα.le hK _ hχ hN j hW
  have hpreg := regFree_coordinate_radial_mem (1/2) (by norm_num) (by norm_num) u j hp
  have hm := (electronRadialPower (1/2)).domain.sub_mem hpreg ht
  rw [he] at hm
  simpa only [sub_sub_cancel] using hm

end GW.Regularity

-- Compiled component Conclusion02
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
namespace GW.Regularity
open GW.Fock GW.Gross GW.Analysis GW.Model

/-- The source critical obstruction, for every positive coupling and cutoff. -/
theorem reg_negative (α K : ℝ) (hα : 0 < α) (hK : 0 < K) :
    freeHamiltonian.domain.map
      (grossWeylCoefficient (GW.Gross.grossDressingCoefficient α K hα.le hK)).toLinearMap ⊓
      (electronRadialPower (3/2)).domain = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro χ hχ
  obtain ⟨ψ,hψ,he⟩ := Submodule.mem_map.mp hχ.1
  let u := commutatorSourceGraphInput (⟨ψ,hψ⟩ : freeHamiltonian.domain)
  have hu : freeGraphDomainInclusion u = ψ := commutatorSourceGraphInput_value _
  have hcrit : grossWeylCoefficient (GW.Gross.grossDressingCoefficient α K hα.le hK)
      (freeGraphDomainInclusion u) ∈ (electronRadialPower (3/2)).domain := by
    rw [hu]
    exact he.symm ▸ hχ.2
  have hz := regNegative_free_zero α K hα hK u hcrit
  rw [hu] at hz
  change grossWeylCoefficient (GW.Gross.grossDressingCoefficient α K hα.le hK) ψ = χ at he
  rw [hz,map_zero] at he
  exact he.symm

end GW.Regularity
