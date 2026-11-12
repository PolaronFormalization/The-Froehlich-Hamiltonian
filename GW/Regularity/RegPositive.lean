module
public import GW.Regularity.RegNegative
@[expose] public section

-- Compiled component Coefficients03
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
namespace GW.Regularity
open GW.Fock GW.Gross GW.Analysis GW.Model

lemma regPhysicalCoefficients_subcritical_mass (α K s : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (hs : 1 ≤ s) (hcrit : s < 3/2) :
    singularFieldMomentMass (s-1) (regPhysicalCoefficients α K hα hK) < ∞ := by
  rw [regPhysicalCoefficients_moment_mass,show 1+(s-1)=s by ring]
  rcases eq_or_lt_of_le hα with he | hp
  · rw [← he,grossMomentTail_zero_coupling]
    exact ENNReal.zero_lt_top
  · exact (grossMomentTail_sharp_iff α K s hp hs).mpr hcrit

lemma regPhysicalCoefficients_moment_memLp (α K s : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (hs : 1 ≤ s) (hcrit : s < 3/2) (j : Fin 3) :
    MemLp (fun k : GW.Space => ((‖k‖^(s-1):ℝ):ℂ)*regPhysicalCoefficients α K hα hK j k)
      2 (volume : Measure GW.Space) := by
  let f := regPhysicalCoefficients α K hα hK j
  let g := fun k : GW.Space => ((‖k‖^(s-1):ℝ):ℂ)*f k
  have hm : AEStronglyMeasurable g (volume : Measure GW.Space) :=
    ((Complex.continuous_ofReal.measurable.comp (continuous_norm.measurable.pow_const _)).aestronglyMeasurable).mul
      (Lp.stronglyMeasurable f).aestronglyMeasurable
  have hb : (∫⁻ k, singularFieldDensity (s-1) f k ∂(volume : Measure GW.Space)) < ∞ := by
    have hle : (∫⁻ k, singularFieldDensity (s-1) f k ∂(volume : Measure GW.Space)) ≤
        ∑ i : Fin 3, ∫⁻ k, singularFieldDensity (s-1) (regPhysicalCoefficients α K hα hK i) k ∂(volume : Measure GW.Space) :=
      Finset.single_le_sum (f := fun i : Fin 3 => ∫⁻ k, singularFieldDensity (s-1)
        (regPhysicalCoefficients α K hα hK i) k ∂(volume : Measure GW.Space))
        (fun i _ => bot_le) (Finset.mem_univ j)
    exact hle.trans_lt (regPhysicalCoefficients_subcritical_mass α K s hα hK hs hcrit)
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  refine ⟨(hm.norm.aemeasurable.pow_const 2).aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun k => sq_nonneg ‖g k‖))).mpr
  convert hb using 1
  apply lintegral_congr
  intro k
  dsimp [g,singularFieldDensity]
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]

end GW.Regularity

-- Compiled component Domains01
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
namespace GW.Regularity
open GW.Fock GW.Gross GW.Analysis GW.Model

lemma regPhysicalNumber_domain_mono (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b)
    (v : Physical) (hv : v ∈ (physicalNumberPower b).domain) :
    v ∈ (physicalNumberPower a).domain := by
  rw [fractionalNumber_domains_eq a ha,physicalShiftedNumberPower_domain_map]
  rw [fractionalNumber_domains_eq b hb,physicalShiftedNumberPower_domain_map] at hv
  obtain ⟨x,hx,he⟩ := Submodule.mem_map.mp hv
  exact Submodule.mem_map.mpr ⟨x,shiftedNumberDomain_mono hab hx,he⟩

lemma regPhysicalField_number_mem (f : OneBoson) (u : FreeGraphDomain) :
    regularFieldGraphMap f u ∈ (physicalNumberPower (1/2)).domain := by
  let v : physicalNumberOperator.domain :=
    ⟨(freeGraphH0Input u).val,freeHamiltonian_number_mem (freeGraphH0Input u)⟩
  have he : regularFieldGraphMap f u = (physicalRegFieldOutput (phaseMultiplicationKernel f) v).val :=
    (generalizedField (phaseMultiplicationKernel f)).mem_graph_snd_inj
      (regularFieldGraphMap_graph f u) (physicalRegField_graph _ v) (freeGraphDomainInclusion_apply u)
  rw [he]
  exact (physicalRegFieldOutput (phaseMultiplicationKernel f) v).property

lemma regFree_coordinate_number_mem (u : FreeGraphDomain) (j : Fin 3)
    (hj : freeGraphDomainInclusion u ∈ (electronMomentumCoordinate j).domain) :
    electronMomentumCoordinate j ⟨freeGraphDomainInclusion u,hj⟩ ∈ (physicalNumberPower (1/2)).domain := by
  obtain ⟨hp,hn,hb⟩ := rootNumber_coordinate_composition (freeGraphH0Input u) j
  have he : electronMomentumCoordinate j ⟨freeGraphDomainInclusion u,hj⟩ =
      electronMomentumCoordinate j ⟨(freeGraphH0Input u).val,hp⟩ :=
    congrArg (electronMomentumCoordinate j) (Subtype.ext (freeGraphDomainInclusion_apply u))
  rw [he]
  exact hn

lemma regPositive_radial_mem (α K s : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (hs : 1 < s) (hcrit : s < 3/2) (u : FreeGraphDomain) :
    grossWeylCoefficient (GW.Gross.grossDressingCoefficient α K hα hK)
      (freeGraphDomainInclusion u) ∈ (electronRadialPower s).domain := by
  let r := s-1
  have hr : 0 < r := by dsimp [r]; linarith
  have hr1 : r ≤ 1 := by dsimp [r]; linarith
  obtain ⟨hf,hbound⟩ := reg_regular_field r hr hr1 (regPhysicalCoefficients α K hα hK)
    (regPhysicalCoefficients_moment_memLp α K s hα hK hs.le hcrit) u
  have hout : grossWeylCoefficient (GW.Gross.grossDressingCoefficient α K hα hK)
      (freeGraphDomainInclusion u) ∈ (electronRadialPower (1+r)).domain := by
    apply (radial_component_domain r hr.le _).mpr
    intro j
    obtain ⟨hp,hW,he⟩ := regPhysical_momentum_identity α K hα hK u j
    let γ := electronMomentumCoordinate j ⟨freeGraphDomainInclusion u,hp⟩-
      regularFieldGraphMap (regPhysicalCoefficients α K hα hK j) u
    have hγp : γ ∈ (electronRadialPower r).domain :=
      (electronRadialPower r).domain.sub_mem (regFree_coordinate_radial_mem r hr.le hr1 u j hp) (hf j)
    have hγN : γ ∈ (physicalNumberPower (1/2)).domain :=
      (physicalNumberPower (1/2)).domain.sub_mem (regFree_coordinate_number_mem u j hp)
        (regPhysicalField_number_mem _ u)
    have hγsmall := regPhysicalNumber_domain_mono (r/2) (1/2) (by positivity) (by norm_num)
      (by linarith) γ hγN
    have hQ : γ ∈ regGrossQsigma r := ⟨hγp,hγsmall⟩
    have hQW := Set.mem_image_of_mem (grossWeylSide true (GW.Gross.grossDressingCoefficient α K hα hK)) hQ
    rw [main_gross_fractional_domain_image true α K hα hK r hr.le hr1] at hQW
    refine ⟨hW,?_⟩
    have hpW : grossWeylCoefficient (GW.Gross.grossDressingCoefficient α K hα hK) γ ∈
        (electronRadialPower r).domain := hQW.1
    have heW := congrArg (grossWeylCoefficient (GW.Gross.grossDressingCoefficient α K hα hK)) he
    rw [LinearIsometryEquiv.apply_symm_apply] at heW
    exact heW.symm ▸ hpW
  convert hout using 1 <;> dsimp [r] <;> congr 2 <;> ring

end GW.Regularity

-- Compiled component Fractional03
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
namespace GW.Regularity
open GW.Fock GW.Gross GW.Analysis GW.Model

lemma regPositive_fractional_square (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (v : Physical) (hp : v ∈ (electronRadialPower r).domain)
    (hn : v ∈ (physicalNumberPower (1/2)).domain)
    (hf : v ∈ (freeFractionalOperator r).domain) :
    ‖freeFractionalOperator r ⟨v,hf⟩‖^2 ≤
      2*‖v‖^2+‖electronRadialPower r ⟨v,hp⟩‖^2+‖physicalNumberPower (1/2) ⟨v,hn⟩‖^2 := by
  let z : ℕ → GW.Space → ℝ := fun _ _ => 0
  let b : ℕ → GW.Space → ℝ := fun n _ => Real.sqrt (n:ℝ)
  let c : ℕ → GW.Space → ℝ := fun n _ => Real.sqrt (1+(n:ℝ))
  have hb : v ∈ (physicalSectorMultiplier b).domain := by
    rw [← physicalNumberHalf_eq_sectorMultiplier]
    exact hn
  obtain ⟨hz,hzero⟩ := physicalSectorMultiplier_domination z b (fun _ => measurable_const)
    (C := 0) (by norm_num) (fun n q => by simp [z]) ⟨v,hb⟩
  have hzval : ‖physicalSectorMultiplier z ⟨v,hz⟩‖ = 0 := by
    apply le_antisymm _ (norm_nonneg _)
    simpa only [zero_mul] using hzero
  obtain ⟨hc,hcval⟩ := physicalSectorMultiplier_quadratic z b c (fun _ => measurable_const)
    (fun n q => by dsimp [z,b,c]; rw [Real.sq_sqrt (by positivity),Real.sq_sqrt (Nat.cast_nonneg n)]; ring) v hz hb
  have hbval : physicalSectorMultiplier b ⟨v,hb⟩ = physicalNumberPower (1/2) ⟨v,hn⟩ :=
    partialMap_action_eq_of_same_input physicalNumberHalf_eq_sectorMultiplier.symm _ _ rfl
  rw [hzval,zero_pow (by decide : (2:ℕ) ≠ 0),add_zero,hbval] at hcval
  let a : ℕ → GW.Space → ℝ := fun n _ => numberPowerCoefficient (r/2) n
  obtain ⟨ha,hab⟩ := physicalSectorMultiplier_domination a c (fun _ => measurable_const)
    (C := 1) zero_le_one (fun n q => by
      rw [one_mul]
      apply (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mp
      rw [sq_abs,sq_abs]
      dsimp [a,c]
      rw [fractionalNumberCoefficient_eq,rpow_square _ _ (Nat.cast_nonneg n),
        show 2*(r/2)=r by ring,Real.sq_sqrt (by positivity)]
      simpa only [Real.rpow_one] using nonnegative_rpow_le_one_add (Nat.cast_nonneg n) hr hr1) ⟨v,hc⟩
  have hsmall : v ∈ (physicalNumberPower (r/2)).domain :=
    (congrArg (fun A : Physical →ₗ.[ℂ] Physical => v ∈ A.domain) (fractionalNumberOperator_eq (r/2))).mpr ha
  have haval : physicalSectorMultiplier a ⟨v,ha⟩ = physicalNumberPower (r/2) ⟨v,hsmall⟩ :=
    partialMap_action_eq_of_same_input (fractionalNumberOperator_eq (r/2)).symm _ _ rfl
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hab 2
  simp only [one_mul] at hsquare
  rw [haval,hcval] at hsquare
  have hquad : v ∈ (physicalSectorMultiplier (fractionalQuadraticWeight r)).domain :=
    (fractionalFree_domain_compare r hr hr1) ▸ hf
  have hcomp := (fractionalFree_norm_equivalence r hr hr1 v hf hquad).1
  rw [fractionalQuadratic_norm_split r v hp hsmall hquad] at hcomp
  linarith

end GW.Regularity

-- Compiled component Coordinates02
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
namespace GW.Regularity
open GW.Fock GW.Gross GW.Analysis GW.Model

lemma regPositive_coordinate_family_bound (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (u : FreeGraphDomain) (hj : ∀ j, freeGraphDomainInclusion u ∈ (electronMomentumCoordinate j).domain) :
    ∃ hp : ∀ j, electronMomentumCoordinate j ⟨freeGraphDomainInclusion u,hj j⟩ ∈ (electronRadialPower r).domain,
      ‖annihilationEscapeFamily (fun j => electronRadialPower r
        ⟨electronMomentumCoordinate j ⟨freeGraphDomainInclusion u,hj j⟩,hp j⟩)‖ ≤ ‖u‖ := by
  let hp := fun j => regFree_coordinate_radial_mem r hr hr1 u j (hj j)
  obtain ⟨hm,hb⟩ := regFree_radial_mem_bound (1+r) (by linarith) (by linarith) u
  refine ⟨hp,?_⟩
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2]
  have he := radial_component_norm_sq r hr ⟨freeGraphDomainInclusion u,hm⟩ hj hp
  change ‖electronRadialPower (1+r) ⟨freeGraphDomainInclusion u,hm⟩‖^2 = _ at he
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
  rw [he] at hs
  exact hs

lemma regPhysicalMultiplier_commute (a b : ℕ → GW.Space → ℝ) (v : Physical)
    (ha : v ∈ (physicalSectorMultiplier a).domain) (hb : v ∈ (physicalSectorMultiplier b).domain)
    (hab : v ∈ (physicalSectorMultiplier (fun n q => b n q*a n q)).domain) :
    ∃ hba : physicalSectorMultiplier a ⟨v,ha⟩ ∈ (physicalSectorMultiplier b).domain,
    ∃ hab' : physicalSectorMultiplier b ⟨v,hb⟩ ∈ (physicalSectorMultiplier a).domain,
      physicalSectorMultiplier b ⟨physicalSectorMultiplier a ⟨v,ha⟩,hba⟩ =
        physicalSectorMultiplier a ⟨physicalSectorMultiplier b ⟨v,hb⟩,hab'⟩ := by
  obtain ⟨hba,he⟩ := physicalSectorMultiplier_composition a b v ha hab
  have hswap : (fun n q => a n q*b n q) = (fun n q => b n q*a n q) := funext (fun n => funext (fun q => mul_comm _ _))
  have hab2 : v ∈ (physicalSectorMultiplier (fun n q => a n q*b n q)).domain := hswap.symm ▸ hab
  obtain ⟨hab',he'⟩ := physicalSectorMultiplier_composition b a v hb hab2
  refine ⟨hba,hab',he.trans (he'.trans ?_).symm⟩
  exact partialMap_action_eq_of_same_input (congrArg physicalSectorMultiplier hswap) _ _ rfl

end GW.Regularity

-- Compiled component Mixed02
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
namespace GW.Regularity
open GW.Fock GW.Gross GW.Analysis GW.Model

lemma regRadialZero_value (v : Physical) (hv : v ∈ (electronRadialPower 0).domain) :
    electronRadialPower 0 ⟨v,hv⟩ = v := by
  exact partialMap_action_eq_of_same_input radialPower_zero
    (⟨v,hv⟩ : (electronRadialPower 0).domain)
    (⟨v,Submodule.mem_top⟩ : ((LinearMap.id : Physical →ₗ[ℂ] Physical).toPMap ⊤).domain) rfl

lemma regCoordinate_family_norm (v : Physical) (hv : v ∈ (electronRadialPower 1).domain)
    (hj : ∀ j, v ∈ (electronMomentumCoordinate j).domain) :
    ‖annihilationEscapeFamily (fun j => electronMomentumCoordinate j ⟨v,hj j⟩)‖ =
      ‖electronRadialPower 1 ⟨v,hv⟩‖ := by
  have hv' : v ∈ (electronRadialPower (1+0)).domain := by simpa only [add_zero] using hv
  let hp (j : Fin 3) : electronMomentumCoordinate j ⟨v,hj j⟩ ∈ (electronRadialPower 0).domain :=
    (radial_coordinate_forward 0 (by norm_num) v hv' j).choose_spec
  have he := radial_component_norm_sq 0 (by norm_num) ⟨v,hv'⟩ hj hp
  change ‖electronRadialPower (1+0) ⟨v,hv'⟩‖^2 = ∑ j, ‖electronRadialPower 0 ⟨electronMomentumCoordinate j ⟨v,hj j⟩,hp j⟩‖^2 at he
  simp_rw [regRadialZero_value] at he
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2]
  have heact := partialMap_action_eq_of_same_input
    (congrArg electronRadialPower (add_zero (1:ℝ)))
    (⟨v,hv'⟩ : (electronRadialPower (1+0)).domain) (⟨v,hv⟩ : (electronRadialPower 1).domain) rfl
  rw [heact] at he
  exact he.symm

lemma regPositive_coordinate_number_family_bound (u : FreeGraphDomain)
    (hj : ∀ j, freeGraphDomainInclusion u ∈ (electronMomentumCoordinate j).domain) :
    ∃ hn : ∀ j, electronMomentumCoordinate j ⟨freeGraphDomainInclusion u,hj j⟩ ∈ (physicalNumberPower (1/2)).domain,
      ‖annihilationEscapeFamily (fun j => physicalNumberPower (1/2)
        ⟨electronMomentumCoordinate j ⟨freeGraphDomainInclusion u,hj j⟩,hn j⟩)‖ ≤ (1/2:ℝ)*‖u‖ := by
  let Ψ := freeGraphDomainInclusion u
  let a : ℕ → GW.Space → ℝ := fun n _ => Real.sqrt (n:ℝ)
  have ha : Ψ ∈ (physicalSectorMultiplier a).domain := by
    rw [← physicalNumberHalf_eq_sectorMultiplier]
    exact (singularFieldRootInput u).property
  have hval : (freeGraphH0Input u).val = Ψ := (freeGraphDomainInclusion_apply u).symm
  have hΨ : Ψ ∈ freeHamiltonian.domain := hval ▸ (freeGraphH0Input u).property
  obtain ⟨hm,hbound⟩ := physicalSectorMultiplier_domination
    (fun n q => ‖q‖*Real.sqrt (n:ℝ)) freeEnergySymbol
    (fun _ => measurable_norm.mul measurable_const) (C := 1/2) (by norm_num) (fun n q => by
      rw [abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)),
        abs_of_nonneg (freeEnergySymbol_nonnegative n q)]
      have hh := two_sqrt_mul_le_add (Nat.cast_nonneg n) (sq_nonneg ‖q‖)
      rw [Real.sqrt_sq (norm_nonneg q)] at hh
      unfold freeEnergySymbol
      nlinarith) (⟨Ψ,hΨ⟩ : freeHamiltonian.domain)
  obtain ⟨hp,he⟩ := physicalSectorMultiplier_composition a (fun _ q => ‖q‖) Ψ ha hm
  let v := physicalSectorMultiplier a ⟨Ψ,ha⟩
  have hv : v ∈ (electronRadialPower 1).domain := by simpa only [electronRadialPower,Real.rpow_one] using hp
  have hvbound : ‖electronRadialPower 1 ⟨v,hv⟩‖ ≤ (1/2:ℝ)*‖u‖ := by
    have hve : electronRadialPower 1 ⟨v,hv⟩ = physicalSectorMultiplier (fun n q => ‖q‖*Real.sqrt (n:ℝ)) ⟨Ψ,hm⟩ := by
      have er : electronRadialPower 1 = physicalSectorMultiplier (fun _ q => ‖q‖) := by
        simp only [electronRadialPower,Real.rpow_one]
      exact (partialMap_action_eq_of_same_input er ⟨v,hv⟩ ⟨v,hp⟩ rfl).trans he
    rw [hve]
    have hH0 : freeHamiltonian (⟨Ψ,hΨ⟩ : freeHamiltonian.domain) = freeHamiltonian (freeGraphH0Input u) :=
      congrArg freeHamiltonian (Subtype.ext hval.symm)
    have hh : ‖physicalSectorMultiplier freeEnergySymbol (⟨Ψ,hΨ⟩ : freeHamiltonian.domain)‖ ≤ ‖u‖ := by
      change ‖freeHamiltonian (⟨Ψ,hΨ⟩ : freeHamiltonian.domain)‖ ≤ ‖u‖
      rw [hH0]
      exact (freeGraph_norm_lower u).2
    exact hbound.trans (mul_le_mul_of_nonneg_left hh (by norm_num))
  have hcoord (j : Fin 3) : ∃ hvj : v ∈ (electronMomentumCoordinate j).domain,
      ∃ hnj : electronMomentumCoordinate j ⟨Ψ,hj j⟩ ∈ (physicalNumberPower (1/2)).domain,
      electronMomentumCoordinate j ⟨v,hvj⟩ = physicalNumberPower (1/2) ⟨electronMomentumCoordinate j ⟨Ψ,hj j⟩,hnj⟩ := by
    have hprod := (physicalSectorMultiplier_domination (fun n q => q j*Real.sqrt (n:ℝ))
      (fun n q => ‖q‖*Real.sqrt (n:ℝ)) (fun _ => (electronCoordinate_measurable j).mul measurable_const)
      zero_le_one (fun n q => by
        rw [one_mul,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _),abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))]
        exact mul_le_mul_of_nonneg_right (electronCoordinate_abs_le q j) (Real.sqrt_nonneg _)) ⟨Ψ,hm⟩).choose
    obtain ⟨hvj,hnj,hej⟩ := regPhysicalMultiplier_commute a (fun _ q => q j) Ψ ha (hj j) hprod
    have hn' : electronMomentumCoordinate j ⟨Ψ,hj j⟩ ∈ (physicalNumberPower (1/2)).domain :=
      (congrArg (fun A : Physical →ₗ.[ℂ] Physical => electronMomentumCoordinate j ⟨Ψ,hj j⟩ ∈ A.domain)
        physicalNumberHalf_eq_sectorMultiplier).mpr hnj
    refine ⟨hvj,hn',hej.trans ?_⟩
    exact partialMap_action_eq_of_same_input physicalNumberHalf_eq_sectorMultiplier.symm _ _ rfl
  let hvj := fun j => (hcoord j).choose
  let hnj := fun j => (hcoord j).choose_spec.choose
  refine ⟨hnj,?_⟩
  have hefamily : annihilationEscapeFamily (fun j => physicalNumberPower (1/2) ⟨electronMomentumCoordinate j ⟨Ψ,hj j⟩,hnj j⟩) =
      annihilationEscapeFamily (fun j => electronMomentumCoordinate j ⟨v,hvj j⟩) := by
    apply PiLp.ext
    intro j
    exact (hcoord j).choose_spec.choose_spec.symm
  rw [hefamily,regCoordinate_family_norm v hv hvj]
  exact hvbound

end GW.Regularity

-- Compiled component Fields02
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
namespace GW.Regularity
open GW.Fock GW.Gross GW.Analysis GW.Model

lemma regPhysicalCoefficients_amplitude (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    annihilationEscapeAmplitude (regPhysicalCoefficients α K hα hK) = grossSourceA α K hα hK := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2,grossFormRadialCoefficient_norm_sq]
  rfl

lemma regPhysicalField_number_bound (f : OneBoson) (u : FreeGraphDomain)
    (hn : regularFieldGraphMap f u ∈ (physicalNumberPower (1/2)).domain) :
    ‖physicalNumberPower (1/2) ⟨regularFieldGraphMap f u,hn⟩‖ ≤ 2*‖f‖*‖u‖ := by
  let v : physicalNumberOperator.domain :=
    ⟨(freeGraphH0Input u).val,freeHamiltonian_number_mem (freeGraphH0Input u)⟩
  have he : regularFieldGraphMap f u = (physicalRegFieldOutput (phaseMultiplicationKernel f) v).val :=
    (generalizedField (phaseMultiplicationKernel f)).mem_graph_snd_inj
      (regularFieldGraphMap_graph f u) (physicalRegField_graph _ v) (freeGraphDomainInclusion_apply u)
  have hedom : (⟨regularFieldGraphMap f u,hn⟩ : (physicalNumberPower (1/2)).domain) =
      physicalRegFieldOutput (phaseMultiplicationKernel f) v := Subtype.ext he
  rw [hedom]
  have hshift : ‖physicalShiftedNumberPower 1 (physicalRegShiftedNumberInput v)‖ ≤ ‖u‖ := by
    obtain ⟨hm,hb⟩ := freeGraph_shiftedNumber_bound u
    have he' : physicalRegShiftedNumberInput v =
        (⟨(freeGraphH0Input u).val,hm⟩ : (physicalShiftedNumberPower 1).domain) :=
      Subtype.ext (physicalRegShiftedNumberInput_val v)
    rw [he',freeGraphDomain_norm]
    exact hb
  exact (physicalRegPhaseField_norm f v).trans
    (mul_le_mul_of_nonneg_left hshift (by positivity))

lemma regPhysicalField_number_family_bound (fs : Fin 3 → OneBoson) (u : FreeGraphDomain)
    (hn : ∀ j, regularFieldGraphMap (fs j) u ∈ (physicalNumberPower (1/2)).domain) :
    ‖annihilationEscapeFamily (fun j => physicalNumberPower (1/2) ⟨regularFieldGraphMap (fs j) u,hn j⟩)‖ ≤
      2*annihilationEscapeAmplitude fs*‖u‖ := by
  have h := annihilationEscape_family_mul_bound
    (fun j => physicalNumberPower (1/2) ⟨regularFieldGraphMap (fs j) u,hn j⟩) fs (2*‖u‖)
    (by positivity) (fun j => (regPhysicalField_number_bound (fs j) u (hn j)).trans_eq (by ring))
  exact h.trans_eq (by ring)

lemma regPhysicalField_family_bound (fs : Fin 3 → OneBoson) (u : FreeGraphDomain) :
    ‖annihilationEscapeFamily (fun j => regularFieldGraphMap (fs j) u)‖ ≤
      2*annihilationEscapeAmplitude fs*‖u‖ := by
  exact (regularField_family_bound fs u).trans
    (mul_le_mul_of_nonneg_left (commutatorGraphRootMap_norm u) (by unfold annihilationEscapeAmplitude; positivity))

lemma regPhysicalField_radial_family_bound (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (fs : Fin 3 → OneBoson)
    (hf : ∀ j, MemLp (fun k : GW.Space => ((‖k‖^r:ℝ):ℂ)*fs j k) 2 (volume : Measure GW.Space))
    (u : FreeGraphDomain) :
    ∃ hp : ∀ j, regularFieldGraphMap (fs j) u ∈ (electronRadialPower r).domain,
      ‖annihilationEscapeFamily (fun j => electronRadialPower r ⟨regularFieldGraphMap (fs j) u,hp j⟩)‖ ≤
        (2*annihilationEscapeAmplitude (fun j => regularFieldMoment r (fs j) (hf j))+
          2*annihilationEscapeAmplitude fs)*‖u‖ := by
  obtain ⟨hp,hb⟩ := reg_regular_field r hr hr1 fs hf u
  rw [fiberPhysicalRoot_norm] at hb
  refine ⟨hp,hb.trans ?_⟩
  exact (add_le_add
    (mul_le_mul_of_nonneg_left (commutatorGraphRootMap_norm u) (by unfold annihilationEscapeAmplitude; positivity))
    (mul_le_mul_of_nonneg_left (fractionalRemainderMixed_bound true r hr.le hr1 u)
      (by unfold annihilationEscapeAmplitude; positivity))).trans_eq (by ring)

end GW.Regularity

-- Compiled component Gamma02
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
namespace GW.Regularity
open GW.Fock GW.Gross GW.Analysis GW.Model

lemma regFamily_map_sub (T : Physical →ₗ.[ℂ] Physical) (v w : Fin 3 → Physical)
    (hv : ∀ j, v j ∈ T.domain) (hw : ∀ j, w j ∈ T.domain)
    (hsub : ∀ j, v j-w j ∈ T.domain) :
    annihilationEscapeFamily (fun j => T ⟨v j-w j,hsub j⟩) =
      annihilationEscapeFamily (fun j => T ⟨v j,hv j⟩)-annihilationEscapeFamily (fun j => T ⟨w j,hw j⟩) := by
  apply PiLp.ext
  intro j
  exact map_sub T.toFun ⟨v j,hv j⟩ ⟨w j,hw j⟩

def regPositiveGamma (fs : Fin 3 → OneBoson) (u : FreeGraphDomain)
    (hj : ∀ j, freeGraphDomainInclusion u ∈ (electronMomentumCoordinate j).domain) (j : Fin 3) : Physical :=
  electronMomentumCoordinate j ⟨freeGraphDomainInclusion u,hj j⟩-regularFieldGraphMap (fs j) u

lemma regPositive_gamma_estimates (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (fs : Fin 3 → OneBoson)
    (hf : ∀ j, MemLp (fun k : GW.Space => ((‖k‖^r:ℝ):ℂ)*fs j k) 2 (volume : Measure GW.Space))
    (u : FreeGraphDomain) (hj : ∀ j, freeGraphDomainInclusion u ∈ (electronMomentumCoordinate j).domain) :
    ∃ hp : ∀ j, regPositiveGamma fs u hj j ∈ (electronRadialPower r).domain,
    ∃ hn : ∀ j, regPositiveGamma fs u hj j ∈ (physicalNumberPower (1/2)).domain,
      ‖annihilationEscapeFamily (regPositiveGamma fs u hj)‖ ≤ (1+2*annihilationEscapeAmplitude fs)*‖u‖ ∧
      ‖annihilationEscapeFamily (fun j => electronRadialPower r ⟨regPositiveGamma fs u hj j,hp j⟩)‖ ≤
        (1+2*annihilationEscapeAmplitude (fun j => regularFieldMoment r (fs j) (hf j))+
          2*annihilationEscapeAmplitude fs)*‖u‖ ∧
      ‖annihilationEscapeFamily (fun j => physicalNumberPower (1/2) ⟨regPositiveGamma fs u hj j,hn j⟩)‖ ≤
        ((1/2:ℝ)+2*annihilationEscapeAmplitude fs)*‖u‖ := by
  obtain ⟨hpr,hprbound⟩ := regPositive_coordinate_family_bound r hr.le hr1 u hj
  obtain ⟨hfr,hfrbound⟩ := regPhysicalField_radial_family_bound r hr hr1 fs hf u
  obtain ⟨hpn,hpnbound⟩ := regPositive_coordinate_number_family_bound u hj
  let hfn := fun j => regPhysicalField_number_mem (fs j) u
  let hp := fun j => (electronRadialPower r).domain.sub_mem (hpr j) (hfr j)
  let hn := fun j => (physicalNumberPower (1/2)).domain.sub_mem (hpn j) (hfn j)
  refine ⟨hp,hn,?_,?_,?_⟩
  · have he : annihilationEscapeFamily (regPositiveGamma fs u hj) =
        annihilationEscapeFamily (fun j => electronMomentumCoordinate j ⟨freeGraphDomainInclusion u,hj j⟩)-
          annihilationEscapeFamily (fun j => regularFieldGraphMap (fs j) u) := by
      apply PiLp.ext
      intro j
      rfl
    obtain ⟨hz,hb⟩ := regPositive_coordinate_family_bound 0 (by norm_num) (by norm_num) u hj
    simp_rw [regRadialZero_value] at hb
    rw [he]
    exact (norm_sub_le _ _).trans ((add_le_add hb (regPhysicalField_family_bound fs u)).trans_eq (by ring))
  · change ‖annihilationEscapeFamily (fun j => electronRadialPower r
      ⟨electronMomentumCoordinate j ⟨freeGraphDomainInclusion u,hj j⟩-regularFieldGraphMap (fs j) u,hp j⟩)‖ ≤ _
    rw [regFamily_map_sub (electronRadialPower r) _ _ hpr hfr hp]
    exact (norm_sub_le _ _).trans ((add_le_add hprbound hfrbound).trans_eq (by ring))
  · change ‖annihilationEscapeFamily (fun j => physicalNumberPower (1/2)
      ⟨electronMomentumCoordinate j ⟨freeGraphDomainInclusion u,hj j⟩-regularFieldGraphMap (fs j) u,hn j⟩)‖ ≤ _
    rw [regFamily_map_sub (physicalNumberPower (1/2)) _ _ hpn hfn hn]
    exact (norm_sub_le _ _).trans
      ((add_le_add hpnbound (regPhysicalField_number_family_bound fs u hfn)).trans_eq (by ring))

end GW.Regularity

-- Compiled component FractionalFamily01
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
namespace GW.Regularity
open GW.Fock GW.Gross GW.Analysis GW.Model

lemma regPositive_fractional_family_bound (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (v : Fin 3 → Physical) (hp : ∀ j, v j ∈ (electronRadialPower r).domain)
    (hn : ∀ j, v j ∈ (physicalNumberPower (1/2)).domain) :
    ∃ hf : ∀ j, v j ∈ (freeFractionalOperator r).domain,
      ‖annihilationEscapeFamily (fun j => freeFractionalOperator r ⟨v j,hf j⟩)‖ ≤
        2*‖annihilationEscapeFamily v‖+
        ‖annihilationEscapeFamily (fun j => electronRadialPower r ⟨v j,hp j⟩)‖+
        ‖annihilationEscapeFamily (fun j => physicalNumberPower (1/2) ⟨v j,hn j⟩)‖ := by
  let hnsmall := fun j => regPhysicalNumber_domain_mono (r/2) (1/2) (by positivity) (by norm_num)
    (by linarith) (v j) (hn j)
  let hf (j : Fin 3) : v j ∈ (freeFractionalOperator r).domain :=
    (fractionalFree_domain r hr hr1).symm ▸ (show v j ∈ (electronRadialPower r).domain ⊓
      (physicalNumberPower (r/2)).domain from ⟨hp j,hnsmall j⟩)
  refine ⟨hf,?_⟩
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3)))
    (fun j _ => regPositive_fractional_square r hr hr1 (v j) (hp j) (hn j) (hf j))
  have hsq : ‖annihilationEscapeFamily (fun j => freeFractionalOperator r ⟨v j,hf j⟩)‖^2 ≤
      2*‖annihilationEscapeFamily v‖^2+
      ‖annihilationEscapeFamily (fun j => electronRadialPower r ⟨v j,hp j⟩)‖^2+
      ‖annihilationEscapeFamily (fun j => physicalNumberPower (1/2) ⟨v j,hn j⟩)‖^2 := by
    simpa only [PiLp.norm_sq_eq_of_L2,annihilationEscapeFamily,WithLp.ofLp_toLp,
      Finset.sum_add_distrib,← Finset.mul_sum] using hs
  let A := ‖annihilationEscapeFamily v‖
  let B := ‖annihilationEscapeFamily (fun j => electronRadialPower r ⟨v j,hp j⟩)‖
  let C := ‖annihilationEscapeFamily (fun j => physicalNumberPower (1/2) ⟨v j,hn j⟩)‖
  have ha : 0 ≤ A := norm_nonneg _
  have hb : 0 ≤ B := norm_nonneg _
  have hc : 0 ≤ C := norm_nonneg _
  apply (sq_le_sq₀ (norm_nonneg _) (by change 0 ≤ 2*A+B+C; positivity)).mp
  change _ ≤ (2*A+B+C)^2
  change _ ≤ 2*A^2+B^2+C^2 at hsq
  nlinarith [mul_nonneg ha hb,mul_nonneg ha hc,mul_nonneg hb hc,sq_nonneg A]

lemma regPositive_radial_le_fractional (r : ℝ) (hr : 0 ≤ r) (v : (freeFractionalOperator r).domain) :
    ∃ hp : v.val ∈ (electronRadialPower r).domain,
      ‖electronRadialPower r ⟨v.val,hp⟩‖ ≤ ‖freeFractionalOperator r v‖ := by
  have h := physicalSectorMultiplier_domination (fun _ q => ‖q‖^r) (fractionalFreeWeight r)
    (fun _ => continuous_norm.measurable.pow_const r) zero_le_one (fun n q => by
      rw [abs_of_nonneg (Real.rpow_nonneg (norm_nonneg q) _),
        abs_of_nonneg (zero_le_one.trans (fractionalFreeWeight_one r hr n q)),one_mul]
      have he : ‖q‖^r = (‖q‖^2)^(r/2) := by
        rw [← Real.rpow_two,← Real.rpow_mul (norm_nonneg q)]
        congr 1
        ring
      rw [he]
      exact Real.rpow_le_rpow (sq_nonneg _) (by unfold freeGraphWeight freeEnergySymbol; linarith [Nat.cast_nonneg (α := ℝ) n])
        (by positivity)) v
  simpa only [one_mul,electronRadialPower,freeFractionalOperator] using h

end GW.Regularity

-- Compiled component Endpoint03
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
namespace GW.Regularity
open GW.Fock GW.Gross GW.Analysis GW.Model

lemma regRadialZero_mem (v : Physical) : v ∈ (electronRadialPower 0).domain := by
  change v ∈ (physicalSectorMultiplier (fun _ q => ‖q‖^(0:ℝ))).domain
  rw [radialPower_zero]
  exact Submodule.mem_top

lemma regWeyl_family_norm (f : OneBoson) (v : Fin 3 → Physical) :
    ‖annihilationEscapeFamily (fun j => grossWeylCoefficient f (v j))‖ = ‖annihilationEscapeFamily v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [PiLp.norm_sq_eq_of_L2,annihilationEscapeFamily,LinearIsometryEquiv.norm_map]

lemma regPositive_endpoint_bound (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (u : FreeGraphDomain) :
    ∃ hp : grossWeylCoefficient (GW.Gross.grossDressingCoefficient α K hα hK)
        (freeGraphDomainInclusion u) ∈ (electronRadialPower 1).domain,
      ‖electronRadialPower 1 ⟨grossWeylCoefficient (GW.Gross.grossDressingCoefficient α K hα hK)
        (freeGraphDomainInclusion u),hp⟩‖ ≤
        (1+2*annihilationEscapeAmplitude (regPhysicalCoefficients α K hα hK))*‖u‖ := by
  let fs := regPhysicalCoefficients α K hα hK
  let W := grossWeylCoefficient (GW.Gross.grossDressingCoefficient α K hα hK)
  let χ := W (freeGraphDomainInclusion u)
  let hi := fun j => regPhysical_momentum_identity α K hα hK u j
  let hj := fun j => (hi j).choose
  let hW := fun j => (hi j).choose_spec.choose
  let γ := fun j => electronMomentumCoordinate j ⟨freeGraphDomainInclusion u,hj j⟩-regularFieldGraphMap (fs j) u
  have hid (j : Fin 3) : electronMomentumCoordinate j ⟨χ,hW j⟩ = W (γ j) := by
    have h := congrArg W (hi j).choose_spec.choose_spec
    dsimp only [W] at h
    simpa only [LinearIsometryEquiv.apply_symm_apply] using h
  have hχ' : χ ∈ (electronRadialPower (1+0)).domain :=
    (radial_component_domain 0 (by norm_num) χ).mpr (fun j => ⟨hW j,regRadialZero_mem _⟩)
  have hχ : χ ∈ (electronRadialPower 1).domain := by simpa only [add_zero] using hχ'
  refine ⟨hχ,?_⟩
  rw [← regCoordinate_family_norm χ hχ hW]
  have he : annihilationEscapeFamily (fun j => electronMomentumCoordinate j ⟨χ,hW j⟩) =
      annihilationEscapeFamily (fun j => W (γ j)) := by
    apply PiLp.ext
    intro j
    exact hid j
  rw [he,regWeyl_family_norm]
  have hγ : annihilationEscapeFamily γ =
      annihilationEscapeFamily (fun j => electronMomentumCoordinate j ⟨freeGraphDomainInclusion u,hj j⟩)-
        annihilationEscapeFamily (fun j => regularFieldGraphMap (fs j) u) := by
    apply PiLp.ext
    intro j
    rfl
  obtain ⟨hz,hb⟩ := regPositive_coordinate_family_bound 0 (by norm_num) (by norm_num) u hj
  simp_rw [regRadialZero_value] at hb
  rw [hγ]
  exact (norm_sub_le _ _).trans ((add_le_add hb (regPhysicalField_family_bound fs u)).trans_eq (by ring))

end GW.Regularity

-- Compiled component Dressed02
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
namespace GW.Regularity
open GW.Fock GW.Gross GW.Analysis GW.Model

lemma regPhysical_family_mul_bound (v w : Fin 3 → Physical) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ j, ‖v j‖ ≤ ‖w j‖*C) :
    ‖annihilationEscapeFamily v‖ ≤ ‖annihilationEscapeFamily w‖*C := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) hC)).mp
  rw [mul_pow,PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  change ‖v j‖^2 ≤ ‖w j‖^2*C^2
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (h j) 2

lemma regPositive_dressed_radial_bound (α K r : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hf : ∀ j, MemLp (fun k : GW.Space => ((‖k‖^r:ℝ):ℂ)*regPhysicalCoefficients α K hα hK j k)
      2 (volume : Measure GW.Space)) (u : FreeGraphDomain) :
    ∃ hp : grossWeylCoefficient (GW.Gross.grossDressingCoefficient α K hα hK)
      (freeGraphDomainInclusion u) ∈ (electronRadialPower (1+r)).domain,
      ‖electronRadialPower (1+r) ⟨grossWeylCoefficient (GW.Gross.grossDressingCoefficient α K hα hK)
        (freeGraphDomainInclusion u),hp⟩‖ ≤
        (grossSourceL α K hα hK)^r*
          ((7/2:ℝ)+8*annihilationEscapeAmplitude (regPhysicalCoefficients α K hα hK)+
            2*annihilationEscapeAmplitude (fun j => regularFieldMoment r (regPhysicalCoefficients α K hα hK j) (hf j)))*‖u‖ := by
  let fs := regPhysicalCoefficients α K hα hK
  let W := grossWeylCoefficient (GW.Gross.grossDressingCoefficient α K hα hK)
  let χ := W (freeGraphDomainInclusion u)
  let hi := fun j => regPhysical_momentum_identity α K hα hK u j
  let hj := fun j => (hi j).choose
  let hW := fun j => (hi j).choose_spec.choose
  let γ := regPositiveGamma fs u hj
  have hid (j : Fin 3) : electronMomentumCoordinate j ⟨χ,hW j⟩ = W (γ j) := by
    have h := congrArg W (hi j).choose_spec.choose_spec
    dsimp only [W] at h
    simpa only [LinearIsometryEquiv.apply_symm_apply,γ,regPositiveGamma,fs,W,χ] using h
  obtain ⟨hγp,hγN,hγ0,hγr,hγn⟩ := regPositive_gamma_estimates r hr hr1 fs hf u hj
  obtain ⟨hγF,hγFbound⟩ := regPositive_fractional_family_bound r hr.le hr1 γ hγp hγN
  have hγbound : ‖annihilationEscapeFamily (fun j => freeFractionalOperator r ⟨γ j,hγF j⟩)‖ ≤
      ((7/2:ℝ)+8*annihilationEscapeAmplitude fs+
        2*annihilationEscapeAmplitude (fun j => regularFieldMoment r (fs j) (hf j)))*‖u‖ := by
    exact hγFbound.trans ((add_le_add (add_le_add (mul_le_mul_of_nonneg_left hγ0 (by norm_num)) hγr) hγn).trans_eq (by ring))
  let hWF := fun j => regGross_fractional_bound true α K hα hK r hr.le hr1 ⟨γ j,hγF j⟩
  let hWp := fun j => regPositive_radial_le_fractional r hr.le
    ⟨W (γ j),(hWF j).choose⟩
  let hpχ (j : Fin 3) : electronMomentumCoordinate j ⟨χ,hW j⟩ ∈ (electronRadialPower r).domain :=
    (hid j).symm ▸ (hWp j).choose
  have hχ : χ ∈ (electronRadialPower (1+r)).domain :=
    (radial_component_domain r hr.le χ).mpr (fun j => ⟨hW j,hpχ j⟩)
  refine ⟨hχ,?_⟩
  have hnormχ : ‖electronRadialPower (1+r) ⟨χ,hχ⟩‖ =
      ‖annihilationEscapeFamily (fun j => electronRadialPower r ⟨electronMomentumCoordinate j ⟨χ,hW j⟩,hpχ j⟩)‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2]
    exact radial_component_norm_sq r hr.le ⟨χ,hχ⟩ hW hpχ
  rw [hnormχ]
  have hcomp (j : Fin 3) : ‖electronRadialPower r ⟨electronMomentumCoordinate j ⟨χ,hW j⟩,hpχ j⟩‖ ≤
      ‖freeFractionalOperator r ⟨γ j,hγF j⟩‖*(grossSourceL α K hα hK)^r := by
    have he : (⟨electronMomentumCoordinate j ⟨χ,hW j⟩,hpχ j⟩ : (electronRadialPower r).domain) =
        ⟨W (γ j),(hWp j).choose⟩ := Subtype.ext (hid j)
    rw [he]
    exact ((hWp j).choose_spec.trans (hWF j).choose_spec).trans_eq (mul_comm _ _)
  have hb := regPhysical_family_mul_bound
    (fun j => electronRadialPower r ⟨electronMomentumCoordinate j ⟨χ,hW j⟩,hpχ j⟩)
    (fun j => freeFractionalOperator r ⟨γ j,hγF j⟩) ((grossSourceL α K hα hK)^r)
    (Real.rpow_nonneg (regGross_sourceL_pos α K hα hK).le r) hcomp
  exact (hb.trans (mul_le_mul_of_nonneg_right hγbound
    (Real.rpow_nonneg (regGross_sourceL_pos α K hα hK).le r))).trans_eq (by ring)

end GW.Regularity

-- Compiled component Final02
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
namespace GW.Regularity
open GW.Fock GW.Gross GW.Analysis GW.Model

/-- The two explicit finite constants supplied by the source proof. -/
def regPositiveConstant (α K s : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (hs : 1 ≤ s) (hcrit : s < 3/2) : ℝ :=
  if s=1 then
    2+2*annihilationEscapeAmplitude (regPhysicalCoefficients α K hα hK)+
      (1+‖GW.Gross.grossDressingCoefficient α K hα hK‖)^2
  else
    1+(grossSourceL α K hα hK)^(s-1)*
      ((7/2:ℝ)+8*annihilationEscapeAmplitude (regPhysicalCoefficients α K hα hK)+
        2*annihilationEscapeAmplitude (fun j => regularFieldMoment (s-1) (regPhysicalCoefficients α K hα hK j)
          (regPhysicalCoefficients_moment_memLp α K s hα hK hs hcrit j)))+
      (1+‖GW.Gross.grossDressingCoefficient α K hα hK‖)^2

lemma regPositiveConstant_nonneg (α K s : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (hs : 1 ≤ s) (hcrit : s < 3/2) :
    0 ≤ regPositiveConstant α K s hα hK hs hcrit := by
  have hL : 0 ≤ grossSourceL α K hα hK := (regGross_sourceL_pos α K hα hK).le
  have hpow : 0 ≤ (grossSourceL α K hα hK)^(s-1) := Real.rpow_nonneg hL _
  unfold regPositiveConstant annihilationEscapeAmplitude
  split <;> positivity

lemma regPositive_graph_bound (α K s : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (hs : 1 ≤ s) (hcrit : s < 3/2)
    (u : FreeGraphDomain) :
    ∃ hp : grossWeylCoefficient (GW.Gross.grossDressingCoefficient α K hα hK)
      (freeGraphDomainInclusion u) ∈ (electronRadialPower s).domain,
    ∃ hn : grossWeylCoefficient (GW.Gross.grossDressingCoefficient α K hα hK)
      (freeGraphDomainInclusion u) ∈ physicalNumberOperator.domain,
      ‖grossWeylCoefficient (GW.Gross.grossDressingCoefficient α K hα hK) (freeGraphDomainInclusion u)‖+
      ‖electronRadialPower s ⟨grossWeylCoefficient (GW.Gross.grossDressingCoefficient α K hα hK)
        (freeGraphDomainInclusion u),hp⟩‖+
      ‖physicalNumberOperator ⟨grossWeylCoefficient (GW.Gross.grossDressingCoefficient α K hα hK)
        (freeGraphDomainInclusion u),hn⟩‖ ≤ regPositiveConstant α K s hα hK hs hcrit*‖u‖ := by
  let f := GW.Gross.grossDressingCoefficient α K hα hK
  have hzero : ‖grossWeylCoefficient f (freeGraphDomainInclusion u)‖ ≤ ‖u‖ := by
    rw [LinearIsometryEquiv.norm_map]
    exact (freeGraph_norm_lower u).1
  have hN := grossGraphWeyl_number_mem f u
  have hNb := grossGraphWeyl_number_bound f u
  by_cases he : s=1
  · subst s
    obtain ⟨hp,hpb⟩ := regPositive_endpoint_bound α K hα hK u
    refine ⟨hp,hN,?_⟩
    exact (add_le_add (add_le_add hzero hpb) hNb).trans_eq (by
      simp only [regPositiveConstant]
      dsimp [f]
      ring)
  · have hr : 0 < s-1 := by
      have hs' : 1 < s := lt_of_le_of_ne hs (Ne.symm he)
      linarith
    have hr1 : s-1 ≤ 1 := by linarith
    have h := regPositive_dressed_radial_bound α K (s-1) hα hK hr hr1
      (regPhysicalCoefficients_moment_memLp α K s hα hK hs hcrit) u
    rw [show 1+(s-1)=s by ring] at h
    obtain ⟨hp,hpb⟩ := h
    refine ⟨hp,hN,?_⟩
    exact (add_le_add (add_le_add hzero hpb) hNb).trans_eq (by
      simp only [regPositiveConstant,ite_eq_right he]
      dsimp [f]
      ring)

lemma regPositive_original_graph_bound (α K s : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (hs : 1 ≤ s) (hcrit : s < 3/2)
    (u : freeHamiltonian.domain) :
    ∃ hp : grossWeylCoefficient (GW.Gross.grossDressingCoefficient α K hα hK) u.val ∈ (electronRadialPower s).domain,
    ∃ hn : grossWeylCoefficient (GW.Gross.grossDressingCoefficient α K hα hK) u.val ∈ physicalNumberOperator.domain,
      ‖grossWeylCoefficient (GW.Gross.grossDressingCoefficient α K hα hK) u.val‖+
      ‖electronRadialPower s ⟨grossWeylCoefficient (GW.Gross.grossDressingCoefficient α K hα hK) u.val,hp⟩‖+
      ‖physicalNumberOperator ⟨grossWeylCoefficient (GW.Gross.grossDressingCoefficient α K hα hK) u.val,hn⟩‖ ≤
        regPositiveConstant α K s hα hK hs hcrit*‖freeHamiltonian u+u.val‖ := by
  have h := regPositive_graph_bound α K s hα hK hs hcrit (commutatorSourceGraphInput u)
  rw [commutatorSourceGraphInput_value,grossSourceGraph_norm] at h
  exact h

/-- The original dressed free domain and its bounded graph-norm inclusion. -/
theorem reg_positive (α K s : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (hs : 1 ≤ s) (hcrit : s < 3/2) :
    (freeHamiltonian.domain.map
      (grossWeylCoefficient (GW.Gross.grossDressingCoefficient α K hα hK)).toLinearMap ≤
      (electronRadialPower s).domain ⊓ physicalNumberOperator.domain) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : freeHamiltonian.domain,
      ∃ hp : grossWeylCoefficient (GW.Gross.grossDressingCoefficient α K hα hK) u.val ∈ (electronRadialPower s).domain,
      ∃ hn : grossWeylCoefficient (GW.Gross.grossDressingCoefficient α K hα hK) u.val ∈ physicalNumberOperator.domain,
        ‖grossWeylCoefficient (GW.Gross.grossDressingCoefficient α K hα hK) u.val‖+
        ‖electronRadialPower s ⟨grossWeylCoefficient (GW.Gross.grossDressingCoefficient α K hα hK) u.val,hp⟩‖+
        ‖physicalNumberOperator ⟨grossWeylCoefficient (GW.Gross.grossDressingCoefficient α K hα hK) u.val,hn⟩‖ ≤
          C*‖freeHamiltonian u+u.val‖ := by
  constructor
  · intro χ hχ
    obtain ⟨ψ,hψ,he⟩ := Submodule.mem_map.mp hχ
    obtain ⟨hp,hn,hb⟩ := regPositive_original_graph_bound α K s hα hK hs hcrit ⟨ψ,hψ⟩
    change grossWeylCoefficient (GW.Gross.grossDressingCoefficient α K hα hK) ψ = χ at he
    exact he ▸ ⟨hp,hn⟩
  · exact ⟨regPositiveConstant α K s hα hK hs hcrit,regPositiveConstant_nonneg α K s hα hK hs hcrit,
      regPositive_original_graph_bound α K s hα hK hs hcrit⟩

end GW.Regularity
