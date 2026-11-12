module
public import GW.Fock.FockCcr
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal
namespace GW.Fock


lemma pullthrough_scalar_root (a : ℕ → ℝ) (ha : ∀ n, |a n| ≤ (n:ℝ)+1)
    (U : (shiftedNumberPower Sector (3/2)).domain) (V : Carrier)
    (hV : ∀ n, V n = (a n : ℂ) • U.val n) :
    V ∈ (shiftedNumberPower Sector (1/2)).domain := by
  have hs := (shiftedNumberPower_domain Sector (3/2) U.val).mp U.property
  have hs' : Summable (fun n : ℕ => ((n:ℝ)+1)^3*‖U.val n‖^2) := by
    simpa only [show 2*(3/2:ℝ)=3 by norm_num,Real.rpow_ofNat] using hs
  apply (shiftedNumberPower_domain Sector (1/2) V).mpr
  simp only [show 2*(1/2:ℝ)=1 by norm_num,Real.rpow_one]
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ hs'
  intro n
  rw [hV n,norm_smul,Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ ((n:ℝ)+1)*(((n:ℝ)+1)*‖U.val n‖)^2 := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right (ha n) (norm_nonneg _)) 2) (by positivity)
    _ = _ := by ring

def pullthroughNumberInput (U : (shiftedNumberPower Sector (3/2)).domain) : numberOperator.domain :=
  ⟨U.val,by
    rw [ordinaryNumber_shiftedOne_domain]
    exact shiftedNumberDomain_mono (by norm_num) U.property⟩

def pullthroughShiftedInput (U : (shiftedNumberPower Sector (3/2)).domain) : (shiftedNumberPower Sector 1).domain :=
  ⟨U.val,shiftedNumberDomain_mono (by norm_num) U.property⟩

lemma pullthroughNumber_root (U : (shiftedNumberPower Sector (3/2)).domain) :
    numberOperator (pullthroughNumberInput U) ∈ (numberPower Sector (1/2)).domain := by
  rw [numberPower_domain_eq Sector (1/2) (by norm_num)]
  have ha (n : ℕ) : |(n:ℝ)| ≤ (n:ℝ)+1 := by
    rw [abs_of_nonneg (Nat.cast_nonneg n)]
    linarith
  exact pullthrough_scalar_root (fun n => (n:ℝ)) ha U _
    (fun n => numberDiagonal_apply Sector (pullthroughNumberInput U) n)

lemma pullthroughShifted_root (U : (shiftedNumberPower Sector (3/2)).domain) :
    shiftedNumberPower Sector 1 (pullthroughShiftedInput U) ∈ (numberPower Sector (1/2)).domain := by
  rw [numberPower_domain_eq Sector (1/2) (by norm_num)]
  have ha (n : ℕ) : |(n:ℝ)+1| ≤ (n:ℝ)+1 :=
    (abs_of_nonneg (by positivity : 0 ≤ (n:ℝ)+1)).le
  apply pullthrough_scalar_root (fun n => (n:ℝ)+1) ha U _
  intro n
  simpa only [pullthroughShiftedInput,Real.rpow_one] using shiftedNumberPower_apply Sector 1 (pullthroughShiftedInput U) n

def pullthroughShiftedNumberInput (U : (shiftedNumberPower Sector 1).domain) : numberOperator.domain :=
  ⟨U.val,by rw [ordinaryNumber_shiftedOne_domain]; exact U.property⟩

lemma pullthrough_shifted_one_action (U : (shiftedNumberPower Sector 1).domain) :
    shiftedNumberPower Sector 1 U = numberOperator (pullthroughShiftedNumberInput U)+U.val := by
  apply lp.ext
  funext n
  rw [shiftedNumberPower_apply,Real.rpow_one]
  simp only [lp.coeFn_add,Pi.add_apply]
  rw [numberDiagonal_apply]
  simp only [pullthroughShiftedNumberInput,Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_one,add_smul,one_smul]



def pullthroughWeightedInput (U : (shiftedNumberPower Sector (3/2)).domain) :
    (shiftedNumberPower Sector (1+(1/2))).domain :=
  ⟨U.val,by simpa only [show (1+(1/2):ℝ)=3/2 by norm_num] using U.property⟩

def pullthroughAnnihilationOutput (f : OneBoson) (U : (shiftedNumberPower Sector (3/2)).domain) :
    (shiftedNumberPower Sector 1).domain :=
  weightedAnnihilationSectorOutput ordinarySectorKernel (ordinaryKernel f) 1 zero_le_one (pullthroughWeightedInput U)

def pullthroughCreationOutput (f : OneBoson) (U : (shiftedNumberPower Sector (3/2)).domain) :
    (shiftedNumberPower Sector 1).domain :=
  weightedCreationSectorOutput ordinarySectorKernel (ordinaryKernel f) 1 zero_le_one (pullthroughWeightedInput U)

lemma pullthroughAnnihilationOutput_graph (f : OneBoson) (U : (shiftedNumberPower Sector (3/2)).domain) :
    (U.val,(pullthroughAnnihilationOutput f U).val) ∈ (ordinaryAnnihilation f).graph :=
  (ordinaryAnnihilation f).mem_graph
    (weightedAnnihilationSectorInput ordinarySectorKernel (ordinaryKernel f) 1 zero_le_one (pullthroughWeightedInput U))

lemma pullthroughCreationOutput_graph (f : OneBoson) (U : (shiftedNumberPower Sector (3/2)).domain) :
    (U.val,(pullthroughCreationOutput f U).val) ∈ (ordinaryCreation f).graph :=
  (ordinaryCreation f).mem_graph
    (weightedCreationSectorInput ordinarySectorKernel (ordinaryKernel f) 1 zero_le_one (pullthroughWeightedInput U))

lemma pullthroughAnnihilationOutput_coordinate (f : OneBoson)
    (U : (shiftedNumberPower Sector (3/2)).domain) (n : ℕ) :
    (pullthroughAnnihilationOutput f U).val n =
      sectorAnnihilation ordinarySectorKernel (ordinaryKernel f) n (U.val (n+1)) :=
  maximalSectorAnnihilation_apply _ _ n

lemma pullthroughCreationOutput_zero (f : OneBoson) (U : (shiftedNumberPower Sector (3/2)).domain) :
    (pullthroughCreationOutput f U).val 0 = 0 := maximalSectorCreation_zero _ _

lemma pullthroughCreationOutput_succ (f : OneBoson) (U : (shiftedNumberPower Sector (3/2)).domain) (n : ℕ) :
    (pullthroughCreationOutput f U).val (n+1) =
      sectorCreation ordinarySectorKernel (ordinaryKernel f) n (U.val n) :=
  maximalSectorCreation_succ _ _ n

def pullthroughAnnihilationNumberInput (f : OneBoson) (U : (shiftedNumberPower Sector (3/2)).domain) :
    (ordinaryAnnihilation f).domain :=
  ordinaryAnnihilationRootInput f ⟨numberOperator (pullthroughNumberInput U),pullthroughNumber_root U⟩

def pullthroughCreationShiftedInput (f : OneBoson) (U : (shiftedNumberPower Sector (3/2)).domain) :
    (ordinaryCreation f).domain :=
  ordinaryCreationRootInput f ⟨shiftedNumberPower Sector 1 (pullthroughShiftedInput U),pullthroughShifted_root U⟩

def pullthroughCreationNumberInput (f : OneBoson) (U : (shiftedNumberPower Sector (3/2)).domain) :
    numberOperator.domain :=
  ⟨(pullthroughCreationOutput f U).val,by
    rw [ordinaryNumber_shiftedOne_domain]
    exact (pullthroughCreationOutput f U).property⟩

set_option backward.isDefEq.respectTransparency.types false in
lemma ordinary_annihilation_number_pullthrough (f : OneBoson) (U : (shiftedNumberPower Sector (3/2)).domain) :
    ordinaryAnnihilation f (pullthroughAnnihilationNumberInput f U) =
      shiftedNumberPower Sector 1 (pullthroughAnnihilationOutput f U) := by
  apply lp.ext
  funext n
  rw [ordinaryAnnihilation_apply,shiftedNumberPower_apply,Real.rpow_one,
    pullthroughAnnihilationOutput_coordinate]
  change sectorAnnihilation ordinarySectorKernel (ordinaryKernel f) n
    (numberOperator (pullthroughNumberInput U) (n+1)) = _
  rw [numberDiagonal_apply,map_smul]
  simp only [pullthroughNumberInput,Nat.cast_add,Nat.cast_one,Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_one]

set_option backward.isDefEq.respectTransparency.types false in
lemma ordinary_creation_number_pullthrough (f : OneBoson) (U : (shiftedNumberPower Sector (3/2)).domain) :
    numberOperator (pullthroughCreationNumberInput f U) =
      ordinaryCreation f (pullthroughCreationShiftedInput f U) := by
  apply lp.ext
  funext n
  cases n with
  | zero =>
    rw [numberDiagonal_apply,ordinaryCreation_zero]
    simp only [Nat.cast_zero,zero_smul]
  | succ n =>
    rw [numberDiagonal_apply,ordinaryCreation_succ]
    simp only [pullthroughCreationNumberInput,pullthroughCreationShiftedInput,ordinaryCreationRootInput,Nat.cast_add,Nat.cast_one]
    change (n+1:ℂ) • (pullthroughCreationOutput f U).val (n+1) =
      sectorCreation ordinarySectorKernel (ordinaryKernel f) n
        (shiftedNumberPower Sector 1 (pullthroughShiftedInput U) n)
    rw [pullthroughCreationOutput_succ,shiftedNumberPower_apply,Real.rpow_one,map_smul]
    simp only [pullthroughShiftedInput,Nat.cast_add,Nat.cast_one,Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_one]

lemma ordinary_annihilation_number_pullthrough_plus (f : OneBoson)
    (U : (shiftedNumberPower Sector (3/2)).domain) :
    ordinaryAnnihilation f (pullthroughAnnihilationNumberInput f U) =
      numberOperator (pullthroughShiftedNumberInput (pullthroughAnnihilationOutput f U))+
        (pullthroughAnnihilationOutput f U).val := by
  rw [ordinary_annihilation_number_pullthrough,pullthrough_shifted_one_action]



def pullthroughFieldProduct (f g : OneBoson) (u : numberOperator.domain) : Carrier :=
  ordinaryField f (ordinaryFieldCompositionInput f g (ccrNumberInput u))

lemma pullthroughFieldProduct_expansion (f g : OneBoson) (u : numberOperator.domain) :
    pullthroughFieldProduct f g u =
      ccrTwoOutput false false f g (ccrNumberInput u)+ccrTwoOutput true false f g (ccrNumberInput u)+
      ccrTwoOutput false true f g (ccrNumberInput u)+ccrTwoOutput true true f g (ccrNumberInput u) := by
  change (ordinaryField f).toFun
    (ordinaryShiftedToField f (ordinaryTwoMiddle false g (ccrNumberInput u))+
      ordinaryShiftedToField f (ordinaryTwoMiddle true g (ccrNumberInput u))) = _
  rw [map_add]
  change ordinaryField f (ordinaryShiftedToField f (ordinaryTwoMiddle false g (ccrNumberInput u)))+
    ordinaryField f (ordinaryShiftedToField f (ordinaryTwoMiddle true g (ccrNumberInput u))) = _
  rw [ordinaryField_weighted_action,ordinaryField_weighted_action]
  change (_+_)+(_+_) = ((_+_)+_)+_
  abel

lemma pullthroughFieldProduct_graphs (f g : OneBoson) (u : numberOperator.domain) :
    ∃ v : Carrier, (u.val,v) ∈ (ordinaryField g).graph ∧ (v,pullthroughFieldProduct f g u) ∈ (ordinaryField f).graph := by
  let w := ordinaryShiftedToField g (ordinaryOneToRoot (ccrNumberInput u))
  refine ⟨ordinaryField g w,(ordinaryField g).mem_graph w,?_⟩
  have hh := (ordinaryField f).mem_graph (ordinaryFieldCompositionInput f g (ccrNumberInput u))
  rw [ordinaryFieldCompositionInput_val] at hh
  exact hh

lemma pullthrough_field_commutator (f g : OneBoson) (u : numberOperator.domain) :
    pullthroughFieldProduct f g u-pullthroughFieldProduct g f u =
      (2*Complex.I*((⟪f,g⟫_ℂ).im:ℂ)) • u.val := by
  rw [pullthroughFieldProduct_expansion,pullthroughFieldProduct_expansion,
    ccrTwoOutput_annihilation_commute f g,ccrTwoOutput_creation_commute f g,
    ccrTwoOutput_mixed f g,ccrTwoOutput_mixed g f]
  have he : (2*Complex.I*((⟪f,g⟫_ℂ).im:ℂ)) = ⟪f,g⟫_ℂ-⟪g,f⟫_ℂ := by
    have hr : (⟪f,g⟫_ℂ).re = (⟪g,f⟫_ℂ).re := by
      convert! inner_re_symm (𝕜 := ℂ) f g using 1 <;> rfl
    have hi : (⟪f,g⟫_ℂ).im = -(⟪g,f⟫_ℂ).im := by
      convert! inner_im_symm (𝕜 := ℂ) f g using 1 <;> rfl
    apply Complex.ext <;> simp <;> linarith
  rw [he,sub_smul]
  abel

lemma pullthrough_momentum_field_commutator (f g : OneBoson) (u : numberOperator.domain) :
    pullthroughFieldProduct f (Complex.I • g) u-pullthroughFieldProduct (Complex.I • g) f u =
      (2*Complex.I*((⟪f,g⟫_ℂ).re:ℂ)) • u.val := by
  have h := pullthrough_field_commutator f (Complex.I • g) u
  have he : (⟪f,Complex.I • g⟫_ℂ).im = (⟪f,g⟫_ℂ).re := by
    rw [inner_smul_right,Complex.mul_im,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_add]
  rwa [he] at h

lemma pullthrough_momentum_field_graphs (f g : OneBoson) (u : numberOperator.domain) :
    (∃ v : Carrier, (u.val,v) ∈ (ordinaryMomentumField g).graph ∧
      (v,pullthroughFieldProduct f (Complex.I • g) u) ∈ (ordinaryField f).graph) ∧
    (∃ v : Carrier, (u.val,v) ∈ (ordinaryField f).graph ∧
      (v,pullthroughFieldProduct (Complex.I • g) f u) ∈ (ordinaryMomentumField g).graph) :=
  ⟨pullthroughFieldProduct_graphs f (Complex.I • g) u,pullthroughFieldProduct_graphs (Complex.I • g) f u⟩


end GW.Fock
