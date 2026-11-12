module
public import GW.Operators.BasicFree
public import Mathlib.Analysis.MeanInequalities
@[expose] public section
noncomputable section
namespace GW.Fock

def electronMomentumCoordinate (j : Fin 3) : Physical →ₗ.[ℂ] Physical :=
  physicalSectorMultiplier (fun _ q => q j)

def electronRadialPower (r : ℝ) : Physical →ₗ.[ℂ] Physical :=
  physicalSectorMultiplier (fun _ q => ‖q‖ ^ r)

lemma electronCoordinate_abs_le (q : GW.Space) (j : Fin 3) : |q j| ≤ ‖q‖ := by
  rw [← Real.norm_eq_abs]
  exact PiLp.norm_apply_le q j

lemma electronCoordinate_measurable (j : Fin 3) : Measurable (fun q : GW.Space => q j) :=
  (PiLp.continuous_apply 2 _ j).measurable

lemma nonnegative_rpow_le_one_add {t a b : ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a) (hab : a ≤ b) :
    t^a ≤ 1+t^b := by
  by_cases h : t ≤ 1
  · exact (Real.rpow_le_one ht h ha).trans (le_add_of_nonneg_right (Real.rpow_nonneg ht _))
  · exact (Real.rpow_le_rpow_of_exponent_le (le_of_not_ge h) hab).trans (le_add_of_nonneg_left zero_le_one)

lemma radial_shiftedRoot_bound (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (n : ℕ) (q : GW.Space) :
    |‖q‖^r * Real.sqrt ((n:ℝ)+1)| ≤ |freeGraphWeight n q| := by
  have ht := norm_nonneg q
  have hn : 0 ≤ (n:ℝ)+1 := by positivity
  have hpow : (‖q‖^r)^2 ≤ 1+‖q‖^2 := by
    have he : (‖q‖^r)^2 = ‖q‖^(r*2) := by rw [Real.rpow_mul ht,Real.rpow_two]
    rw [he]
    simpa only [Real.rpow_two] using nonnegative_rpow_le_one_add ht
      (show 0 ≤ r*2 by positivity) (show r*2 ≤ 2 by linarith)
  have hs : ‖q‖^r ≤ Real.sqrt (1+‖q‖^2) := Real.le_sqrt_of_sq_le hpow
  rw [abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht _) (Real.sqrt_nonneg _)),
    abs_of_nonneg (zero_le_one.trans (freeGraphWeight_one n q))]
  refine (mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _)).trans ?_
  have hm := two_sqrt_mul_le_add (show 0 ≤ 1+‖q‖^2 by positivity) hn
  unfold freeGraphWeight freeEnergySymbol
  nlinarith [Nat.cast_nonneg (α := ℝ) n, sq_nonneg ‖q‖]

lemma radial_shiftedRoot_composition (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (u : freeGraphOperator.domain) :
    ∃ hn : u.val ∈ (physicalShiftedNumberPower (1/2)).domain,
      ∃ hp : physicalShiftedNumberPower (1/2) ⟨u.val,hn⟩ ∈ (electronRadialPower r).domain,
        ‖electronRadialPower r ⟨physicalShiftedNumberPower (1/2) ⟨u.val,hn⟩,hp⟩‖ ≤ ‖freeGraphOperator u‖ := by
  rw [physicalShiftedNumberHalf_eq_sectorMultiplier]
  have hn := (physicalSectorMultiplier_domination (fun n _ => Real.sqrt ((n:ℝ)+1)) freeGraphWeight
    (fun _ => measurable_const) zero_le_one (fun n q => by
      rw [abs_of_nonneg (Real.sqrt_nonneg _),abs_of_nonneg (zero_le_one.trans (freeGraphWeight_one n q)),one_mul]
      have hc : Real.sqrt ((n:ℝ)+1) ≤ (n:ℝ)+1 := by
        apply Real.sqrt_le_iff.mpr
        constructor
        · positivity
        · nlinarith [Nat.cast_nonneg (α := ℝ) n, sq_nonneg (n:ℝ)]
      unfold freeGraphWeight freeEnergySymbol
      linarith [sq_nonneg ‖q‖]) u).choose
  obtain ⟨hm,hb⟩ := physicalSectorMultiplier_domination (fun n q => ‖q‖^r * Real.sqrt ((n:ℝ)+1)) freeGraphWeight
    (fun _ => (continuous_norm.measurable.pow_const r).mul measurable_const) zero_le_one
    (fun n q => by simpa only [one_mul] using radial_shiftedRoot_bound r hr hr1 n q) u
  obtain ⟨hp,he⟩ := physicalSectorMultiplier_composition (fun n _ => Real.sqrt ((n:ℝ)+1))
    (fun _ q => ‖q‖^r) u.val hn hm
  refine ⟨hn,hp,(congrArg norm he).le.trans ?_⟩
  change _ ≤ ‖physicalSectorMultiplier freeGraphWeight u‖
  simpa only [one_mul] using hb

lemma rootNumber_coordinate_composition (u : freeHamiltonian.domain) (j : Fin 3) :
    ∃ hp : u.val ∈ (electronMomentumCoordinate j).domain,
      ∃ hn : electronMomentumCoordinate j ⟨u.val,hp⟩ ∈ (physicalNumberPower (1/2)).domain,
        ‖physicalNumberPower (1/2) ⟨electronMomentumCoordinate j ⟨u.val,hp⟩,hn⟩‖ ≤
          (1/2:ℝ)*‖freeHamiltonian u‖ := by
  rw [physicalNumberHalf_eq_sectorMultiplier]
  let v : freeGraphOperator.domain := ⟨u.val,freeGraphOperator_domain.symm ▸ u.property⟩
  have hp := (physicalSectorMultiplier_domination (fun _ q => q j) freeGraphWeight
    (fun _ => electronCoordinate_measurable j) zero_le_one (fun n q => by
      rw [abs_of_nonneg (zero_le_one.trans (freeGraphWeight_one n q)),one_mul]
      refine (electronCoordinate_abs_le q j).trans ?_
      unfold freeGraphWeight freeEnergySymbol
      nlinarith [sq_nonneg (‖q‖-1),Nat.cast_nonneg (α := ℝ) n]) v).choose
  obtain ⟨hm,hb⟩ := physicalSectorMultiplier_domination
    (fun n q => Real.sqrt (n:ℝ)*q j) freeEnergySymbol
    (fun _ => measurable_const.mul (electronCoordinate_measurable j)) (C := 1/2) (by norm_num) (fun n q => by
      rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _),abs_of_nonneg (freeEnergySymbol_nonnegative n q)]
      refine (mul_le_mul_of_nonneg_left (electronCoordinate_abs_le q j) (Real.sqrt_nonneg _)).trans ?_
      have hh := two_sqrt_mul_le_add (Nat.cast_nonneg (α := ℝ) n) (sq_nonneg ‖q‖)
      rw [Real.sqrt_sq (norm_nonneg q)] at hh
      unfold freeEnergySymbol
      linarith) u
  obtain ⟨hn,he⟩ := physicalSectorMultiplier_composition (fun _ q => q j)
    (fun n _ => Real.sqrt (n:ℝ)) u.val hp hm
  exact ⟨hp,hn,(congrArg norm he).le.trans hb⟩

lemma fractionalNumber_coordinate_scalar (s : ℝ) (hs : 1 < s) (hs2 : s ≤ 2) (n t : ℝ)
    (hn : 0 ≤ n) (ht : 0 ≤ t) :
    n^((s-1)/2) * t ≤ 1 + (t^s+n) := by
  have hs0 : 0 < s := zero_lt_one.trans hs
  have ha : 0 ≤ (s-1)/s := div_nonneg (sub_nonneg.mpr hs.le) hs0.le
  have hb : 0 ≤ 1/s := one_div_nonneg.mpr hs0.le
  have hsum : (s-1)/s+1/s=1 := by field_simp; ring
  have h := Real.geom_mean_le_arith_mean2_weighted ha hb
    (Real.rpow_nonneg hn (s/2)) (Real.rpow_nonneg ht s) hsum
  rw [← Real.rpow_mul hn, ← Real.rpow_mul ht, show (s/2)*((s-1)/s)=(s-1)/2 by field_simp,
    show s*(1/s)=1 by field_simp,Real.rpow_one] at h
  refine h.trans ?_
  have hnp := nonnegative_rpow_le_one_add hn (show 0 ≤ s/2 by positivity) (show s/2 ≤ 1 by linarith)
  rw [Real.rpow_one] at hnp
  have ha1 : (s-1)/s ≤ 1 := by linarith
  have hb1 : 1/s ≤ 1 := by linarith
  have h₁ : (s-1)/s*n^(s/2) ≤ 1+n := by
    exact (mul_le_mul_of_nonneg_right ha1 (Real.rpow_nonneg hn _)).trans (by simpa only [one_mul] using hnp)
  have h₂ : 1/s*t^s ≤ t^s := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hb1 (Real.rpow_nonneg ht s)
  linarith

lemma fractional_coordinate_transfer (s : ℝ) (hs : 1 < s) (hs2 : s ≤ 2) (u : Physical)
    (hp : u ∈ (electronRadialPower s).domain) (hn : u ∈ physicalNumberOperator.domain) (j : Fin 3) :
    ∃ hj : u ∈ (electronMomentumCoordinate j).domain,
      electronMomentumCoordinate j ⟨u,hj⟩ ∈
        (electronRadialPower (s-1)).domain ⊓ (physicalNumberPower ((s-1)/2)).domain := by
  rw [physicalNumber_eq_sectorMultiplier] at hn
  let b := fun (n : ℕ) (q : GW.Space) => 1+(‖q‖^s+(n:ℝ))
  have hu : u ∈ (physicalSectorMultiplier b).domain := by
    apply (physicalSectorMultiplier_domain b u).mpr
    apply (congrArg (fun (V : Submodule ℂ ElectronBosonSum) => freeFourierRepresentation u ∈ V)
      (sumWeightDomain_add_one (fun n q => ‖q‖^s+(n:ℝ)))).mpr
    exact sumWeightDomain_add_mem (fun _ q => ‖q‖^s) (fun n _ => (n:ℝ)) _
      ((physicalSectorMultiplier_domain _ u).mp hp) ((physicalSectorMultiplier_domain _ u).mp hn)
  have hbnn (n : ℕ) (q : GW.Space) : 0 ≤ b n q := by
    change 0 ≤ 1 + (‖q‖^s+(n:ℝ))
    positivity
  have hj := (physicalSectorMultiplier_domination (fun _ q => q j) b
    (fun _ => electronCoordinate_measurable j) zero_le_one (fun n q => by
      rw [abs_of_nonneg (hbnn n q),one_mul]
      have h := nonnegative_rpow_le_one_add (norm_nonneg q) zero_le_one hs.le
      rw [Real.rpow_one] at h
      exact (electronCoordinate_abs_le q j).trans (h.trans (by change _ ≤ 1 + (‖q‖^s+(n:ℝ)); linarith [Nat.cast_nonneg (α := ℝ) n])))
      ⟨u,hu⟩).choose
  have hpr := (physicalSectorMultiplier_domination (fun _ q => ‖q‖^(s-1)*q j) (fun _ q => ‖q‖^s)
    (fun _ => (continuous_norm.measurable.pow_const _).mul (electronCoordinate_measurable j))
    zero_le_one (fun _ q => by
      rw [abs_mul,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg q) _),
        abs_of_nonneg (Real.rpow_nonneg (norm_nonneg q) _),one_mul]
      refine (mul_le_mul_of_nonneg_left (electronCoordinate_abs_le q j) (Real.rpow_nonneg (norm_nonneg q) _)).trans_eq ?_
      calc
        ‖q‖^(s-1) * ‖q‖ = ‖q‖^(s-1) * ‖q‖^(1:ℝ) := by rw [Real.rpow_one]
        _ = ‖q‖^s := by rw [← Real.rpow_add' (norm_nonneg q) (by linarith : (s-1)+1 ≠ 0),sub_add_cancel]) ⟨u,hp⟩).choose
  let r := (s-1)/2
  have hr : r ≠ 0 := by dsimp [r]; linarith
  have hnr := (physicalSectorMultiplier_domination (fun n q => (n:ℝ)^r*q j) b
    (fun _ => measurable_const.mul (electronCoordinate_measurable j)) zero_le_one (fun n q => by
      rw [abs_mul,abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _),
        abs_of_nonneg (hbnn n q),one_mul]
      exact (mul_le_mul_of_nonneg_left (electronCoordinate_abs_le q j) (Real.rpow_nonneg (Nat.cast_nonneg n) _)).trans
        (fractionalNumber_coordinate_scalar s hs hs2 n ‖q‖ (Nat.cast_nonneg n) (norm_nonneg _))) ⟨u,hu⟩).choose
  have he : physicalNumberPower r = physicalSectorMultiplier (fun n _ => (n:ℝ)^r) := by
    change bochnerDiagonal _ Sector (numberPowerCoefficient r) = _
    have hc : numberPowerCoefficient r = (fun (n : ℕ) => (n:ℝ)^r) := by
      funext n
      unfold numberPowerCoefficient
      split <;> rename_i h
      · exact (hr h).elim
      · rfl
    rw [hc]
    exact (physicalSectorMultiplier_constant (fun n => (n:ℝ)^r)).symm
  refine ⟨hj, (physicalSectorMultiplier_composition (fun _ q => q j) (fun _ q => ‖q‖^(s-1)) u hj hpr).choose, ?_⟩
  change _ ∈ (physicalNumberPower r).domain
  rw [he]
  exact (physicalSectorMultiplier_composition (fun _ q => q j) (fun n _ => (n:ℝ)^r) u hj hnr).choose

end GW.Fock
