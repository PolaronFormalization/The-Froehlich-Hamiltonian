module
public import GW.Fock.Symmetrization
public import GW.Analysis.SeriesDomination
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
@[expose] public section
noncomputable section
open scoped Topology InnerProductSpace ENNReal
namespace GW.Fock
section ScalarDiagonal
variable (E : ℕ → Type*) [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℂ (E n)]

/-- Actual maximal coordinate product domain on the specified dependent sum. -/
def scalarDomain (a : ℕ → ℝ) : Submodule ℂ (lp E 2) where
  carrier := {u | Memℓp (fun n => (a n : ℂ) • u n) 2}
  zero_mem' := by
    change Memℓp (fun n => (a n : ℂ) • (0 : lp E 2) n) 2
    simpa only [lp.coeFn_zero,Pi.zero_apply,smul_zero,Pi.zero_def] using
      (zero_memℓp : Memℓp (fun n => (0 : E n)) 2)
  add_mem' := by
    intro u v hu hv
    change Memℓp (fun n => (a n : ℂ) • u n) 2 at hu
    change Memℓp (fun n => (a n : ℂ) • v n) 2 at hv
    change Memℓp (fun n => (a n : ℂ) • (u+v) n) 2
    simpa only [lp.coeFn_add,Pi.add_apply,smul_add,Pi.add_def] using hu.add hv
  smul_mem' := by
    intro c u hu
    change Memℓp (fun n => (a n : ℂ) • u n) 2 at hu
    change Memℓp (fun n => (a n : ℂ) • (c • u) n) 2
    have h := hu.const_smul c
    simpa only [lp.coeFn_smul,Pi.smul_apply,Pi.smul_def, smul_comm (a _ : ℂ) c] using h

def scalarDiagonal (a : ℕ → ℝ) : lp E 2 →ₗ.[ℂ] lp E 2 where
  domain := scalarDomain E a
  toFun :=
    { toFun := fun u => ⟨(fun n => (a n : ℂ) • (u : lp E 2) n),u.property⟩
      map_add' := by intro u v; apply lp.ext; funext n; exact smul_add _ _ _
      map_smul' := by intro c u; apply lp.ext; funext n; exact smul_comm _ _ _ }

lemma scalarDiagonal_apply (a : ℕ → ℝ) (u : (scalarDiagonal E a).domain) (n : ℕ) :
    scalarDiagonal E a u n = (a n : ℂ) • (u : lp E 2) n := rfl

lemma scalarDiagonal_domain_iff (a : ℕ → ℝ) (u : lp E 2) :
    u ∈ (scalarDiagonal E a).domain ↔ Summable (fun n => a n ^ 2*‖u n‖ ^ 2) := by
  change Memℓp (fun n => (a n : ℂ) • u n) 2 ↔ _
  rw [GW.Analysis.memℓp_two_iff_sq]
  simp only [norm_smul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]

lemma scalarDiagonal_norm_sq (a : ℕ → ℝ) (u : (scalarDiagonal E a).domain) :
    ‖scalarDiagonal E a u‖ ^ 2 = ∑' n, a n ^ 2*‖(u : lp E 2) n‖ ^ 2 := by
  rw [GW.Analysis.lp_norm_sq]
  apply tsum_congr
  intro n
  rw [scalarDiagonal_apply,norm_smul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]

lemma scalarDiagonal_one : scalarDiagonal E (fun _ => 1) =
    (LinearMap.id : lp E 2 →ₗ[ℂ] lp E 2).toPMap ⊤ := by
  apply LinearPMap.ext
  · change scalarDomain E (fun _ => 1) = ⊤
    apply top_unique
    intro u _
    change Memℓp (fun n => (1 : ℂ) • u n) 2
    simpa only [one_smul] using lp.memℓp u
  · intro u hu ht
    change scalarDiagonal E (fun _ => 1) ⟨u,hu⟩ = u
    apply lp.ext
    funext n
    simp only [scalarDiagonal_apply,Complex.ofReal_one,one_smul]

def numberDiagonal : lp E 2 →ₗ.[ℂ] lp E 2 := scalarDiagonal E (fun n => (n : ℝ))
def shiftedNumberPower (r : ℝ) : lp E 2 →ₗ.[ℂ] lp E 2 := scalarDiagonal E (fun n => ((n : ℝ)+1) ^ r)
/-- The zero coefficient branch is literal one, so no use of 0^0 is needed. -/
def numberPowerCoefficient (r : ℝ) (n : ℕ) : ℝ := by
  classical
  exact if r = 0 then 1 else (n : ℝ) ^ r

def numberPower (r : ℝ) : lp E 2 →ₗ.[ℂ] lp E 2 := scalarDiagonal E (numberPowerCoefficient r)

lemma numberPower_zero : numberPower E 0 = (LinearMap.id : lp E 2 →ₗ[ℂ] lp E 2).toPMap ⊤ := by
  unfold numberPower
  have h : numberPowerCoefficient 0 = fun _ => 1 := by funext n; simp [numberPowerCoefficient]
  rw [h]; exact scalarDiagonal_one E

lemma shiftedNumberPower_zero : shiftedNumberPower E 0 =
    (LinearMap.id : lp E 2 →ₗ[ℂ] lp E 2).toPMap ⊤ := by
  simp only [shiftedNumberPower,Real.rpow_zero]
  exact scalarDiagonal_one E

lemma numberPower_ne_zero (r : ℝ) (hr : r ≠ 0) : numberPower E r = scalarDiagonal E (fun n => (n : ℝ) ^ r) := by
  unfold numberPower
  congr 1
  funext n
  simp [numberPowerCoefficient,hr]

lemma numberPower_one : numberPower E 1 = numberDiagonal E := by
  rw [numberPower_ne_zero E 1 one_ne_zero]
  simp only [Real.rpow_one,numberDiagonal]
lemma number_weight_bounds (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    (n : ℝ)^r ≤ ((n : ℝ)+1)^r ∧
    ((n : ℝ)+1)^r ≤ (2 : ℝ)^r * max 1 ((n : ℝ)^r) := by
  constructor
  · exact Real.rpow_le_rpow (Nat.cast_nonneg n) (by linarith) hr
  · by_cases hn : n = 0
    · subst n
      simp only [Nat.cast_zero,zero_add,Real.one_rpow]
      exact le_trans (Real.one_le_rpow (by norm_num) hr)
        (le_mul_of_one_le_right (Real.rpow_nonneg (by norm_num) _) (le_max_left _ _))
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      calc
        ((n : ℝ)+1)^r ≤ (2*(n : ℝ))^r :=
          Real.rpow_le_rpow (by positivity) (by linarith) hr
        _ = (2 : ℝ)^r * (n : ℝ)^r := Real.mul_rpow (by norm_num) (Nat.cast_nonneg n)
        _ ≤ (2 : ℝ)^r * max 1 ((n : ℝ)^r) :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.rpow_nonneg (by norm_num) _)

lemma number_weight_sq_bound (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    (((n : ℝ)+1)^r)^2 ≤ ((2 : ℝ)^r)^2 * (1+((n : ℝ)^r)^2) := by
  have h := (number_weight_bounds n r hr).2
  have ha := Real.rpow_nonneg (Nat.cast_nonneg n) r
  have hb := Real.rpow_nonneg (by positivity : 0 ≤ (n : ℝ)+1) r
  have hc := Real.rpow_nonneg (by norm_num : 0 ≤ (2 : ℝ)) r
  have hs : (((n : ℝ)+1)^r)^2 ≤ ((2 : ℝ)^r * max 1 ((n : ℝ)^r))^2 :=
    pow_le_pow_left₀ hb h 2
  rw [mul_pow] at hs
  apply hs.trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  rcases le_total ((n : ℝ)^r) 1 with hle | hge
  · rw [max_eq_left hle]; nlinarith [sq_nonneg ((n : ℝ)^r)]
  · rw [max_eq_right hge]; linarith

lemma rpow_square (x r : ℝ) (hx : 0 ≤ x) : (x^r)^2 = x^(2*r) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  ring

lemma shiftedNumberPower_domain (r : ℝ) (u : lp E 2) :
    u ∈ (shiftedNumberPower E r).domain ↔
      Summable (fun n : ℕ => ((n : ℝ)+1)^(2*r)*‖u n‖^2) := by
  rw [shiftedNumberPower,scalarDiagonal_domain_iff]
  simp only [rpow_square _ _ (by positivity : 0 ≤ (Nat.cast _ : ℝ)+1)]

lemma numberPower_domain (r : ℝ) (hr : 0 < r) (u : lp E 2) :
    u ∈ (numberPower E r).domain ↔
      Summable (fun n : ℕ => (n : ℝ)^(2*r)*‖u n‖^2) := by
  rw [numberPower_ne_zero E r (ne_of_gt hr),scalarDiagonal_domain_iff]
  simp only [rpow_square _ _ (Nat.cast_nonneg _)]

lemma numberPower_domain_eq (r : ℝ) (hr : 0 < r) :
    (numberPower E r).domain = (shiftedNumberPower E r).domain := by
  apply Submodule.ext
  intro u
  rw [numberPower_ne_zero E r (ne_of_gt hr),shiftedNumberPower,
    scalarDiagonal_domain_iff,scalarDiagonal_domain_iff]
  constructor
  · intro h
    have hu := (GW.Analysis.memℓp_two_iff_sq (fun n => u n)).mp (lp.memℓp u)
    have hmajor := (hu.add h).mul_left (((2 : ℝ)^r)^2)
    apply Summable.of_nonneg_of_le (fun n => mul_nonneg (sq_nonneg _) (sq_nonneg _)) _ hmajor
    intro n
    calc
      (((n : ℝ)+1)^r)^2 * ‖u n‖^2 ≤
          (((2 : ℝ)^r)^2 * (1+((n : ℝ)^r)^2)) * ‖u n‖^2 :=
        mul_le_mul_of_nonneg_right (number_weight_sq_bound n r hr.le) (sq_nonneg _)
      _ = ((2 : ℝ)^r)^2 * (‖u n‖^2 + ((n : ℝ)^r)^2*‖u n‖^2) := by ring
  · intro h
    apply Summable.of_nonneg_of_le (fun n => mul_nonneg (sq_nonneg _) (sq_nonneg _)) _ h
    intro n
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg n) r)
        (number_weight_bounds n r hr.le).1 2) (sq_nonneg _)

lemma numberPower_apply (r : ℝ) (hr : r ≠ 0)
    (u : (numberPower E r).domain) (n : ℕ) :
    numberPower E r u n = (↑((n : ℝ)^r) : ℂ) • (u : lp E 2) n := by
  change (numberPowerCoefficient r n : ℂ) • _ = _
  simp [numberPowerCoefficient,hr]

lemma shiftedNumberPower_apply (r : ℝ)
    (u : (shiftedNumberPower E r).domain) (n : ℕ) :
    shiftedNumberPower E r u n = (↑(((n : ℝ)+1)^r) : ℂ) • (u : lp E 2) n := rfl

/-- Canonical shifted-domain input, with the same ambient vector. -/
def shiftedNumberInput (r : ℝ) (hr : 0 < r) (u : (numberPower E r).domain) :
    (shiftedNumberPower E r).domain := ⟨u, by
  rw [← numberPower_domain_eq E r hr]
  exact u.property⟩

lemma numberPower_norm_sq (r : ℝ) (hr : r ≠ 0) (u : (numberPower E r).domain) :
    ‖numberPower E r u‖^2 = ∑' n : ℕ, ((n : ℝ)^r)^2*‖(u : lp E 2) n‖^2 := by
  rw [GW.Analysis.lp_norm_sq]
  apply tsum_congr
  intro n
  rw [numberPower_apply E r hr,norm_smul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]

lemma numberPower_graph_lower (r : ℝ) (hr : 0 < r) (u : (numberPower E r).domain) :
    ‖(u : lp E 2)‖^2 + ‖numberPower E r u‖^2 ≤
      ‖(u : lp E 2)‖^2 + ‖shiftedNumberPower E r (shiftedNumberInput E r hr u)‖^2 := by
  apply add_le_add le_rfl
  apply pow_le_pow_left₀ (norm_nonneg _)
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro n
  rw [numberPower_apply E r (ne_of_gt hr),shiftedNumberPower_apply,norm_smul,norm_smul,
    Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) r),
    abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ (n : ℝ)+1) r)]
  exact mul_le_mul_of_nonneg_right (number_weight_bounds n r hr.le).1 (norm_nonneg _)

lemma numberDiagonal_domain (u : lp E 2) :
    u ∈ (numberDiagonal E).domain ↔ Summable (fun n : ℕ => (n : ℝ)^2*‖u n‖^2) :=
  scalarDiagonal_domain_iff E (fun n => (n : ℝ)) u

lemma numberDiagonal_apply (u : (numberDiagonal E).domain) (n : ℕ) :
    numberDiagonal E u n = (n : ℂ) • (u : lp E 2) n := rfl

set_option backward.isDefEq.respectTransparency.types false in
lemma numberPower_graph_upper (r : ℝ) (hr : 0 < r) (u : (numberPower E r).domain) :
    ‖(u : lp E 2)‖^2 + ‖shiftedNumberPower E r (shiftedNumberInput E r hr u)‖^2 ≤
      (1+((2 : ℝ)^r)^2) * (‖(u : lp E 2)‖^2 + ‖numberPower E r u‖^2) := by
  have hu := (GW.Analysis.memℓp_two_iff_sq (fun n => (u : lp E 2) n)).mp (lp.memℓp (u : lp E 2))
  have hn : Summable (fun n : ℕ => ((n : ℝ)^r)^2 * ‖(u : lp E 2) n‖^2) := by
    have h := (numberPower_domain E r hr (u : lp E 2)).mp u.property
    simpa only [rpow_square _ _ (Nat.cast_nonneg _)] using h
  have hs := (scalarDiagonal_domain_iff E (fun n => ((n : ℝ)+1)^r)
    (u : lp E 2)).mp (shiftedNumberInput E r hr u).property
  have hmajor := (hu.add hn).mul_left (((2 : ℝ)^r)^2)
  have hb : ‖shiftedNumberPower E r (shiftedNumberInput E r hr u)‖^2 ≤
      ((2 : ℝ)^r)^2 * (‖(u : lp E 2)‖^2 + ‖numberPower E r u‖^2) := by
    change ‖scalarDiagonal E (fun n => ((n : ℝ)+1)^r) (shiftedNumberInput E r hr u)‖^2 ≤ _
    rw [scalarDiagonal_norm_sq]
    calc
      _ ≤ ∑' n : ℕ, ((2 : ℝ)^r)^2 * (‖(u : lp E 2) n‖^2 +
          ((n : ℝ)^r)^2 * ‖(u : lp E 2) n‖^2) := by
        apply hs.tsum_le_tsum _ hmajor
        intro n
        calc
          _ ≤ (((2 : ℝ)^r)^2 * (1+((n : ℝ)^r)^2)) * ‖(u : lp E 2) n‖^2 :=
            mul_le_mul_of_nonneg_right (number_weight_sq_bound n r hr.le) (sq_nonneg _)
          _ = _ := by ring
      _ = _ := by
        rw [tsum_mul_left,hu.tsum_add hn,← GW.Analysis.lp_norm_sq,
          ← numberPower_norm_sq E r (ne_of_gt hr) u]
  nlinarith [sq_nonneg ‖numberPower E r u‖]

end ScalarDiagonal

abbrev numberOperator : Carrier →ₗ.[ℂ] Carrier := numberDiagonal Sector
abbrev electronNumberOperator : ElectronBosonSum →ₗ.[ℂ] ElectronBosonSum := numberDiagonal ElectronSector
abbrev phononNumberPower (r : ℝ) : Carrier →ₗ.[ℂ] Carrier := numberPower Sector r
abbrev electronNumberPower (r : ℝ) : ElectronBosonSum →ₗ.[ℂ] ElectronBosonSum := numberPower ElectronSector r
abbrev phononShiftedNumberPower (r : ℝ) : Carrier →ₗ.[ℂ] Carrier := shiftedNumberPower Sector r
abbrev electronShiftedNumberPower (r : ℝ) : ElectronBosonSum →ₗ.[ℂ] ElectronBosonSum := shiftedNumberPower ElectronSector r
end GW.Fock
