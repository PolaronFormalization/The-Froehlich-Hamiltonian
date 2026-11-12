module
public import GW.Fock.FockProductTensors
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ENNReal
namespace GW.Fock

lemma diagonalTensor_fixed (n : ℕ) (g : OneBoson) (τ : Equiv.Perm (Fin n)) :
    permutationL2 n τ (rawTensor n (fun _ => g)) = rawTensor n (fun _ => g) := by
  apply Lp.ext
  filter_upwards [permutationL2_ae n τ (rawTensor n (fun _ => g)),
    (coordinatePermutation_preserving n τ).quasiMeasurePreserving.ae (rawTensor_ae n (fun _ => g)),
    rawTensor_ae n (fun _ => g)] with k h₁ h₂ h₃
  rw [h₁,h₂,h₃]
  simp only [rawTensorRep,coordinatePermutation_apply]
  exact Fintype.prod_equiv τ _ _ (fun _ => rfl)

/-- Concrete diagonal product in the existing symmetric sector, with literal scalar vacuum. -/
def tensorPower : (n : ℕ) → OneBoson → Sector n
  | 0,_ => (1 : ℂ)
  | n+1,g => ⟨rawTensor (n+1) (fun _ => g),fun τ => diagonalTensor_fixed (n+1) g τ⟩

lemma tensorPower_norm (n : ℕ) (g : OneBoson) : ‖tensorPower n g‖ = ‖g‖^n := by
  cases n with
  | zero =>
    change ‖(1 : ℂ)‖ = 1
    exact norm_one
  | succ n =>
    change ‖rawTensor (n+1) (fun _ => g)‖ = ‖g‖^(n+1)
    rw [rawTensor_norm]
    simp

def exponentialRaw (g : OneBoson) (n : ℕ) : Sector n :=
  (((Real.sqrt (n.factorial : ℝ))⁻¹ : ℝ) : ℂ) • tensorPower n g

lemma exponentialRaw_norm_sq (g : OneBoson) (n : ℕ) :
    ‖exponentialRaw g n‖^2 = (‖g‖^2)^n / (n.factorial : ℝ) := by
  change ‖(((Real.sqrt (n.factorial : ℝ))⁻¹ : ℝ) : ℂ) • tensorPower n g‖^2 = _
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_inv,abs_of_nonneg (Real.sqrt_nonneg _),
    tensorPower_norm,mul_pow,inv_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [← pow_mul,← pow_mul]
  simp only [mul_comm,div_eq_mul_inv]

lemma exponentialRaw_hasSum (g : OneBoson) : HasSum (fun n => ‖exponentialRaw g n‖^2) (Real.exp (‖g‖^2)) := by
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (‖g‖^2)
  convert h using 1
  · funext n
    rw [exponentialRaw_norm_sq]
    simp only [smul_eq_mul,div_eq_mul_inv,mul_comm]
  · exact congrFun Real.exp_eq_exp_ℝ _

/-- Bundle only after the concrete raw sequence's square-summability is proved. -/
def exponentialVector (g : OneBoson) : Carrier :=
  ⟨exponentialRaw g,(GW.Analysis.memℓp_two_iff_sq _).mpr (exponentialRaw_hasSum g).summable⟩

lemma exponentialVector_apply (g : OneBoson) (n : ℕ) : exponentialVector g n = exponentialRaw g n := rfl

lemma exponentialVector_norm_sq (g : OneBoson) : ‖exponentialVector g‖^2 = Real.exp (‖g‖^2) := by
  rw [carrier_norm_sq]
  exact (exponentialRaw_hasSum g).tsum_eq

def normalizedExponential (g : OneBoson) : Carrier :=
  ((Real.exp (-(‖g‖^2)/2) : ℝ) : ℂ) • exponentialVector g

lemma exponentialVector_vacuum (g : OneBoson) : exponentialVector g 0 = (1 : ℂ) := by
  change (((Real.sqrt ((0 : ℕ).factorial : ℝ))⁻¹ : ℝ) : ℂ) • (1 : ℂ) = _
  norm_num

lemma normalizedExponential_norm_sq (g : OneBoson) : ‖normalizedExponential g‖^2 = 1 := by
  change ‖((Real.exp (-(‖g‖^2)/2) : ℝ) : ℂ) • exponentialVector g‖^2 = 1
  rw [norm_smul,mul_pow,exponentialVector_norm_sq,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),pow_two,← Real.exp_add,← Real.exp_add]
  have he : (-(‖g‖^2)/2 + -(‖g‖^2)/2) + ‖g‖^2 = 0 := by ring
  rw [he,Real.exp_zero]

lemma normalizedExponential_norm (g : OneBoson) : ‖normalizedExponential g‖ = 1 := by
  have h := normalizedExponential_norm_sq g
  nlinarith [norm_nonneg (normalizedExponential g)]

def exponentialSpan (D : Submodule ℂ OneBoson) : Submodule ℂ Carrier :=
  Submodule.span ℂ {u | ∃ g : OneBoson, g ∈ D ∧ u = exponentialVector g}
end GW.Fock
