module
public import GW.Conventions
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
public import Mathlib.Tactic
@[expose] public section
noncomputable section
open MeasureTheory
open scoped Topology InnerProductSpace ENNReal
namespace GW.Fock

abbrev Coordinates (n : ℕ) := Fin n → GW.Space

def sectorMeasure (n : ℕ) : Measure (Coordinates n) :=
  Measure.pi (fun _ : Fin n => (volume : Measure GW.Space))

abbrev AmbientSector (n : ℕ) : Type := Lp ℂ 2 (sectorMeasure n)

/-- The source direction k ↦ k ∘ τ; the library reindexing uses τ.symm. -/
def coordinatePermutation (n : ℕ) (τ : Equiv.Perm (Fin n)) : Coordinates n ≃ᵐ Coordinates n :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin n => GW.Space) τ.symm

lemma coordinatePermutation_apply (n : ℕ) (τ : Equiv.Perm (Fin n)) (k : Coordinates n) (i : Fin n) :
    coordinatePermutation n τ k i = k (τ i) := by
  change MeasurableEquiv.piCongrLeft (fun _ : Fin n => GW.Space) τ.symm k i = k (τ i)
  simpa only [Equiv.symm_apply_apply] using MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin n => GW.Space) τ.symm k (τ i)

lemma coordinatePermutation_eq (n : ℕ) (τ : Equiv.Perm (Fin n)) (k : Coordinates n) :
    coordinatePermutation n τ k = (fun i => k (τ i)) :=
  funext (coordinatePermutation_apply n τ k)

lemma coordinatePermutation_preserving (n : ℕ) (τ : Equiv.Perm (Fin n)) :
    MeasurePreserving (coordinatePermutation n τ) (sectorMeasure n) (sectorMeasure n) :=
  measurePreserving_piCongrLeft (fun _ : Fin n => (volume : Measure GW.Space)) τ.symm

/-- Pullback on actual L² equivalence classes, not on chosen representatives. -/
def permutationL2 (n : ℕ) (τ : Equiv.Perm (Fin n)) : AmbientSector n →ₗᵢ[ℂ] AmbientSector n :=
  Lp.compMeasurePreservingₗᵢ ℂ (coordinatePermutation n τ) (coordinatePermutation_preserving n τ)

lemma permutationL2_ae (n : ℕ) (τ : Equiv.Perm (Fin n)) (u : AmbientSector n) :
    permutationL2 n τ u =ᵐ[sectorMeasure n] (fun k => u (coordinatePermutation n τ k)) :=
  Lp.coeFn_compMeasurePreserving u (coordinatePermutation_preserving n τ)

lemma permutation_fixed_iff (n : ℕ) (τ : Equiv.Perm (Fin n)) (u : AmbientSector n) :
    permutationL2 n τ u = u ↔ (fun k => u (coordinatePermutation n τ k)) =ᵐ[sectorMeasure n] u := by
  constructor
  · intro he
    have ha : (permutationL2 n τ u : Coordinates n → ℂ) =ᵐ[sectorMeasure n] u :=
      Filter.EventuallyEq.of_eq (congrArg (fun v : AmbientSector n => (v : Coordinates n → ℂ)) he)
    exact (permutationL2_ae n τ u).symm.trans ha
  · intro ha
    apply Lp.ext
    exact (permutationL2_ae n τ u).trans ha

def symmetricSubmodule (n : ℕ) : Submodule ℂ (AmbientSector n) where
  carrier := {u | ∀ τ : Equiv.Perm (Fin n), permutationL2 n τ u = u}
  zero_mem' := by intro τ; exact map_zero _
  add_mem' := by
    intro u v hu hv τ
    rw [map_add,hu τ,hv τ]
  smul_mem' := by
    intro c u hu τ
    rw [map_smul,hu τ]

def symmetricSector (n : ℕ) : ClosedSubmodule ℂ (AmbientSector n) where
  toSubmodule := symmetricSubmodule n
  isClosed' := by
    have he : (symmetricSubmodule n : Set (AmbientSector n)) =
        ⋂ τ : Equiv.Perm (Fin n), {u | permutationL2 n τ u = u} := by
      ext u
      simp only [SetLike.mem_coe,Set.mem_iInter,Set.mem_ofPred_eq]
      rfl
    change IsClosed (symmetricSubmodule n : Set (AmbientSector n))
    rw [he]
    exact isClosed_iInter (fun τ => isClosed_eq (permutationL2 n τ).continuous continuous_id)

lemma symmetricSector_mem_iff (n : ℕ) (u : AmbientSector n) :
    u ∈ symmetricSector n ↔ ∀ τ : Equiv.Perm (Fin n),
      (fun k => u (fun i => k (τ i))) =ᵐ[sectorMeasure n] u := by
  change (∀ τ, permutationL2 n τ u = u) ↔ _
  apply forall_congr'
  intro τ
  simpa only [coordinatePermutation_eq] using permutation_fixed_iff n τ u

/-- The vacuum is scalar ℂ, never definitionally an empty-product L² space. -/
def Sector : ℕ → Type
  | 0 => ℂ
  | n+1 => symmetricSector (n+1)

instance sectorNormedAddCommGroup (n : ℕ) : NormedAddCommGroup (Sector n) := by
  cases n with
  | zero => exact inferInstanceAs (NormedAddCommGroup ℂ)
  | succ n => exact inferInstanceAs (NormedAddCommGroup (symmetricSector (n+1)))

instance sectorInnerProductSpace (n : ℕ) : InnerProductSpace ℂ (Sector n) := by
  cases n with
  | zero => exact inferInstanceAs (InnerProductSpace ℂ ℂ)
  | succ n => exact inferInstanceAs (InnerProductSpace ℂ (symmetricSector (n+1)))

/-- Use the inner-product parent to keep every sector scalar action coherent. -/
instance sectorNormedSpace (n : ℕ) : NormedSpace ℂ (Sector n) :=
  (sectorInnerProductSpace n).toNormedSpace

instance sectorCompleteSpace (n : ℕ) : CompleteSpace (Sector n) := by
  cases n with
  | zero => exact inferInstanceAs (CompleteSpace ℂ)
  | succ n => exact inferInstanceAs (CompleteSpace (symmetricSector (n+1)))

abbrev Carrier : Type := lp Sector 2
abbrev ElectronSector (n : ℕ) : Type := Lp (Sector n) 2 (volume : Measure GW.Space)
abbrev ElectronBosonSum : Type := lp ElectronSector 2
/-- Fixed physical carrier; its unitary to ElectronBosonSum is a later source obligation. -/
abbrev Physical : Type := Lp Carrier 2 (volume : Measure GW.Space)

def vacuum : Carrier := lp.single 2 0 (1 : ℂ)

lemma vacuum_zero : vacuum 0 = (1 : ℂ) := lp.single_apply_self (E := Sector) 2 0 (1 : ℂ)

lemma vacuum_succ (n : ℕ) : vacuum (n+1) = 0 := lp.single_apply_ne (E := Sector) 2 0 (1 : ℂ) (Nat.succ_ne_zero n)
lemma vacuum_norm : ‖vacuum‖ = 1 := by
  have he := lp.norm_single (E := Sector) (by norm_num : (0 : ℝ≥0∞) < 2) 0 (1 : ℂ)
  apply he.trans
  change ‖(1 : ℂ)‖ = 1
  exact norm_one

lemma carrier_inner (u v : Carrier) : ⟪u,v⟫_ℂ = ∑' n, ⟪u n,v n⟫_ℂ := lp.inner_eq_tsum u v

lemma carrier_norm_sq (u : Carrier) : ‖u‖ ^ 2 = ∑' n, ‖u n‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (show 0 < (2 : ℝ≥0∞).toReal by norm_num) u
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using h

section Cutoffs
variable (E : ℕ → Type*) [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℂ (E n)]

/-- The finite sector projection on the specified dependent ℓ² family. -/
def cutoff (m : ℕ) : lp E 2 →L[ℂ] lp E 2 :=
  ∑ j ∈ Finset.range (m+1), (lp.singleContinuousLinearMap ℂ E 2 j).comp (lp.evalCLM ℂ E 2 j)

lemma cutoff_sum (m : ℕ) (u : lp E 2) : cutoff E m u =
    ∑ j ∈ Finset.range (m+1), lp.single 2 j (u j) := by
  simp only [cutoff,sum_apply,ContinuousLinearMap.comp_apply,
    lp.singleContinuousLinearMap_apply]
  rfl

lemma cutoff_apply (m : ℕ) (u : lp E 2) (n : ℕ) : cutoff E m u n = if n ≤ m then u n else 0 := by
  rw [cutoff_sum]
  simp only [lp.coeFn_sum,lp.coeFn_single,Finset.sum_apply,Finset.sum_pi_single,
    Finset.mem_range,Nat.lt_succ_iff]

lemma cutoff_norm_le (m : ℕ) (u : lp E 2) : ‖cutoff E m u‖ ≤ ‖u‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro n
  rw [cutoff_apply]
  split_ifs <;> simp only [le_refl,norm_zero,norm_nonneg]

lemma cutoff_opNorm_le (m : ℕ) : ‖cutoff E m‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa only [one_mul] using cutoff_norm_le E m u

lemma cutoff_idempotent (m : ℕ) : (cutoff E m).comp (cutoff E m) = cutoff E m := by
  ext u n
  change cutoff E m (cutoff E m u) n = cutoff E m u n
  by_cases hn : n ≤ m <;> simp [cutoff_apply,hn]

lemma cutoff_tendsto (u : lp E 2) : Filter.Tendsto (fun m => cutoff E m u) Filter.atTop (𝓝 u) := by
  have ht := (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) u).tendsto_sum_nat
  simpa only [cutoff_sum,Function.comp_def] using ht.comp (Filter.tendsto_add_atTop_nat 1)
end Cutoffs

abbrev P (m : ℕ) : Carrier →L[ℂ] Carrier := cutoff Sector m
abbrev electronP (m : ℕ) : ElectronBosonSum →L[ℂ] ElectronBosonSum := cutoff ElectronSector m

section HilbertCutoffs
variable (E : ℕ → Type*) [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℂ (E n)]

lemma cutoff_pairing (m : ℕ) (u v : lp E 2) : ⟪cutoff E m u,v⟫_ℂ = ⟪u,cutoff E m v⟫_ℂ := by
  rw [lp.inner_eq_tsum,lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  rw [cutoff_apply,cutoff_apply]
  by_cases hn : n ≤ m <;> simp [hn]
end HilbertCutoffs

lemma P_vacuum (m : ℕ) : P m vacuum = vacuum := by
  ext n
  change cutoff Sector m vacuum n = vacuum n
  cases n with
  | zero => simp [cutoff_apply]
  | succ n => simp only [cutoff_apply,vacuum_succ,ite_self]

lemma electron_inner (u v : ElectronBosonSum) : ⟪u,v⟫_ℂ = ∑' n, ⟪u n,v n⟫_ℂ := lp.inner_eq_tsum u v

lemma electron_norm_sq (u : ElectronBosonSum) : ‖u‖ ^ 2 = ∑' n, ‖u n‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (show 0 < (2 : ℝ≥0∞).toReal by norm_num) u
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using h

end GW.Fock
