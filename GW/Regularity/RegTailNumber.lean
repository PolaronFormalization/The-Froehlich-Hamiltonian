module
public import GW.Operators.BasicFree
public import GW.Fock.FockAmplification
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ENNReal
namespace GW.Fock

def highMomentumCount (R : ℝ) (n : ℕ) (k : Coordinates n) : ℝ :=
  ∑ j : Fin n, if R < ‖k j‖ then 1 else 0

lemma highMomentumCount_measurable (R : ℝ) (n : ℕ) : Measurable (highMomentumCount R n) := by
  apply Finset.measurable_sum
  intro j _
  exact measurable_const.ite (measurableSet_lt measurable_const (measurable_pi_apply j).norm) measurable_const

lemma highMomentumCount_nonneg (R : ℝ) (n : ℕ) (k : Coordinates n) :
    0 ≤ highMomentumCount R n k := by
  apply Finset.sum_nonneg
  intro j _
  split <;> norm_num

lemma highMomentumCount_le (R : ℝ) (n : ℕ) (k : Coordinates n) :
    highMomentumCount R n k ≤ n := by
  calc
    _ ≤ ∑ _j : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun j _ => by split <;> norm_num)
    _ = _ := by simp

lemma highMomentumCount_permutation (R : ℝ) (n : ℕ) (τ : Equiv.Perm (Fin n)) (k : Coordinates n) :
    highMomentumCount R n (coordinatePermutation n τ k) = highMomentumCount R n k := by
  simp only [highMomentumCount,coordinatePermutation_apply]
  exact Fintype.sum_equiv τ _ _ (fun _ => rfl)

def tailWeight (root : Bool) (R : ℝ) (n : ℕ) (k : Coordinates n) : ℝ :=
  if root then Real.sqrt (highMomentumCount R n k) else highMomentumCount R n k

def tailWeightBound (root : Bool) (n : ℕ) : ℝ :=
  if root then Real.sqrt n else n

lemma tailWeight_measurable (root : Bool) (R : ℝ) (n : ℕ) : Measurable (tailWeight root R n) := by
  cases root
  · exact highMomentumCount_measurable R n
  · exact Real.continuous_sqrt.measurable.comp (highMomentumCount_measurable R n)

lemma tailWeight_nonneg (root : Bool) (R : ℝ) (n : ℕ) (k : Coordinates n) :
    0 ≤ tailWeight root R n k := by
  cases root
  · exact highMomentumCount_nonneg R n k
  · exact Real.sqrt_nonneg _

lemma tailWeight_le (root : Bool) (R : ℝ) (n : ℕ) (k : Coordinates n) :
    tailWeight root R n k ≤ tailWeightBound root n := by
  cases root
  · exact highMomentumCount_le R n k
  · exact Real.sqrt_le_sqrt (highMomentumCount_le R n k)

lemma tailWeight_root_sq (R : ℝ) (n : ℕ) (k : Coordinates n) :
    tailWeight true R n k ^ 2 = tailWeight false R n k :=
  Real.sq_sqrt (highMomentumCount_nonneg R n k)

lemma tailWeight_permutation (root : Bool) (R : ℝ) (n : ℕ)
    (τ : Equiv.Perm (Fin n)) (k : Coordinates n) :
    tailWeight root R n (coordinatePermutation n τ k) = tailWeight root R n k := by
  simp only [tailWeight,highMomentumCount_permutation]

def tailAmbientMultiplier (root : Bool) (R : ℝ) (n : ℕ) : AmbientSector n →L[ℂ] AmbientSector n :=
  GW.Analysis.boundedMultiplier (fun k => (tailWeight root R n k : ℂ))
    (Complex.continuous_ofReal.measurable.comp (tailWeight_measurable root R n))
    (C := tailWeightBound root n) (Eventually.of_forall (fun k => by
      rw [Complex.norm_real,Real.norm_of_nonneg (tailWeight_nonneg root R n k)]
      exact tailWeight_le root R n k))

lemma tailAmbientMultiplier_ae (root : Bool) (R : ℝ) (n : ℕ) (u : AmbientSector n) :
    tailAmbientMultiplier root R n u =ᵐ[sectorMeasure n] fun k => (tailWeight root R n k : ℂ) • u k :=
  (GW.Analysis.boundedMultiplier_ae _ _ _ u).symm

lemma tailAmbientMultiplier_perm (root : Bool) (R : ℝ) (n : ℕ)
    (τ : Equiv.Perm (Fin n)) (u : AmbientSector n) :
    permutationL2 n τ (tailAmbientMultiplier root R n u) =
      tailAmbientMultiplier root R n (permutationL2 n τ u) := by
  apply Lp.ext
  filter_upwards [permutationL2_ae n τ (tailAmbientMultiplier root R n u),
    (coordinatePermutation_preserving n τ).quasiMeasurePreserving.ae (tailAmbientMultiplier_ae root R n u),
    tailAmbientMultiplier_ae root R n (permutationL2 n τ u),
    permutationL2_ae n τ u] with k h₁ h₂ h₃ h₄
  rw [h₁,h₂,h₃,h₄,tailWeight_permutation]

def tailSectorMultiplier (root : Bool) (R : ℝ) (n : ℕ) : Sector n →L[ℂ] Sector n :=
  match n with
  | 0 => 0
  | n+1 => ((tailAmbientMultiplier root R (n+1)).comp (sectorInclusion n).toContinuousLinearMap).codRestrict
      (symmetricSector (n+1)).toSubmodule (fun u τ => by
        change permutationL2 (n+1) τ (tailAmbientMultiplier root R (n+1) (sectorInclusion n u)) =
          tailAmbientMultiplier root R (n+1) (sectorInclusion n u)
        rw [tailAmbientMultiplier_perm]
        exact congrArg (tailAmbientMultiplier root R (n+1)) (u.property τ))

lemma tailSectorMultiplier_bound (root : Bool) (R : ℝ) (n : ℕ) (u : Sector n) :
    ‖tailSectorMultiplier root R n u‖ ≤ tailWeightBound root n * ‖u‖ := by
  cases n with
  | zero => cases root <;> simp [tailSectorMultiplier,tailWeightBound]
  | succ n =>
    change ‖tailAmbientMultiplier root R (n+1) (sectorInclusion n u)‖ ≤
      tailWeightBound root (n+1) * ‖sectorInclusion n u‖
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [tailAmbientMultiplier_ae root R (n+1) (sectorInclusion n u)] with k hk
    rw [hk,norm_smul,Complex.norm_real,Real.norm_of_nonneg (tailWeight_nonneg root R (n+1) k)]
    exact mul_le_mul_of_nonneg_right (tailWeight_le root R (n+1) k) (norm_nonneg _)

def tailElectronSectorMultiplier (root : Bool) (R : ℝ) (n : ℕ) :
    ElectronSector n →L[ℂ] ElectronSector n :=
  amplify volume (tailSectorMultiplier root R n)

lemma tailElectronSectorMultiplier_bound (root : Bool) (R : ℝ) (n : ℕ) (u : ElectronSector n) :
    ‖tailElectronSectorMultiplier root R n u‖ ≤ tailWeightBound root n * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [amplify_ae volume (tailSectorMultiplier root R n) u] with x hx
  change tailElectronSectorMultiplier root R n u x = tailSectorMultiplier root R n (u x) at hx
  rw [hx]
  exact tailSectorMultiplier_bound root R n (u x)

def tailElectronSectorOperator (root : Bool) (R : ℝ) (n : ℕ) :
    ElectronSector n →ₗ.[ℂ] ElectronSector n :=
  (tailElectronSectorMultiplier root R n).toLinearMap.toPMap ⊤

lemma tailElectronSectorOperator_graph (root : Bool) (R : ℝ) (n : ℕ) (u v : ElectronSector n) :
    (u,v) ∈ (tailElectronSectorOperator root R n).graph ↔ v = tailElectronSectorMultiplier root R n u := by
  rw [LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨w,hw,hv⟩
    have he : tailElectronSectorMultiplier root R n (w : ElectronSector n) = v := hv
    exact (he.symm.trans (congrArg (tailElectronSectorMultiplier root R n) hw))
  · intro hv
    exact ⟨⟨u,Submodule.mem_top⟩,rfl,hv.symm⟩

def tailNumberOperator (root : Bool) (R : ℝ) : Physical →ₗ.[ℂ] Physical :=
  representationTransport electronBosonUnitary.symm (operatorSum ElectronSector (tailElectronSectorOperator root R))

lemma tailNumberOperator_graph (root : Bool) (R : ℝ) (u v : Physical) :
    (u,v) ∈ (tailNumberOperator root R).graph ↔
      ∀ n, electronBosonUnitary.symm v n = tailElectronSectorMultiplier root R n (electronBosonUnitary.symm u n) := by
  change (u,v) ∈ (representationTransport electronBosonUnitary.symm
    (operatorSum ElectronSector (tailElectronSectorOperator root R))).graph ↔ _
  rw [representationTransport_graph,operatorSum_graph_iff]
  exact forall_congr' (fun n => tailElectronSectorOperator_graph root R n _ _)

lemma tailNumberOperator_domain (root : Bool) (R : ℝ) (u : Physical) :
    u ∈ (tailNumberOperator root R).domain ↔
      Summable (fun n => ‖tailElectronSectorMultiplier root R n (electronBosonUnitary.symm u n)‖^2) := by
  rw [LinearPMap.mem_domain_iff]
  constructor
  · rintro ⟨v,hv⟩
    have he : (fun n => ‖electronBosonUnitary.symm v n‖^2) =
        fun n => ‖tailElectronSectorMultiplier root R n (electronBosonUnitary.symm u n)‖^2 :=
      funext (fun n => congrArg (fun z : ElectronSector n => ‖z‖^2)
        ((tailNumberOperator_graph root R u v).mp hv n))
    exact he ▸ (GW.Analysis.memℓp_two_iff_sq _).mp (electronBosonUnitary.symm v).property
  · intro hs
    let w : ElectronBosonSum := ⟨fun n => tailElectronSectorMultiplier root R n (electronBosonUnitary.symm u n),
      (GW.Analysis.memℓp_two_iff_sq _).mpr hs⟩
    refine ⟨electronBosonUnitary w,(tailNumberOperator_graph root R _ _).mpr ?_⟩
    rw [LinearIsometryEquiv.symm_apply_apply]
    exact fun _ => rfl

lemma tailNumberOperator_action (root : Bool) (R : ℝ) (u : (tailNumberOperator root R).domain) (n : ℕ) :
    electronBosonUnitary.symm (tailNumberOperator root R u) n =
      tailElectronSectorMultiplier root R n (electronBosonUnitary.symm (u : Physical) n) :=
  (tailNumberOperator_graph root R _ _).mp ((tailNumberOperator root R).mem_graph u) n

abbrev highMomentumNumber (R : ℝ) := tailNumberOperator false R
abbrev highMomentumNumberRoot (R : ℝ) := tailNumberOperator true R

lemma highMomentumNumberRoot_domain (R : ℝ) : (physicalNumberPower (1/2)).domain ≤ (highMomentumNumberRoot R).domain := by
  intro u hu
  let w := electronBosonUnitary.symm u
  have hw : Memℓp (fun n => (numberPowerCoefficient (1/2) n : ℂ) • w n) 2 := hu
  have hs := (GW.Analysis.memℓp_two_iff_sq _).mp hw
  apply (tailNumberOperator_domain true R u).mpr
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ hs
  intro n
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  calc
    _ ≤ tailWeightBound true n * ‖w n‖ := tailElectronSectorMultiplier_bound true R n (w n)
    _ = ‖(numberPowerCoefficient (1/2) n : ℂ) • w n‖ := by
      have he : numberPowerCoefficient (1/2) n = Real.sqrt n := by
        simp [numberPowerCoefficient,Real.sqrt_eq_rpow]
      rw [norm_smul,he,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      rfl

lemma tailSectorMultiplier_value (root : Bool) (R : ℝ) (n : ℕ) (u : Sector (n+1)) :
    sectorInclusion n (tailSectorMultiplier root R (n+1) u) =
      tailAmbientMultiplier root R (n+1) (sectorInclusion n u) := rfl

lemma tailElectronSectorMultiplier_ae (root : Bool) (R : ℝ) (n : ℕ) (u : ElectronSector (n+1)) :
    ∀ᵐ x ∂(volume : Measure GW.Space), ∀ᵐ k ∂sectorMeasure (n+1),
      sectorInclusion n (tailElectronSectorMultiplier root R (n+1) u x) k =
        (tailWeight root R (n+1) k : ℂ) • sectorInclusion n (u x) k := by
  filter_upwards [amplify_ae volume (tailSectorMultiplier root R (n+1)) u] with x hx
  change tailElectronSectorMultiplier root R (n+1) u x = tailSectorMultiplier root R (n+1) (u x) at hx
  rw [hx,tailSectorMultiplier_value]
  exact tailAmbientMultiplier_ae root R (n+1) (sectorInclusion n (u x))

lemma tailElectronSectorMultiplier_vacuum (root : Bool) (R : ℝ) (u : ElectronSector 0) :
    tailElectronSectorMultiplier root R 0 u = 0 := by
  apply Lp.ext
  filter_upwards [amplify_ae volume (tailSectorMultiplier root R 0) u,
    Lp.coeFn_zero (Sector 0) 2 (volume : Measure GW.Space)] with x hx hz
  exact hx.trans hz.symm

lemma tailNumberOperator_action_ae (root : Bool) (R : ℝ) (u : (tailNumberOperator root R).domain) (n : ℕ) :
    ∀ᵐ x ∂(volume : Measure GW.Space), ∀ᵐ k ∂sectorMeasure (n+1),
      sectorInclusion n (electronBosonUnitary.symm (tailNumberOperator root R u) (n+1) x) k =
        (tailWeight root R (n+1) k : ℂ) • sectorInclusion n (electronBosonUnitary.symm (u : Physical) (n+1) x) k := by
  rw [tailNumberOperator_action]
  exact tailElectronSectorMultiplier_ae root R n (electronBosonUnitary.symm (u : Physical) (n+1))

lemma tailNumberOperator_action_vacuum (root : Bool) (R : ℝ) (u : (tailNumberOperator root R).domain) :
    electronBosonUnitary.symm (tailNumberOperator root R u) 0 = 0 :=
  (tailNumberOperator_action root R u 0).trans
    (tailElectronSectorMultiplier_vacuum root R (electronBosonUnitary.symm (u : Physical) 0))

end GW.Fock
