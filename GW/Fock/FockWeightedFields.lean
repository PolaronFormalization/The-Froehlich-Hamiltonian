module
public import GW.Fock.FockGeneralizedBounds
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace GW.Fock

lemma annihilationShiftedWeight (r : ℝ) (hr : 0 ≤ r) (n : ℕ) :
    ((n:ℝ)+1)^r * Real.sqrt (n+1:ℕ) ≤ (((n+1:ℕ):ℝ)+1)^(r+1/2) := by
  have hbase : 1 ≤ (n:ℝ)+1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
  rw [Nat.cast_add,Nat.cast_one,Real.sqrt_eq_rpow,← Real.rpow_add (zero_lt_one.trans_le hbase)]
  exact Real.rpow_le_rpow (zero_le_one.trans hbase) (le_add_of_nonneg_right zero_le_one) (by linarith)

lemma creationShiftedWeight (r : ℝ) (hr : 0 ≤ r) (n : ℕ) :
    (((n+1:ℕ):ℝ)+1)^r * Real.sqrt (n+1:ℕ) ≤ (2:ℝ)^r * ((n:ℝ)+1)^(r+1/2) := by
  have hbase : 1 ≤ (n:ℝ)+1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hscale : (n:ℝ)+1+1 ≤ 2*((n:ℝ)+1) := by linarith
  rw [Nat.cast_add,Nat.cast_one,Real.sqrt_eq_rpow]
  calc
    _ ≤ (2*((n:ℝ)+1))^r * ((n:ℝ)+1)^(1/2:ℝ) := by
      refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by positivity) hscale hr)
        (Real.rpow_nonneg (zero_le_one.trans hbase) _)
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (zero_le_one.trans hbase),mul_assoc,
        ← Real.rpow_add (zero_lt_one.trans_le hbase)]

section SectorWeights
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {G : ℕ → Type*} [∀ n, NormedAddCommGroup (G n)] [∀ n, InnerProductSpace ℂ (G n)]
  (R : ∀ n, G n ≃ₗᵢ[ℂ] kernelFixed (E := E) n) (F : BosonKernel E)

lemma shiftedNumberDomain_mono {a b : ℝ} (hab : a ≤ b) :
    (shiftedNumberPower G b).domain ≤ (shiftedNumberPower G a).domain := by
  intro u hu
  have h := (shiftedNumberPower_domain G b u).mp hu
  apply (shiftedNumberPower_domain G a u).mpr
  apply Summable.of_nonneg_of_le _ _ h
  · intro n; positivity
  · intro n
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_left (Nat.cast_nonneg n))
    linarith

def shiftedRootSectorInput {r : ℝ} (hr : 0 ≤ r) (u : (shiftedNumberPower G (r+1/2)).domain) :
    (shiftedNumberPower G (1/2)).domain :=
  ⟨u,shiftedNumberDomain_mono (by linarith) u.property⟩

def rootSectorInputOfShifted {r : ℝ} (hr : 0 ≤ r) (u : (shiftedNumberPower G (r+1/2)).domain) :
    (numberPower G (1/2)).domain :=
  ⟨u,by
    rw [numberPower_domain_eq G (1/2) (by norm_num)]
    exact (shiftedRootSectorInput hr u).property⟩

def weightedCreationSectorInput (r : ℝ) (hr : 0 ≤ r) (u : (shiftedNumberPower G (r+1/2)).domain) :
    (maximalSectorCreation (sectorCreation R F)).domain :=
  ⟨u,creation_mem_shiftedRoot R F (shiftedRootSectorInput hr u)⟩

def weightedAnnihilationSectorInput (r : ℝ) (hr : 0 ≤ r) (u : (shiftedNumberPower G (r+1/2)).domain) :
    (maximalSectorAnnihilation (sectorAnnihilation R F)).domain :=
  ⟨u,annihilation_mem_root R F (rootSectorInputOfShifted hr u)⟩

lemma weightedCreationCoordinate_bound (r : ℝ) (hr : 0 ≤ r) (u : (shiftedNumberPower G (r+1/2)).domain) (n : ℕ) :
    ‖(((((n+1:ℕ):ℝ)+1)^r : ℝ) : ℂ) •
        sectorCreation R F n ((u : lp G 2) n)‖ ≤
      ((2:ℝ)^r*‖F‖) * ‖shiftedNumberPower G (r+1/2) u n‖ := by
  rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _),
    shiftedNumberPower_apply,norm_smul,Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  have hb := ((sectorCreation R F n).le_opNorm ((u : lp G 2) n)).trans
    (mul_le_mul_of_nonneg_right (sectorCreation_norm R F n) (norm_nonneg _))
  refine (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg (by positivity) _)).trans ?_
  have h := mul_le_mul_of_nonneg_right (creationShiftedWeight r hr n)
    (mul_nonneg F.opNorm_nonneg (norm_nonneg ((u : lp G 2) n)))
  convert h using 1 <;> ring

lemma weightedAnnihilationCoordinate_bound (r : ℝ) (hr : 0 ≤ r) (u : (shiftedNumberPower G (r+1/2)).domain) (n : ℕ) :
    ‖(((((n:ℝ)+1)^r : ℝ)) : ℂ) •
        sectorAnnihilation R F n ((u : lp G 2) (n+1))‖ ≤
      ‖F‖ * ‖shiftedNumberPower G (r+1/2) u (n+1)‖ := by
  rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _),
    shiftedNumberPower_apply,norm_smul,Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  have hb := ((sectorAnnihilation R F n).le_opNorm ((u : lp G 2) (n+1))).trans
    (mul_le_mul_of_nonneg_right (sectorAnnihilation_norm R F n) (norm_nonneg _))
  refine (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg (by positivity) _)).trans ?_
  have h := mul_le_mul_of_nonneg_right (annihilationShiftedWeight r hr n)
    (mul_nonneg F.opNorm_nonneg (norm_nonneg ((u : lp G 2) (n+1))))
  convert h using 1 <;> ring

lemma weightedCreationSector_mem (r : ℝ) (hr : 0 ≤ r)
    (u : (shiftedNumberPower G (r+1/2)).domain) :
    maximalSectorCreation (sectorCreation R F) (weightedCreationSectorInput R F r hr u) ∈
      (shiftedNumberPower G r).domain := by
  let v := maximalSectorCreation (sectorCreation R F) (weightedCreationSectorInput R F r hr u)
  let w := shiftedNumberPower G (r+1/2) u
  let K := (2:ℝ)^r * ‖F‖
  change Memℓp (fun n : ℕ => ((((n:ℝ)+1)^r : ℝ) : ℂ) • v n) 2
  apply (GW.Analysis.memℓp_two_iff_sq _).mpr
  apply (summable_nat_add_iff 1).mp
  have hw : Summable (fun n => ‖w n‖^2) := (GW.Analysis.memℓp_two_iff_sq _).mp w.property
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ (hw.mul_left (K^2))
  intro n
  rw [← mul_pow]
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  have h : v (n+1) = sectorCreation R F n ((u : lp G 2) n) :=
    maximalSectorCreation_succ _ _ n
  rw [h]
  exact weightedCreationCoordinate_bound R F r hr u n

lemma weightedAnnihilationSector_mem (r : ℝ) (hr : 0 ≤ r)
    (u : (shiftedNumberPower G (r+1/2)).domain) :
    maximalSectorAnnihilation (sectorAnnihilation R F) (weightedAnnihilationSectorInput R F r hr u) ∈
      (shiftedNumberPower G r).domain := by
  let v := maximalSectorAnnihilation (sectorAnnihilation R F) (weightedAnnihilationSectorInput R F r hr u)
  let w := shiftedNumberPower G (r+1/2) u
  change Memℓp (fun n : ℕ => ((((n:ℝ)+1)^r : ℝ) : ℂ) • v n) 2
  apply (GW.Analysis.memℓp_two_iff_sq _).mpr
  have hw : Summable (fun n => ‖w n‖^2) := (GW.Analysis.memℓp_two_iff_sq _).mp w.property
  have hw' : Summable (fun n => ‖w (n+1)‖^2) := (summable_nat_add_iff 1).mpr hw
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ (hw'.mul_left (‖F‖^2))
  intro n
  rw [← mul_pow]
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  have h : v n = sectorAnnihilation R F n ((u : lp G 2) (n+1)) :=
    maximalSectorAnnihilation_apply _ _ n
  rw [h]
  exact weightedAnnihilationCoordinate_bound R F r hr u n

def weightedCreationSectorOutput (r : ℝ) (hr : 0 ≤ r)
    (u : (shiftedNumberPower G (r+1/2)).domain) : (shiftedNumberPower G r).domain :=
  ⟨maximalSectorCreation (sectorCreation R F) (weightedCreationSectorInput R F r hr u),
    weightedCreationSector_mem R F r hr u⟩

def weightedAnnihilationSectorOutput (r : ℝ) (hr : 0 ≤ r)
    (u : (shiftedNumberPower G (r+1/2)).domain) : (shiftedNumberPower G r).domain :=
  ⟨maximalSectorAnnihilation (sectorAnnihilation R F) (weightedAnnihilationSectorInput R F r hr u),
    weightedAnnihilationSector_mem R F r hr u⟩

lemma weightedCreationSector_norm (r : ℝ) (hr : 0 ≤ r)
    (u : (shiftedNumberPower G (r+1/2)).domain) :
    ‖shiftedNumberPower G r (weightedCreationSectorOutput R F r hr u)‖ ≤
      ((2:ℝ)^r*‖F‖) * ‖shiftedNumberPower G (r+1/2) u‖ := by
  let v := shiftedNumberPower G r (weightedCreationSectorOutput R F r hr u)
  let w := shiftedNumberPower G (r+1/2) u
  change ‖v‖ ≤ _ * ‖w‖
  apply sector_norm_from_shifted_bounds v w (mul_nonneg (Real.rpow_nonneg (by norm_num) _) F.opNorm_nonneg)
  · change (((((0:ℕ):ℝ)+1)^r : ℝ) : ℂ) •
      maximalSectorCreation (sectorCreation R F) (weightedCreationSectorInput R F r hr u) 0 = 0
    rw [maximalSectorCreation_zero,smul_zero]
  · intro n
    change ‖(((((n+1:ℕ):ℝ)+1)^r : ℝ) : ℂ) •
      maximalSectorCreation (sectorCreation R F) (weightedCreationSectorInput R F r hr u) (n+1)‖ ≤ _
    rw [maximalSectorCreation_succ]
    exact weightedCreationCoordinate_bound R F r hr u n

lemma weightedAnnihilationSector_norm (r : ℝ) (hr : 0 ≤ r)
    (u : (shiftedNumberPower G (r+1/2)).domain) :
    ‖shiftedNumberPower G r (weightedAnnihilationSectorOutput R F r hr u)‖ ≤
      ‖F‖ * ‖shiftedNumberPower G (r+1/2) u‖ := by
  let v := shiftedNumberPower G r (weightedAnnihilationSectorOutput R F r hr u)
  let w := shiftedNumberPower G (r+1/2) u
  change ‖v‖ ≤ ‖F‖ * ‖w‖
  apply (sq_le_sq₀ (norm_nonneg v) (mul_nonneg F.opNorm_nonneg (norm_nonneg w))).mp
  have hv : Summable (fun n => ‖v n‖^2) := (GW.Analysis.memℓp_two_iff_sq _).mp v.property
  have hw : Summable (fun n => ‖w n‖^2) := (GW.Analysis.memℓp_two_iff_sq _).mp w.property
  have hw' : Summable (fun n => ‖w (n+1)‖^2) := (summable_nat_add_iff 1).mpr hw
  rw [GW.Analysis.lp_norm_sq,mul_pow,GW.Analysis.lp_norm_sq]
  calc
    _ ≤ ∑' n, ‖F‖^2 * ‖w (n+1)‖^2 := by
      apply Summable.tsum_le_tsum _ hv (hw'.mul_left _)
      intro n
      rw [← mul_pow]
      apply pow_le_pow_left₀ (norm_nonneg _) _ 2
      change ‖((((n:ℝ)+1)^r : ℝ) : ℂ) •
        maximalSectorAnnihilation (sectorAnnihilation R F) (weightedAnnihilationSectorInput R F r hr u) n‖ ≤ _
      rw [maximalSectorAnnihilation_apply]
      exact weightedAnnihilationCoordinate_bound R F r hr u n
    _ = ‖F‖^2 * (∑' n, ‖w (n+1)‖^2) := tsum_mul_left
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      rw [hw.tsum_eq_zero_add]
      exact le_add_of_nonneg_left (sq_nonneg _)

end SectorWeights
section PhysicalWeights

def physicalShiftedSectorInput (r : ℝ) (u : (physicalShiftedNumberPower r).domain) :
    (shiftedNumberPower ElectronSector r).domain :=
  ⟨electronBosonUnitary.symm u.val,u.property⟩

def physicalShiftedSectorOutput (r : ℝ) (v : (shiftedNumberPower ElectronSector r).domain) :
    (physicalShiftedNumberPower r).domain :=
  ⟨electronBosonUnitary v.val,bochnerShiftedNumberPower_unitary_mem volume Sector r v⟩

lemma physicalShiftedSectorOutput_norm (r : ℝ) (v : (shiftedNumberPower ElectronSector r).domain) :
    ‖physicalShiftedNumberPower r (physicalShiftedSectorOutput r v)‖ =
      ‖shiftedNumberPower ElectronSector r v‖ := by
  have h := bochnerShiftedNumberPower_intertwines volume Sector r v
  exact (congrArg norm h).trans (electronBosonUnitary.norm_map _)

lemma physicalShiftedSectorInput_norm (r : ℝ) (u : (physicalShiftedNumberPower r).domain) :
    ‖physicalShiftedNumberPower r u‖ = ‖shiftedNumberPower ElectronSector r (physicalShiftedSectorInput r u)‖ :=
  bochnerDiagonal_norm_eq (fun n => ((n:ℝ)+1)^r) u (physicalShiftedSectorInput r u) rfl

def physicalWeightedCreationInput (F : BosonKernel ElectronL2) (r : ℝ) (hr : 0 ≤ r)
    (u : (physicalShiftedNumberPower (r+1/2)).domain) : (generalizedCreation F).domain :=
  ⟨u.val,(weightedCreationSectorInput physicalSectorKernel F r hr (physicalShiftedSectorInput _ u)).property⟩

def physicalWeightedAnnihilationInput (F : BosonKernel ElectronL2) (r : ℝ) (hr : 0 ≤ r)
    (u : (physicalShiftedNumberPower (r+1/2)).domain) : (generalizedAnnihilation F).domain :=
  ⟨u.val,(weightedAnnihilationSectorInput physicalSectorKernel F r hr (physicalShiftedSectorInput _ u)).property⟩

def physicalWeightedCreationOutput (F : BosonKernel ElectronL2) (r : ℝ) (hr : 0 ≤ r)
    (u : (physicalShiftedNumberPower (r+1/2)).domain) : (physicalShiftedNumberPower r).domain :=
  physicalShiftedSectorOutput r (weightedCreationSectorOutput physicalSectorKernel F r hr (physicalShiftedSectorInput _ u))

def physicalWeightedAnnihilationOutput (F : BosonKernel ElectronL2) (r : ℝ) (hr : 0 ≤ r)
    (u : (physicalShiftedNumberPower (r+1/2)).domain) : (physicalShiftedNumberPower r).domain :=
  physicalShiftedSectorOutput r (weightedAnnihilationSectorOutput physicalSectorKernel F r hr (physicalShiftedSectorInput _ u))

lemma physicalWeightedCreationOutput_action (F : BosonKernel ElectronL2) (r : ℝ) (hr : 0 ≤ r)
    (u : (physicalShiftedNumberPower (r+1/2)).domain) :
    (physicalWeightedCreationOutput F r hr u).val =
      generalizedCreation F (physicalWeightedCreationInput F r hr u) := rfl

lemma physicalWeightedAnnihilationOutput_action (F : BosonKernel ElectronL2) (r : ℝ) (hr : 0 ≤ r)
    (u : (physicalShiftedNumberPower (r+1/2)).domain) :
    (physicalWeightedAnnihilationOutput F r hr u).val =
      generalizedAnnihilation F (physicalWeightedAnnihilationInput F r hr u) := rfl

lemma physicalWeightedCreation_norm (F : BosonKernel ElectronL2) (r : ℝ) (hr : 0 ≤ r)
    (u : (physicalShiftedNumberPower (r+1/2)).domain) :
    ‖physicalShiftedNumberPower r (physicalWeightedCreationOutput F r hr u)‖ ≤
      ((2:ℝ)^r*‖F‖) * ‖physicalShiftedNumberPower (r+1/2) u‖ := by
  change ‖physicalShiftedNumberPower r (physicalShiftedSectorOutput r _)‖ ≤ _
  rw [physicalShiftedSectorOutput_norm,physicalShiftedSectorInput_norm]
  exact weightedCreationSector_norm physicalSectorKernel F r hr (physicalShiftedSectorInput _ u)

lemma physicalWeightedAnnihilation_norm (F : BosonKernel ElectronL2) (r : ℝ) (hr : 0 ≤ r)
    (u : (physicalShiftedNumberPower (r+1/2)).domain) :
    ‖physicalShiftedNumberPower r (physicalWeightedAnnihilationOutput F r hr u)‖ ≤
      ‖F‖ * ‖physicalShiftedNumberPower (r+1/2) u‖ := by
  change ‖physicalShiftedNumberPower r (physicalShiftedSectorOutput r _)‖ ≤ _
  rw [physicalShiftedSectorOutput_norm,physicalShiftedSectorInput_norm]
  exact weightedAnnihilationSector_norm physicalSectorKernel F r hr (physicalShiftedSectorInput _ u)

end PhysicalWeights
section WeightedRestriction
variable {H U V : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup U] [InnerProductSpace ℂ U] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  (T : H →ₗ.[ℂ] H) (G : GW.Spaces.WeightedGraph H U) (K : GW.Spaces.WeightedGraph H V)
  (hG : G.domain ≤ T.domain) (hK : ∀ u : G.domain, T ⟨u.val,hG u.property⟩ ∈ K.domain)

def weightedRestrictionLinear : GW.Spaces.WeightedDomain G →ₗ[ℂ] GW.Spaces.WeightedDomain K :=
  (T.toFun.comp (Submodule.inclusion hG)).codRestrict K.domain hK

lemma weightedRestrictionLinear_value (u : GW.Spaces.WeightedDomain G) :
    (show K.domain from weightedRestrictionLinear T G K hG hK u).val =
      T ⟨(show G.domain from u).val,hG (show G.domain from u).property⟩ := rfl

def weightedRestriction (C : ℝ)
    (h : ∀ u : G.domain, ‖K.product ⟨T ⟨u.val,hG u.property⟩,hK u⟩‖ ≤ C*‖G.product u‖) :
    GW.Spaces.WeightedDomain G →L[ℂ] GW.Spaces.WeightedDomain K :=
  (weightedRestrictionLinear T G K hG hK).mkContinuous C (fun u => h u)

end WeightedRestriction

abbrev physicalShiftedWeightGraph (r : ℝ) (hr : 0 ≤ r) :=
  bochnerWeightedGraph (volume : Measure GW.Space) Sector (fun n => ((n:ℝ)+1)^r)
    (shiftedNumber_weight_one r hr)

lemma physicalWeightedCreation_mem (F : BosonKernel ElectronL2) (r : ℝ) (hr : 0 ≤ r)
    (u : (physicalShiftedNumberPower (r+1/2)).domain) :
    generalizedCreation F (physicalWeightedCreationInput F r hr u) ∈ (physicalShiftedNumberPower r).domain :=
  (physicalWeightedCreationOutput_action F r hr u) ▸ (physicalWeightedCreationOutput F r hr u).property

lemma physicalWeightedAnnihilation_mem (F : BosonKernel ElectronL2) (r : ℝ) (hr : 0 ≤ r)
    (u : (physicalShiftedNumberPower (r+1/2)).domain) :
    generalizedAnnihilation F (physicalWeightedAnnihilationInput F r hr u) ∈ (physicalShiftedNumberPower r).domain :=
  (physicalWeightedAnnihilationOutput_action F r hr u) ▸ (physicalWeightedAnnihilationOutput F r hr u).property

def physicalWeightedCreation (F : BosonKernel ElectronL2) (r : ℝ) (hr : 0 ≤ r) :
    PhysicalNumberDomain (r+1/2) (by linarith) →L[ℂ] PhysicalNumberDomain r hr := by
  let G := physicalShiftedWeightGraph (r+1/2) (by linarith)
  let K := physicalShiftedWeightGraph r hr
  let T := generalizedCreation F
  have hG : G.domain ≤ T.domain := fun u hu => (physicalWeightedCreationInput F r hr ⟨u,hu⟩).property
  have hK (u : G.domain) : T ⟨u.val,hG u.property⟩ ∈ K.domain := physicalWeightedCreation_mem F r hr u
  refine weightedRestriction T G K hG hK ((2:ℝ)^r*‖F‖) (fun u => ?_)
  let v := physicalWeightedCreationOutput F r hr u
  have he : (⟨T ⟨u.val,hG u.property⟩,hK u⟩ : K.domain) = v :=
    Subtype.ext (physicalWeightedCreationOutput_action F r hr u).symm
  rw [he]
  exact physicalWeightedCreation_norm F r hr u

def physicalWeightedAnnihilation (F : BosonKernel ElectronL2) (r : ℝ) (hr : 0 ≤ r) :
    PhysicalNumberDomain (r+1/2) (by linarith) →L[ℂ] PhysicalNumberDomain r hr := by
  let G := physicalShiftedWeightGraph (r+1/2) (by linarith)
  let K := physicalShiftedWeightGraph r hr
  let T := generalizedAnnihilation F
  have hG : G.domain ≤ T.domain := fun u hu => (physicalWeightedAnnihilationInput F r hr ⟨u,hu⟩).property
  have hK (u : G.domain) : T ⟨u.val,hG u.property⟩ ∈ K.domain := physicalWeightedAnnihilation_mem F r hr u
  refine weightedRestriction T G K hG hK ‖F‖ (fun u => ?_)
  let v := physicalWeightedAnnihilationOutput F r hr u
  have he : (⟨T ⟨u.val,hG u.property⟩,hK u⟩ : K.domain) = v :=
    Subtype.ext (physicalWeightedAnnihilationOutput_action F r hr u).symm
  rw [he]
  exact physicalWeightedAnnihilation_norm F r hr u

def EveryOrdinaryNumberDomain (u : Carrier) : Prop :=
  ∀ r : ℝ, 0 ≤ r → u ∈ (shiftedNumberPower Sector r).domain

lemma everyOrdinaryNumberDomain_iff (u : Carrier) :
    EveryOrdinaryNumberDomain u ↔ ∀ r : ℝ, 0 ≤ r → u ∈ (numberPower Sector r).domain := by
  unfold EveryOrdinaryNumberDomain
  apply forall_congr'
  intro r
  constructor <;> intro h hr
  · rcases hr.eq_or_lt with (rfl | hp)
    · rw [numberPower_zero,LinearMap.toPMap_domain]
      exact Submodule.mem_top
    · rw [numberPower_domain_eq Sector r hp]
      exact h hp.le
  · rcases hr.eq_or_lt with (rfl | hp)
    · rw [shiftedNumberPower_zero,LinearMap.toPMap_domain]
      exact Submodule.mem_top
    · rw [← numberPower_domain_eq Sector r hp]
      exact h hp.le

abbrev EveryOrdinaryNumberVector := {u : Carrier // EveryOrdinaryNumberDomain u}

def ordinaryCreationAllInput (f : OneBoson) (u : EveryOrdinaryNumberVector) : (ordinaryCreation f).domain :=
  weightedCreationSectorInput ordinarySectorKernel (ordinaryKernel f) 0 le_rfl
    ⟨u.val,u.property (0+1/2) (by norm_num)⟩

def ordinaryAnnihilationAllInput (f : OneBoson) (u : EveryOrdinaryNumberVector) :
    (ordinaryAnnihilation f).domain :=
  weightedAnnihilationSectorInput ordinarySectorKernel (ordinaryKernel f) 0 le_rfl
    ⟨u.val,u.property (0+1/2) (by norm_num)⟩

def ordinaryCreationAll (f : OneBoson) (u : EveryOrdinaryNumberVector) : EveryOrdinaryNumberVector := by
  refine ⟨ordinaryCreation f (ordinaryCreationAllInput f u),?_⟩
  intro r hr
  let x : (shiftedNumberPower Sector (r+1/2)).domain := ⟨u.val,u.property _ (by linarith)⟩
  let y : (ordinaryCreation f).domain := weightedCreationSectorInput ordinarySectorKernel (ordinaryKernel f) r hr x
  have he : ordinaryCreationAllInput f u = y := Subtype.ext rfl
  rw [he]
  exact weightedCreationSector_mem ordinarySectorKernel (ordinaryKernel f) r hr x

def ordinaryAnnihilationAll (f : OneBoson) (u : EveryOrdinaryNumberVector) : EveryOrdinaryNumberVector := by
  refine ⟨ordinaryAnnihilation f (ordinaryAnnihilationAllInput f u),?_⟩
  intro r hr
  let x : (shiftedNumberPower Sector (r+1/2)).domain := ⟨u.val,u.property _ (by linarith)⟩
  let y : (ordinaryAnnihilation f).domain := weightedAnnihilationSectorInput ordinarySectorKernel (ordinaryKernel f) r hr x
  have he : ordinaryAnnihilationAllInput f u = y := Subtype.ext rfl
  rw [he]
  exact weightedAnnihilationSector_mem ordinarySectorKernel (ordinaryKernel f) r hr x

/-- Read the list in the order of application; every stage carries its actual domain witness. -/
def ordinaryFieldWord (ops : List (Bool × OneBoson)) (u : EveryOrdinaryNumberVector) : EveryOrdinaryNumberVector :=
  match ops with
  | [] => u
  | (true,f)::rest => ordinaryFieldWord rest (ordinaryCreationAll f u)
  | (false,f)::rest => ordinaryFieldWord rest (ordinaryAnnihilationAll f u)

lemma ordinaryFieldWord_preserves (ops : List (Bool × OneBoson)) (u : EveryOrdinaryNumberVector) :
    ∀ r : ℝ, 0 ≤ r → (ordinaryFieldWord ops u).val ∈ (numberPower Sector r).domain :=
  (everyOrdinaryNumberDomain_iff _).mp (ordinaryFieldWord ops u).property

end GW.Fock
