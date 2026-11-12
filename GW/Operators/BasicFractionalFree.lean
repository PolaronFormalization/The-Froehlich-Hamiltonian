module
public import GW.Operators.BasicInterpolation
public import GW.Regularity.RegMixedDomains
public import GW.Fock.FockTwoFields
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Fock

lemma fractionalFree_scalar_sandwich (σ a b : ℝ) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (1+a+b)^σ ≤ 1+a^σ+b^σ ∧ 1+a^σ+b^σ ≤ 3*(1+a+b)^σ := by
  have h₁ := Real.rpow_add_le_add_rpow (by positivity : (0:ℝ) ≤ 1+a) hb hσ hσ1
  have h₂ := Real.rpow_add_le_add_rpow (by norm_num : (0:ℝ) ≤ 1) ha hσ hσ1
  rw [Real.one_rpow] at h₂
  have h0 : (1:ℝ) ≤ (1+a+b)^σ := Real.one_le_rpow (by linarith) hσ
  have hA : a^σ ≤ (1+a+b)^σ := Real.rpow_le_rpow ha (by linarith) hσ
  have hB : b^σ ≤ (1+a+b)^σ := Real.rpow_le_rpow hb (by linarith) hσ
  constructor <;> linarith

def fractionalFreeWeight (σ : ℝ) (n : ℕ) (q : GW.Space) : ℝ := (freeGraphWeight n q)^(σ/2)
def freeFractionalOperator (σ : ℝ) : Physical →ₗ.[ℂ] Physical := physicalSectorMultiplier (fractionalFreeWeight σ)
def fractionalQuadraticWeight (σ : ℝ) (n : ℕ) (q : GW.Space) : ℝ :=
  Real.sqrt (1+(‖q‖^σ)^2+(numberPowerCoefficient (σ/2) n)^2)

lemma fractionalFreeWeight_measurable (σ : ℝ) (n : ℕ) : Measurable (fractionalFreeWeight σ n) :=
  (freeGraphWeight_measurable n).pow_const _

lemma fractionalFreeWeight_one (σ : ℝ) (hσ : 0 ≤ σ) (n : ℕ) (q : GW.Space) :
    1 ≤ fractionalFreeWeight σ n q := Real.one_le_rpow (freeGraphWeight_one n q) (by positivity)

lemma fractionalNumberCoefficient_eq (r : ℝ) (n : ℕ) : numberPowerCoefficient r n = (n:ℝ)^r := by
  by_cases h : r = 0 <;> simp [numberPowerCoefficient,h]

lemma fractionalFreeWeight_sq (σ : ℝ) (n : ℕ) (q : GW.Space) :
    fractionalFreeWeight σ n q ^ 2 = (freeGraphWeight n q)^σ := by
  unfold fractionalFreeWeight
  rw [rpow_square _ _ (zero_le_one.trans (freeGraphWeight_one n q))]
  congr 1
  ring

lemma fractionalQuadraticWeight_sq (σ : ℝ) (n : ℕ) (q : GW.Space) :
    fractionalQuadraticWeight σ n q ^ 2 = 1+(‖q‖^σ)^2+(numberPowerCoefficient (σ/2) n)^2 :=
  Real.sq_sqrt (by positivity)

lemma fractionalQuadraticWeight_nonneg (σ : ℝ) (n : ℕ) (q : GW.Space) :
    0 ≤ fractionalQuadraticWeight σ n q := Real.sqrt_nonneg _

lemma fractionalQuadraticWeight_measurable (σ : ℝ) (n : ℕ) : Measurable (fractionalQuadraticWeight σ n) := by
  unfold fractionalQuadraticWeight
  fun_prop

lemma fractionalFree_weight_sandwich (σ : ℝ) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (n : ℕ) (q : GW.Space) :
    fractionalFreeWeight σ n q ^ 2 ≤ fractionalQuadraticWeight σ n q ^ 2 ∧
    fractionalQuadraticWeight σ n q ^ 2 ≤ 3*fractionalFreeWeight σ n q ^ 2 := by
  have h := fractionalFree_scalar_sandwich σ (‖q‖^2) (n:ℝ) hσ hσ1 (sq_nonneg _) (Nat.cast_nonneg n)
  have he : (‖q‖^2)^σ = (‖q‖^σ)^2 := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (norm_nonneg q),rpow_square _ _ (norm_nonneg q)]
    congr 1
  have hn : (n:ℝ)^σ = (numberPowerCoefficient (σ/2) n)^2 := by
    rw [fractionalNumberCoefficient_eq,rpow_square _ _ (Nat.cast_nonneg n)]
    congr 1
    ring
  rw [he,hn] at h
  simpa only [fractionalFreeWeight_sq,fractionalQuadraticWeight_sq,freeGraphWeight,freeEnergySymbol,add_assoc] using h

lemma fractionalFree_weight_le_quadratic (σ : ℝ) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (n : ℕ) (q : GW.Space) :
    |fractionalFreeWeight σ n q| ≤ |fractionalQuadraticWeight σ n q| := by
  apply (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mp
  rw [sq_abs,sq_abs]
  exact (fractionalFree_weight_sandwich σ hσ hσ1 n q).1

lemma fractionalQuadratic_weight_le_free (σ : ℝ) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (n : ℕ) (q : GW.Space) :
    |fractionalQuadraticWeight σ n q| ≤ Real.sqrt 3 * |fractionalFreeWeight σ n q| := by
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))).mp
  rw [sq_abs,mul_pow,sq_abs,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  exact (fractionalFree_weight_sandwich σ hσ hσ1 n q).2

lemma fractionalFree_domain_compare (σ : ℝ) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    (freeFractionalOperator σ).domain = (physicalSectorMultiplier (fractionalQuadraticWeight σ)).domain := by
  apply Submodule.ext
  intro u
  constructor
  · intro hu
    exact (physicalSectorMultiplier_domination (fractionalQuadraticWeight σ) (fractionalFreeWeight σ)
      (fractionalQuadraticWeight_measurable σ) (C := Real.sqrt 3) (Real.sqrt_nonneg _)
      (fractionalQuadratic_weight_le_free σ hσ hσ1) ⟨u,hu⟩).choose
  · intro hu
    exact (physicalSectorMultiplier_domination (fractionalFreeWeight σ) (fractionalQuadraticWeight σ)
      (fractionalFreeWeight_measurable σ) (C := 1) zero_le_one
      (fun n q => by simpa only [one_mul] using fractionalFree_weight_le_quadratic σ hσ hσ1 n q) ⟨u,hu⟩).choose

lemma fractionalFree_norm_equivalence (σ : ℝ) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (u : Physical)
    (hf : u ∈ (freeFractionalOperator σ).domain)
    (hc : u ∈ (physicalSectorMultiplier (fractionalQuadraticWeight σ)).domain) :
    ‖freeFractionalOperator σ ⟨u,hf⟩‖^2 ≤ ‖physicalSectorMultiplier (fractionalQuadraticWeight σ) ⟨u,hc⟩‖^2 ∧
    ‖physicalSectorMultiplier (fractionalQuadraticWeight σ) ⟨u,hc⟩‖^2 ≤ 3*‖freeFractionalOperator σ ⟨u,hf⟩‖^2 := by
  have hsmall := (physicalSectorMultiplier_domination (fractionalFreeWeight σ) (fractionalQuadraticWeight σ)
    (fractionalFreeWeight_measurable σ) (C := 1) zero_le_one
    (fun n q => by simpa only [one_mul] using fractionalFree_weight_le_quadratic σ hσ hσ1 n q) ⟨u,hc⟩).choose_spec
  have hlarge := (physicalSectorMultiplier_domination (fractionalQuadraticWeight σ) (fractionalFreeWeight σ)
    (fractionalQuadraticWeight_measurable σ) (C := Real.sqrt 3) (Real.sqrt_nonneg _)
    (fractionalQuadratic_weight_le_free σ hσ hσ1) ⟨u,hf⟩).choose_spec
  have hs : ‖freeFractionalOperator σ ⟨u,hf⟩‖ ≤ ‖physicalSectorMultiplier (fractionalQuadraticWeight σ) ⟨u,hc⟩‖ := by
    simpa only [freeFractionalOperator,one_mul] using hsmall
  have hl : ‖physicalSectorMultiplier (fractionalQuadraticWeight σ) ⟨u,hc⟩‖ ≤ Real.sqrt 3*‖freeFractionalOperator σ ⟨u,hf⟩‖ := hlarge
  refine ⟨pow_le_pow_left₀ (norm_nonneg _) hs 2,?_⟩
  have h := pow_le_pow_left₀ (norm_nonneg _) hl 2
  rw [mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)] at h
  exact h

lemma fractionalNumberOperator_eq (r : ℝ) :
    physicalNumberPower r = physicalSectorMultiplier (fun n _ => numberPowerCoefficient r n) :=
  (physicalSectorMultiplier_constant (numberPowerCoefficient r)).symm

lemma fractionalQuadratic_domain (σ : ℝ) :
    (physicalSectorMultiplier (fractionalQuadraticWeight σ)).domain =
      (electronRadialPower σ).domain ⊓ (physicalNumberPower (σ/2)).domain := by
  rw [fractionalNumberOperator_eq]
  change (physicalSectorMultiplier (fractionalQuadraticWeight σ)).domain =
    (physicalSectorMultiplier (fun _ q => ‖q‖^σ)).domain ⊓
      (physicalSectorMultiplier (fun n _ => numberPowerCoefficient (σ/2) n)).domain
  apply Submodule.ext
  intro u
  constructor
  · intro hu
    constructor
    · exact (physicalSectorMultiplier_domination (fun _ q => ‖q‖^σ) (fractionalQuadraticWeight σ)
        (fun _ => continuous_norm.measurable.pow_const _) (C := 1) zero_le_one
        (fun n q => by
          rw [abs_of_nonneg (fractionalQuadraticWeight_nonneg σ n q),one_mul]
          apply (sq_le_sq₀ (abs_nonneg _) (fractionalQuadraticWeight_nonneg σ n q)).mp
          rw [sq_abs,fractionalQuadraticWeight_sq]
          nlinarith [sq_nonneg (numberPowerCoefficient (σ/2) n)]) ⟨u,hu⟩).choose
    · exact (physicalSectorMultiplier_domination (fun n _ => numberPowerCoefficient (σ/2) n)
        (fractionalQuadraticWeight σ) (fun _ => measurable_const) (C := 1) zero_le_one
        (fun n q => by
          rw [abs_of_nonneg (fractionalQuadraticWeight_nonneg σ n q),one_mul]
          apply (sq_le_sq₀ (abs_nonneg _) (fractionalQuadraticWeight_nonneg σ n q)).mp
          rw [sq_abs,fractionalQuadraticWeight_sq]
          nlinarith [sq_nonneg (‖q‖^σ)]) ⟨u,hu⟩).choose
  · rintro ⟨ha,hb⟩
    exact (physicalSectorMultiplier_quadratic (fun _ q => ‖q‖^σ)
      (fun n _ => numberPowerCoefficient (σ/2) n) (fractionalQuadraticWeight σ)
      (fractionalQuadraticWeight_measurable σ) (fractionalQuadraticWeight_sq σ) u ha hb).choose

lemma fractionalFree_domain (σ : ℝ) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    (freeFractionalOperator σ).domain =
      (electronRadialPower σ).domain ⊓ (physicalNumberPower (σ/2)).domain :=
  (fractionalFree_domain_compare σ hσ hσ1).trans (fractionalQuadratic_domain σ)

lemma freeFractionalOperator_zero : freeFractionalOperator 0 =
    (LinearMap.id : Physical →ₗ[ℂ] Physical).toPMap ⊤ := by
  unfold freeFractionalOperator fractionalFreeWeight
  simp only [zero_div,Real.rpow_zero]
  rw [physicalSectorMultiplier_constant]
  exact bochnerDiagonal_one volume Sector

lemma freeFractionalOperator_one : freeFractionalOperator 1 = freeFormOperator := by
  unfold freeFractionalOperator fractionalFreeWeight freeFormOperator freeFormWeight
  congr 1
  funext n q
  rw [Real.sqrt_eq_rpow]

lemma freeFractionalOperator_two : freeFractionalOperator 2 = freeGraphOperator := by
  unfold freeFractionalOperator fractionalFreeWeight freeGraphOperator
  norm_num

lemma fractionalNumber_domains_eq (r : ℝ) (hr : 0 ≤ r) :
    (physicalNumberPower r).domain = (physicalShiftedNumberPower r).domain := by
  by_cases hz : r = 0
  · subst r
    rw [physicalNumberPower_zero]
    have he : physicalShiftedNumberPower 0 =
        (LinearMap.id : Physical →ₗ[ℂ] Physical).toPMap ⊤ := by
      change bochnerDiagonal volume Sector (fun n => ((n:ℝ)+1)^(0:ℝ)) = _
      simp only [Real.rpow_zero]
      exact bochnerDiagonal_one volume Sector
    rw [he]
  · rw [physicalNumberPower_domain_map,physicalShiftedNumberPower_domain_map]
    exact congrArg (fun V : Submodule ℂ ElectronBosonSum => V.map electronBosonUnitary.toLinearMap)
      (numberPower_domain_eq ElectronSector r (lt_of_le_of_ne hr (Ne.symm hz)))

lemma fractionalWeightValue_norm (w : ℕ → GW.Space → ℝ) (u : (physicalSectorMultiplier w).domain) :
    ‖GW.Spaces.sumWeightValue (F := Sector) (fun _ : ℕ => (volume : Measure GW.Space)) (physicalWeightInput w u)‖ =
      ‖physicalSectorMultiplier w u‖ := by
  rw [← physicalWeightProduct_value]
  change ‖freeFourierRepresentation (physicalSectorMultiplier w u)‖ = _
  exact freeFourierRepresentation.norm_map _

def fractionalPhysicalInput (w : ℕ → GW.Space → ℝ)
    (a : GW.Spaces.sumWeightDomain (F := Sector) (fun _ : ℕ => (volume : Measure GW.Space)) w) :
    (physicalSectorMultiplier w).domain :=
  ⟨freeFourierRepresentation.symm a.val,by
    apply (physicalSectorMultiplier_domain w _).mpr
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact a.property⟩

lemma fractionalPhysicalInput_weight (w : ℕ → GW.Space → ℝ)
    (a : GW.Spaces.sumWeightDomain (F := Sector) (fun _ : ℕ => (volume : Measure GW.Space)) w) :
    physicalWeightInput w (fractionalPhysicalInput w a) = a := by
  apply Subtype.ext
  exact freeFourierRepresentation.apply_symm_apply a.val

lemma fractionalPhysicalInput_norm (w : ℕ → GW.Space → ℝ)
    (a : GW.Spaces.sumWeightDomain (F := Sector) (fun _ : ℕ => (volume : Measure GW.Space)) w) :
    ‖physicalSectorMultiplier w (fractionalPhysicalInput w a)‖ = ‖GW.Spaces.sumWeightValue (F := Sector)
      (fun _ : ℕ => (volume : Measure GW.Space)) a‖ := by
  have h := fractionalWeightValue_norm w (fractionalPhysicalInput w a)
  rw [fractionalPhysicalInput_weight] at h
  exact h.symm

lemma fractionalPhysical_interpolation
    (w : ℕ → GW.Space → ℝ) (hw : ∀ n, Measurable (w n)) (hw1 : ∀ n q, 1 ≤ w n q)
    (T : Physical →L[ℂ] Physical) (M₀ M₁ : ℝ) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (hT₀ : ∀ u, ‖T u‖ ≤ M₀*‖u‖)
    (hT₁ : ∀ u : (physicalSectorMultiplier w).domain,
      ∃ hu : T u.val ∈ (physicalSectorMultiplier w).domain,
        ‖physicalSectorMultiplier w ⟨T u.val,hu⟩‖ ≤ M₁*‖physicalSectorMultiplier w u‖)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (u : Physical)
    (hu : u ∈ (physicalSectorMultiplier (fun n q => (w n q)^θ)).domain) :
    ∃ hv : T u ∈ (physicalSectorMultiplier (fun n q => (w n q)^θ)).domain,
      ‖physicalSectorMultiplier (fun n q => (w n q)^θ) ⟨T u,hv⟩‖ ≤
        M₀^(1-θ)*M₁^θ*‖physicalSectorMultiplier (fun n q => (w n q)^θ) ⟨u,hu⟩‖ := by
  let μ := fun _ : ℕ => (volume : Measure GW.Space)
  have he (a : GW.Spaces.sumWeightDomain (F := Sector) μ w) :
      ∃ b : GW.Spaces.sumWeightDomain (F := Sector) μ w,
        b.val = freeFourierRepresentation (T (freeFourierRepresentation.symm a.val)) ∧
        ‖GW.Spaces.sumWeightValue (F := Sector) μ b‖ ≤ M₁*‖GW.Spaces.sumWeightValue (F := Sector) μ a‖ := by
    let x := fractionalPhysicalInput w a
    obtain ⟨hx,hbound⟩ := hT₁ x
    let y : (physicalSectorMultiplier w).domain := ⟨T x.val,hx⟩
    refine ⟨physicalWeightInput w y,rfl,?_⟩
    rw [fractionalWeightValue_norm,← fractionalPhysicalInput_norm]
    exact hbound
  have hz : freeFourierRepresentation u ∈ GW.Spaces.sumWeightDomain (F := Sector) μ (fun n q => (w n q)^θ) :=
    (physicalSectorMultiplier_domain _ u).mp hu
  obtain ⟨b,hb,hbound⟩ := GW.Operators.sumWeightedInterpolation_unitary μ μ w w hw hw hw1 hw1
    freeFourierRepresentation freeFourierRepresentation T M₀ M₁ hM₀ hM₁ hT₀ he θ hθ hθ1 u hz
  have hv : T u ∈ (physicalSectorMultiplier (fun n q => (w n q)^θ)).domain := by
    apply (physicalSectorMultiplier_domain _ _).mpr
    rw [← hb]
    exact b.property
  refine ⟨hv,?_⟩
  have hbb : physicalWeightInput (fun n q => (w n q)^θ) ⟨T u,hv⟩ = b := Subtype.ext hb.symm
  rw [← fractionalWeightValue_norm _ ⟨T u,hv⟩,hbb,← fractionalWeightValue_norm _ ⟨u,hu⟩]
  exact hbound

lemma fractionalFormWeight_power (σ : ℝ) (n : ℕ) (q : GW.Space) :
    (freeFormWeight n q)^σ = fractionalFreeWeight σ n q := by
  unfold freeFormWeight fractionalFreeWeight
  rw [Real.sqrt_eq_rpow,← Real.rpow_mul (zero_le_one.trans (freeGraphWeight_one n q))]
  congr 1
  ring

lemma fractionalFormWeight_operator (σ : ℝ) :
    physicalSectorMultiplier (fun n q => (freeFormWeight n q)^σ) = freeFractionalOperator σ := by
  unfold freeFractionalOperator
  congr 1
  funext n q
  exact fractionalFormWeight_power σ n q

lemma fractionalFree_invariant (T : Physical →L[ℂ] Physical)
    (hQ : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : freeFormOperator.domain,
      ∃ hu : T u.val ∈ freeFormOperator.domain,
        ‖freeFormOperator ⟨T u.val,hu⟩‖ ≤ C*‖freeFormOperator u‖)
    (σ : ℝ) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (u : Physical)
    (hu : u ∈ (freeFractionalOperator σ).domain) : T u ∈ (freeFractionalOperator σ).domain := by
  by_cases hz : σ = 0
  · subst σ
    rw [freeFractionalOperator_zero]
    exact Submodule.mem_top
  obtain ⟨C,hC,hTC⟩ := hQ
  have hT₀ (x : Physical) : ‖T x‖ ≤ (‖T‖+1)*‖x‖ :=
    (T.le_opNorm x).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  have hT₁ (x : (physicalSectorMultiplier freeFormWeight).domain) :
      ∃ hx : T x.val ∈ (physicalSectorMultiplier freeFormWeight).domain,
        ‖physicalSectorMultiplier freeFormWeight ⟨T x.val,hx⟩‖ ≤ (C+1)*‖physicalSectorMultiplier freeFormWeight x‖ := by
    obtain ⟨hx,hbound⟩ := hTC x
    refine ⟨hx,?_⟩
    exact hbound.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  have hu' : u ∈ (physicalSectorMultiplier (fun n q => (freeFormWeight n q)^σ)).domain := by
    rw [fractionalFormWeight_operator]
    exact hu
  obtain ⟨hv,_⟩ := fractionalPhysical_interpolation freeFormWeight freeFormWeight_measurable freeFormWeight_one
    T (‖T‖+1) (C+1) (by positivity) (by linarith) hT₀ hT₁ σ hσ hσ1 u hu'
  rwa [fractionalFormWeight_operator] at hv

lemma fractionalShiftedOne_eq : physicalShiftedNumberPower 1 =
    physicalSectorMultiplier (fun n _ => (n:ℝ)+1) := by
  simpa only [Real.rpow_one] using physicalShiftedNumberPower_eq_sectorMultiplier (1:ℝ)

lemma fractionalNumberOne_domain : (physicalSectorMultiplier (fun n _ => (n:ℝ)+1)).domain =
    physicalNumberOperator.domain := by
  rw [← fractionalShiftedOne_eq]
  exact physicalNumber_shiftedOne_domain.symm

lemma fractionalNumberOne_action (u : (physicalSectorMultiplier (fun n _ => (n:ℝ)+1)).domain) :
    ∃ hn : u.val ∈ physicalNumberOperator.domain,
      physicalSectorMultiplier (fun n _ => (n:ℝ)+1) u = physicalNumberOperator ⟨u.val,hn⟩+u.val := by
  let v : physicalNumberOperator.domain := ⟨u.val,fractionalNumberOne_domain.le u.property⟩
  let z : (physicalSectorMultiplier (fun n _ => (n:ℝ))).domain :=
    ⟨u.val,by rw [← physicalNumber_eq_sectorMultiplier];exact v.property⟩
  have hz : physicalSectorMultiplier (fun n _ => (n:ℝ)) z = physicalNumberOperator v :=
    (partialMap_action_eq_of_same_input physicalNumber_eq_sectorMultiplier v z rfl).symm
  have he : physicalSectorMultiplier (fun n _ => (n:ℝ)+1) u =
      physicalSectorMultiplier (fun n _ => (n:ℝ)) z+u.val := by
    apply freeFourierRepresentation.injective
    rw [map_add]
    apply lp.ext
    funext n
    apply Lp.ext
    filter_upwards [physicalSectorMultiplier_action (fun n _ => (n:ℝ)+1) u n,
      physicalSectorMultiplier_action (fun n _ => (n:ℝ)) z n,
      Lp.coeFn_add (freeFourierRepresentation (physicalSectorMultiplier (fun n _ => (n:ℝ)) z) n)
        (freeFourierRepresentation u.val n)] with q h₁ h₂ h₃
    change freeFourierRepresentation (physicalSectorMultiplier (fun n _ => (n:ℝ)+1) u) n q =
      (freeFourierRepresentation (physicalSectorMultiplier (fun n _ => (n:ℝ)) z) n+freeFourierRepresentation u.val n) q
    rw [h₃]
    simp only [Pi.add_apply]
    change ((((n:ℝ)+1:ℝ):ℂ) • freeFourierRepresentation u.val n q) =
      freeFourierRepresentation (physicalSectorMultiplier (fun n _ => (n:ℝ)+1) u) n q at h₁
    change ((n:ℝ):ℂ) • freeFourierRepresentation u.val n q =
      freeFourierRepresentation (physicalSectorMultiplier (fun n _ => (n:ℝ)) z) n q at h₂
    rw [← h₁,← h₂,Complex.ofReal_add,Complex.ofReal_one,add_smul,one_smul]
  exact ⟨v.property,he.trans (congrArg (fun a : Physical => a+u.val) hz)⟩

lemma fractionalWeight_ge_norm (w : ℕ → GW.Space → ℝ) (hw : ∀ n, Measurable (w n))
    (hw1 : ∀ n q, 1 ≤ w n q) (u : (physicalSectorMultiplier w).domain) :
    ‖u.val‖ ≤ ‖physicalSectorMultiplier w u‖ := by
  have h := (physicalWeightEmbedding w hw hw1).le_opNorm (physicalWeightProduct w u)
  rw [physicalWeightEmbedding_product] at h
  calc
    _ ≤ ‖physicalWeightEmbedding w hw hw1‖*‖physicalWeightProduct w u‖ := h
    _ ≤ 1*‖physicalWeightProduct w u‖ := mul_le_mul_of_nonneg_right (physicalWeightEmbedding_norm w hw hw1) (norm_nonneg _)
    _ = _ := by
      rw [one_mul]
      change ‖freeFourierRepresentation (physicalSectorMultiplier w u)‖ = _
      exact freeFourierRepresentation.norm_map _

lemma fractionalNumberOne_graph_bounds (u : (physicalSectorMultiplier (fun n _ => (n:ℝ)+1)).domain) :
    ∃ hn : u.val ∈ physicalNumberOperator.domain,
      ‖physicalSectorMultiplier (fun n _ => (n:ℝ)+1) u‖ ≤ ‖u.val‖+‖physicalNumberOperator ⟨u.val,hn⟩‖ ∧
      ‖u.val‖+‖physicalNumberOperator ⟨u.val,hn⟩‖ ≤ 2*‖physicalSectorMultiplier (fun n _ => (n:ℝ)+1) u‖ := by
  obtain ⟨hn,he⟩ := fractionalNumberOne_action u
  have hu := fractionalWeight_ge_norm (fun n _ => (n:ℝ)+1) (fun _ => measurable_const)
    (fun n _ => by linarith [Nat.cast_nonneg (α := ℝ) n]) u
  have hN := physicalSectorMultiplier_domination (fun n _ => (n:ℝ)) (fun n _ => (n:ℝ)+1)
    (fun _ => measurable_const) (C := 1) zero_le_one
    (fun n _ => by rw [abs_of_nonneg (Nat.cast_nonneg _),abs_of_nonneg (by positivity),one_mul]; linarith) u
  let z : (physicalSectorMultiplier (fun n _ => (n:ℝ))).domain := ⟨u.val,hN.choose⟩
  have hz := partialMap_action_eq_of_same_input physicalNumber_eq_sectorMultiplier
    (⟨u.val,hn⟩ : physicalNumberOperator.domain) z rfl
  have hsmall : ‖physicalNumberOperator ⟨u.val,hn⟩‖ ≤ ‖physicalSectorMultiplier (fun n _ => (n:ℝ)+1) u‖ := by
    rw [hz]
    simpa only [one_mul] using hN.choose_spec
  refine ⟨hn,?_,by linarith⟩
  rw [he]
  exact (norm_add_le _ _).trans_eq (add_comm _ _)

lemma fractionalQuadratic_norm_split (σ : ℝ) (u : Physical)
    (hp : u ∈ (electronRadialPower σ).domain) (hn : u ∈ (physicalNumberPower (σ/2)).domain)
    (hc : u ∈ (physicalSectorMultiplier (fractionalQuadraticWeight σ)).domain) :
    ‖physicalSectorMultiplier (fractionalQuadraticWeight σ) ⟨u,hc⟩‖^2 =
      ‖u‖^2+‖electronRadialPower σ ⟨u,hp⟩‖^2+‖physicalNumberPower (σ/2) ⟨u,hn⟩‖^2 := by
  have hb : u ∈ (physicalSectorMultiplier (fun n _ => numberPowerCoefficient (σ/2) n)).domain := by
    rw [← fractionalNumberOperator_eq]
    exact hn
  have he := partialMap_action_eq_of_same_input (fractionalNumberOperator_eq (σ/2))
    (⟨u,hn⟩ : (physicalNumberPower (σ/2)).domain)
    (⟨u,hb⟩ : (physicalSectorMultiplier (fun n _ => numberPowerCoefficient (σ/2) n)).domain) rfl
  have h : ‖physicalSectorMultiplier (fractionalQuadraticWeight σ) ⟨u,hc⟩‖^2 =
      ‖u‖^2+‖electronRadialPower σ ⟨u,hp⟩‖^2+
        ‖physicalSectorMultiplier (fun n _ => numberPowerCoefficient (σ/2) n) ⟨u,hb⟩‖^2 :=
    (physicalSectorMultiplier_quadratic (fun _ q => ‖q‖^σ)
    (fun n _ => numberPowerCoefficient (σ/2) n) (fractionalQuadraticWeight σ)
    (fractionalQuadraticWeight_measurable σ) (fractionalQuadraticWeight_sq σ) u hp hb).choose_spec
  have hn' := congrArg (fun z : Physical => ‖z‖^2) he.symm
  rw [hn'] at h
  exact h

lemma fractionalNumber_invariant (T : Physical →L[ℂ] Physical)
    (hN : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : physicalNumberOperator.domain,
      ∃ hu : T u.val ∈ physicalNumberOperator.domain,
        ‖T u.val‖+‖physicalNumberOperator ⟨T u.val,hu⟩‖ ≤ C*(‖u.val‖+‖physicalNumberOperator u‖))
    (σ : ℝ) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (u : Physical)
    (hu : u ∈ (physicalNumberPower σ).domain) : T u ∈ (physicalNumberPower σ).domain := by
  by_cases hz : σ = 0
  · subst σ
    rw [physicalNumberPower_zero]
    exact Submodule.mem_top
  obtain ⟨C,hC,hTC⟩ := hN
  have hT₀ (x : Physical) : ‖T x‖ ≤ (‖T‖+1)*‖x‖ :=
    (T.le_opNorm x).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  have hT₁ (x : (physicalSectorMultiplier (fun n _ => (n:ℝ)+1)).domain) :
      ∃ hx : T x.val ∈ (physicalSectorMultiplier (fun n _ => (n:ℝ)+1)).domain,
        ‖physicalSectorMultiplier (fun n _ => (n:ℝ)+1) ⟨T x.val,hx⟩‖ ≤
          (2*C+1)*‖physicalSectorMultiplier (fun n _ => (n:ℝ)+1) x‖ := by
    obtain ⟨hn,hleft,hright⟩ := fractionalNumberOne_graph_bounds x
    obtain ⟨hy,hbound⟩ := hTC ⟨x.val,hn⟩
    have hyw : T x.val ∈ (physicalSectorMultiplier (fun n _ => (n:ℝ)+1)).domain := by
      exact (congrArg (fun V : Submodule ℂ Physical => T x.val ∈ V)
        fractionalNumberOne_domain).mpr hy
    obtain ⟨hny,hyleft,hyright⟩ := fractionalNumberOne_graph_bounds ⟨T x.val,hyw⟩
    refine ⟨hyw,?_⟩
    calc
      _ ≤ C*(‖x.val‖+‖physicalNumberOperator ⟨x.val,hn⟩‖) := hyleft.trans hbound
      _ ≤ C*(2*‖physicalSectorMultiplier (fun n _ => (n:ℝ)+1) x‖) := mul_le_mul_of_nonneg_left hright hC
      _ ≤ _ := by nlinarith [norm_nonneg (physicalSectorMultiplier (fun n _ => (n:ℝ)+1) x)]
  have hu' : u ∈ (physicalSectorMultiplier (fun n _ => ((n:ℝ)+1)^σ)).domain := by
    rw [← physicalShiftedNumberPower_eq_sectorMultiplier]
    rw [← fractionalNumber_domains_eq σ hσ]
    exact hu
  obtain ⟨hv,_⟩ := fractionalPhysical_interpolation (fun n _ => (n:ℝ)+1) (fun _ => measurable_const)
    (fun n _ => by linarith [Nat.cast_nonneg (α := ℝ) n]) T (‖T‖+1) (2*C+1)
    (by positivity) (by positivity) hT₀ hT₁ σ hσ hσ1 u hu'
  rw [← physicalShiftedNumberPower_eq_sectorMultiplier,← fractionalNumber_domains_eq σ hσ] at hv
  exact hv

end GW.Fock
