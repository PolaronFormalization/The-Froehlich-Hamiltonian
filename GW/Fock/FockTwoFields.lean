module
public import GW.Fock.FockWeightedFields
public import GW.Fock.FockFieldDefinition
public import GW.Operators.BasicFree
@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GW.Fock

lemma partialMap_action_eq_of_same_input {H : Type*} [AddCommGroup H] [Module ℂ H]
    {A B : H →ₗ.[ℂ] H} (h : A = B) (u : A.domain) (v : B.domain) (huv : u.val = v.val) :
    A u = B v := by
  subst B
  exact congrArg A (Subtype.ext huv)

section SectorProducts
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {S : ℕ → Type*} [∀ n, NormedAddCommGroup (S n)] [∀ n, InnerProductSpace ℂ (S n)]
  (R : ∀ n, S n ≃ₗᵢ[ℂ] kernelFixed (E := E) n)

def sectorWeightedChoice (b : Bool) (F : BosonKernel E) (r : ℝ) (hr : 0 ≤ r)
    (u : (shiftedNumberPower S (r+1/2)).domain) : (shiftedNumberPower S r).domain :=
  if b then weightedCreationSectorOutput R F r hr u else weightedAnnihilationSectorOutput R F r hr u

def sectorFieldChoice (b : Bool) (F : BosonKernel E) : lp S 2 →ₗ.[ℂ] lp S 2 :=
  if b then maximalSectorCreation (sectorCreation R F) else maximalSectorAnnihilation (sectorAnnihilation R F)

lemma sectorWeightedChoice_graph (b : Bool) (F : BosonKernel E) (r : ℝ) (hr : 0 ≤ r)
    (u : (shiftedNumberPower S (r+1/2)).domain) :
    (u.val,(sectorWeightedChoice R b F r hr u).val) ∈ (sectorFieldChoice R b F).graph := by
  cases b
  · exact (maximalSectorAnnihilation (sectorAnnihilation R F)).mem_graph
      (weightedAnnihilationSectorInput R F r hr u)
  · exact (maximalSectorCreation (sectorCreation R F)).mem_graph
      (weightedCreationSectorInput R F r hr u)

lemma sectorWeightedChoice_norm (b : Bool) (F : BosonKernel E) (r : ℝ) (hr : 0 ≤ r)
    (u : (shiftedNumberPower S (r+1/2)).domain) :
    ‖shiftedNumberPower S r (sectorWeightedChoice R b F r hr u)‖ ≤
      (2:ℝ)^r * ‖F‖ * ‖shiftedNumberPower S (r+1/2) u‖ := by
  cases b
  · change ‖shiftedNumberPower S r (weightedAnnihilationSectorOutput R F r hr u)‖ ≤ _
    calc
      _ ≤ ‖F‖ * ‖shiftedNumberPower S (r+1/2) u‖ := weightedAnnihilationSector_norm R F r hr u
      _ ≤ _ := mul_le_mul_of_nonneg_right
        ((one_mul ‖F‖).symm.le.trans (mul_le_mul_of_nonneg_right
          (Real.one_le_rpow (by norm_num) hr) (norm_nonneg F))) (norm_nonneg _)
  · exact weightedCreationSector_norm R F r hr u

lemma sectorShiftedNumber_zero_action (u : (shiftedNumberPower S 0).domain) :
    shiftedNumberPower S 0 u = u.val := by
  let I := (LinearMap.id : lp S 2 →ₗ[ℂ] lp S 2).toPMap ⊤
  have h : (u.val,shiftedNumberPower S 0 u) ∈ I.graph :=
    (congrArg LinearPMap.graph (shiftedNumberPower_zero S)) ▸ (shiftedNumberPower S 0).mem_graph u
  obtain ⟨x,hx,hy⟩ := I.mem_graph_iff.mp h
  change x.val = shiftedNumberPower S 0 u at hy
  exact hy.symm.trans hx

lemma sectorTwoField (b c : Bool) (F G : BosonKernel E) (u : (shiftedNumberPower S 1).domain) :
    ∃ w v : lp S 2, (u.val,w) ∈ (sectorFieldChoice R c G).graph ∧
      (w,v) ∈ (sectorFieldChoice R b F).graph ∧
      ‖v‖ ≤ Real.sqrt 2 * ‖F‖ * ‖G‖ * ‖shiftedNumberPower S 1 u‖ := by
  have h₁ : (1/2:ℝ)+1/2 = 1 := by norm_num
  have h₀ : (0:ℝ)+1/2 = 1/2 := zero_add _
  let x : (shiftedNumberPower S (1/2+1/2)).domain := ⟨u.val,by rw [h₁]; exact u.property⟩
  let w := sectorWeightedChoice R c G (1/2) (by norm_num) x
  let y : (shiftedNumberPower S (0+1/2)).domain := ⟨w.val,by rw [h₀]; exact w.property⟩
  let v := sectorWeightedChoice R b F 0 le_rfl y
  refine ⟨w.val,v.val,sectorWeightedChoice_graph R c G (1/2) (by norm_num) x,
    sectorWeightedChoice_graph R b F 0 le_rfl y,?_⟩
  have hX := partialMap_action_eq_of_same_input (congrArg (shiftedNumberPower S) h₁) x u rfl
  have hY := partialMap_action_eq_of_same_input (congrArg (shiftedNumberPower S) h₀) y w rfl
  have hb := sectorWeightedChoice_norm R b F 0 le_rfl y
  have hc := sectorWeightedChoice_norm R c G (1/2) (by norm_num) x
  change ‖shiftedNumberPower S 0 v‖ ≤ _ at hb
  rw [sectorShiftedNumber_zero_action v,hY,Real.rpow_zero,one_mul] at hb
  change ‖shiftedNumberPower S (1/2) w‖ ≤ _ at hc
  rw [hX, ← Real.sqrt_eq_rpow] at hc
  exact hb.trans ((mul_le_mul_of_nonneg_left hc (norm_nonneg F)).trans_eq (by ring))

end SectorProducts

def fieldChoice (b : Bool) (F : BosonKernel ElectronL2) : Physical →ₗ.[ℂ] Physical :=
  if b then generalizedCreation F else generalizedAnnihilation F

lemma fieldChoice_representation (b : Bool) (F : BosonKernel ElectronL2) :
    fieldChoice b F =
      representationTransport electronBosonUnitary.symm (sectorFieldChoice physicalSectorKernel b F) := by
  cases b <;> rfl

lemma fieldChoice_graph_transport (b : Bool) (F : BosonKernel ElectronL2) (x y : ElectronBosonSum)
    (h : (x,y) ∈ (sectorFieldChoice physicalSectorKernel b F).graph) :
    (electronBosonUnitary x,electronBosonUnitary y) ∈ (fieldChoice b F).graph := by
  rw [fieldChoice_representation]
  apply (representationTransport_graph electronBosonUnitary.symm (sectorFieldChoice physicalSectorKernel b F) _).mpr
  change (electronBosonUnitary.symm (electronBosonUnitary x),electronBosonUnitary.symm (electronBosonUnitary y)) ∈ _
  rw [electronBosonUnitary.symm_apply_apply,electronBosonUnitary.symm_apply_apply]
  exact h

lemma twoField_composition (b c : Bool) (F G : BosonKernel ElectronL2)
    (u : (physicalShiftedNumberPower 1).domain) :
    ∃ w v : Physical, (u.val,w) ∈ (fieldChoice c G).graph ∧ (w,v) ∈ (fieldChoice b F).graph ∧
      ‖v‖ ≤ Real.sqrt 2 * ‖F‖ * ‖G‖ * ‖physicalShiftedNumberPower 1 u‖ := by
  let x := physicalShiftedSectorInput 1 u
  obtain ⟨w,v,hw,hv,hb⟩ := sectorTwoField physicalSectorKernel b c F G x
  refine ⟨electronBosonUnitary w,electronBosonUnitary v,?_,fieldChoice_graph_transport b F w v hv,?_⟩
  · have h := fieldChoice_graph_transport c G x.val w hw
    have hx : electronBosonUnitary x.val = u.val := electronBosonUnitary.apply_symm_apply _
    rwa [hx] at h
  · rw [electronBosonUnitary.norm_map,physicalShiftedSectorInput_norm]
    exact hb

def electronMomentumComponent (j : Fin 3) : Physical →ₗ.[ℂ] Physical :=
  physicalSectorMultiplier (fun _ q => q j)

def mixedNumberMomentumComponentSymbol (j : Fin 3) (n : ℕ) (q : GW.Space) : ℝ :=
  Real.sqrt ((n:ℝ)+1) * q j

lemma freeGraph_momentumComponent_mem (u : freeGraphOperator.domain) (j : Fin 3) :
    u.val ∈ (electronMomentumComponent j).domain := by
  obtain ⟨h,_⟩ := physicalSectorMultiplier_domination (fun _ q => q j) freeGraphWeight
    (fun _ => (PiLp.continuous_apply 2 _ j).measurable) zero_le_one (fun n q => by
      have hq : |q j| ≤ ‖q‖ := (Real.norm_eq_abs (q j)) ▸ PiLp.norm_apply_le q j
      rw [abs_of_nonneg (zero_le_one.trans (freeGraphWeight_one n q)),one_mul]
      refine hq.trans ?_
      change ‖q‖ ≤ 1 + (‖q‖^2+(n:ℝ))
      nlinarith [sq_nonneg (‖q‖-1),Nat.cast_nonneg (α := ℝ) n]) u
  exact h

def freeGraphMomentumInput (u : freeGraphOperator.domain) (j : Fin 3) :
    (electronMomentumComponent j).domain :=
  ⟨u.val,freeGraph_momentumComponent_mem u j⟩

set_option maxHeartbeats 450000 in
lemma freeGraph_momentumComponent_shiftedRoot_mem (u : freeGraphOperator.domain) (j : Fin 3) :
    electronMomentumComponent j (freeGraphMomentumInput u j) ∈
      (physicalShiftedNumberPower (1/2)).domain := by
  have hmq (n : ℕ) (q : GW.Space) : |mixedNumberMomentumComponentSymbol j n q| ≤
      (1/2:ℝ) * |freeGraphWeight n q| := by
    have hq : |q j| ≤ ‖q‖ := (Real.norm_eq_abs (q j)) ▸ PiLp.norm_apply_le q j
    calc
      _ = Real.sqrt ((n:ℝ)+1) * |q j| := by
        rw [mixedNumberMomentumComponentSymbol,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ mixedNumberMomentumSymbol n q := by
        exact mul_le_mul_of_nonneg_left hq (Real.sqrt_nonneg _)
      _ = |mixedNumberMomentumSymbol n q| := (abs_of_nonneg (by unfold mixedNumberMomentumSymbol; positivity)).symm
      _ ≤ _ := mixedNumberMomentum_bound n q
  obtain ⟨hm,_⟩ := physicalSectorMultiplier_domination (mixedNumberMomentumComponentSymbol j) freeGraphWeight
    (fun _ => measurable_const.mul (PiLp.continuous_apply 2 _ j).measurable) (by norm_num) hmq u
  have h := (physicalSectorMultiplier_composition (fun _ q => q j)
    (fun n _ => Real.sqrt ((n:ℝ)+1)) u.val (freeGraph_momentumComponent_mem u j) hm).choose
  let v : Physical := electronMomentumComponent j (freeGraphMomentumInput u j)
  change v ∈ (physicalSectorMultiplier (fun n _ => Real.sqrt ((n:ℝ)+1))).domain at h
  exact (congrArg (fun (A : Physical →ₗ.[ℂ] Physical) => v ∈ A.domain)
    physicalShiftedNumberHalf_eq_sectorMultiplier).mpr h

def freeGraphMomentumShiftedRoot (u : freeGraphOperator.domain) (j : Fin 3) :
    (physicalShiftedNumberPower (1/2)).domain :=
  ⟨electronMomentumComponent j (freeGraphMomentumInput u j),freeGraph_momentumComponent_shiftedRoot_mem u j⟩

lemma creationMomentum_vector_bound (F : Fin 3 → BosonKernel ElectronL2) (u : freeGraphOperator.domain) :
    ‖∑ j, generalizedCreation (F j) (generalizedCreationShiftedInput (F j) (freeGraphMomentumShiftedRoot u j))‖ ≤
      Real.sqrt (∑ j, ‖F j‖^2) *
        Real.sqrt (∑ j, ‖physicalShiftedNumberPower (1/2) (freeGraphMomentumShiftedRoot u j)‖^2) := by
  calc
    _ ≤ ∑ j, ‖generalizedCreation (F j) (generalizedCreationShiftedInput (F j) (freeGraphMomentumShiftedRoot u j))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j, ‖F j‖ * ‖physicalShiftedNumberPower (1/2) (freeGraphMomentumShiftedRoot u j)‖ :=
      Finset.sum_le_sum (fun j _ => generalizedCreation_shifted_norm (F j) (freeGraphMomentumShiftedRoot u j))
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _

lemma creationMomentum_phaseVector_bound (f : Fin 3 → OneBoson) (u : freeGraphOperator.domain) :
    ‖∑ j, generalizedCreation (phaseMultiplicationKernel (f j))
        (generalizedCreationShiftedInput (phaseMultiplicationKernel (f j)) (freeGraphMomentumShiftedRoot u j))‖ ≤
      Real.sqrt (∑ j, ‖f j‖^2) *
        Real.sqrt (∑ j, ‖physicalShiftedNumberPower (1/2) (freeGraphMomentumShiftedRoot u j)‖^2) := by
  simpa only [phaseMultiplicationKernel_norm] using creationMomentum_vector_bound (fun j => phaseMultiplicationKernel (f j)) u

lemma ordinaryKernel_opNorm (f : OneBoson) : ‖ordinaryKernel f‖ = ‖f‖ :=
  ContinuousLinearMap.norm_toSpanSingleton f

def ordinaryWeightedChoice (b : Bool) (f : OneBoson) (r : ℝ) (hr : 0 ≤ r)
    (u : (shiftedNumberPower Sector (r+1/2)).domain) : (shiftedNumberPower Sector r).domain :=
  if b then weightedCreationSectorOutput ordinarySectorKernel (ordinaryKernel f) r hr u
  else weightedAnnihilationSectorOutput ordinarySectorKernel (ordinaryKernel f) r hr u

lemma ordinaryWeightedChoice_norm (b : Bool) (f : OneBoson) (r : ℝ) (hr : 0 ≤ r)
    (u : (shiftedNumberPower Sector (r+1/2)).domain) :
    ‖shiftedNumberPower Sector r (ordinaryWeightedChoice b f r hr u)‖ ≤
      (2:ℝ)^r * ‖f‖ * ‖shiftedNumberPower Sector (r+1/2) u‖ := by
  cases b
  · change ‖shiftedNumberPower Sector r
      (weightedAnnihilationSectorOutput ordinarySectorKernel (ordinaryKernel f) r hr u)‖ ≤ _
    calc
      _ ≤ ‖f‖ * ‖shiftedNumberPower Sector (r+1/2) u‖ := by
        rw [← ordinaryKernel_opNorm f]
        exact weightedAnnihilationSector_norm ordinarySectorKernel (ordinaryKernel f) r hr u
      _ ≤ _ := mul_le_mul_of_nonneg_right
        ((one_mul ‖f‖).symm.le.trans (mul_le_mul_of_nonneg_right
          (Real.one_le_rpow (by norm_num) hr) (norm_nonneg f))) (norm_nonneg _)
  · rw [← ordinaryKernel_opNorm f]
    exact weightedCreationSector_norm ordinarySectorKernel (ordinaryKernel f) r hr u

def ordinaryTwoInput (u : (shiftedNumberPower Sector 1).domain) :
    (shiftedNumberPower Sector ((1/2:ℝ)+1/2)).domain :=
  ⟨u.val,by simpa only [show (1/2:ℝ)+1/2=1 by norm_num] using u.property⟩

def ordinaryTwoMiddle (b : Bool) (g : OneBoson) (u : (shiftedNumberPower Sector 1).domain) :
    (shiftedNumberPower Sector (1/2)).domain :=
  ordinaryWeightedChoice b g (1/2) (by norm_num) (ordinaryTwoInput u)

def ordinaryShiftedToField (f : OneBoson) (u : (shiftedNumberPower Sector (1/2)).domain) :
    (ordinaryField f).domain := ⟨u.val,by
      rw [ordinaryField_domain,numberPower_domain_eq Sector (1/2) (by norm_num)]
      exact u.property⟩

def ordinaryRootToZero (w : (shiftedNumberPower Sector (1/2)).domain) :
    (shiftedNumberPower Sector ((0:ℝ)+1/2)).domain :=
  ⟨w.val,by simpa only [zero_add] using w.property⟩

lemma ordinaryField_weighted_action (f : OneBoson) (w : (shiftedNumberPower Sector (1/2)).domain) :
    ordinaryField f (ordinaryShiftedToField f w) =
      (ordinaryWeightedChoice false f 0 le_rfl (ordinaryRootToZero w)).val +
      (ordinaryWeightedChoice true f 0 le_rfl (ordinaryRootToZero w)).val := by
  rw [ordinaryField_action]
  rfl

lemma shiftedNumberPower_zero_action (u : (shiftedNumberPower Sector 0).domain) :
    shiftedNumberPower Sector 0 u = u.val := by
  have h := (shiftedNumberPower Sector 0).mem_graph u
  let I := (LinearMap.id : Carrier →ₗ[ℂ] Carrier).toPMap ⊤
  have hI : (u.val,shiftedNumberPower Sector 0 u) ∈ I.graph :=
    (congrArg LinearPMap.graph (shiftedNumberPower_zero Sector)) ▸ h
  obtain ⟨x,hx,hy⟩ := I.mem_graph_iff.mp hI
  change x.val = shiftedNumberPower Sector 0 u at hy
  exact hy.symm.trans hx

lemma ordinaryTwoTerm_norm (b c : Bool) (f g : OneBoson) (u : (shiftedNumberPower Sector 1).domain) :
    ‖(ordinaryWeightedChoice b f 0 le_rfl (ordinaryRootToZero (ordinaryTwoMiddle c g u))).val‖ ≤
      Real.sqrt 2 * ‖f‖ * ‖g‖ * ‖shiftedNumberPower Sector 1 u‖ := by
  let w := ordinaryTwoMiddle c g u
  let v := ordinaryWeightedChoice b f 0 le_rfl (ordinaryRootToZero w)
  change ‖v.val‖ ≤ _
  have he₀ : shiftedNumberPower Sector (0+1/2) (ordinaryRootToZero w) = shiftedNumberPower Sector (1/2) w :=
    partialMap_action_eq_of_same_input (congrArg (shiftedNumberPower Sector) (zero_add (1/2:ℝ))) (ordinaryRootToZero w) w rfl
  have he₁ : shiftedNumberPower Sector (1/2+1/2) (ordinaryTwoInput u) = shiftedNumberPower Sector 1 u :=
    partialMap_action_eq_of_same_input (congrArg (shiftedNumberPower Sector) (show (1/2:ℝ)+1/2=1 by norm_num)) (ordinaryTwoInput u) u rfl
  calc
    ‖v.val‖ = ‖shiftedNumberPower Sector 0 v‖ := congrArg norm (shiftedNumberPower_zero_action v).symm
    _ ≤ ‖f‖ * ‖shiftedNumberPower Sector (1/2) w‖ := by
      rw [← he₀]
      simpa only [Real.rpow_zero,one_mul] using ordinaryWeightedChoice_norm b f 0 le_rfl (ordinaryRootToZero w)
    _ ≤ ‖f‖ * ((2:ℝ)^(1/2:ℝ) * ‖g‖ * ‖shiftedNumberPower Sector 1 u‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      rw [← he₁]
      exact ordinaryWeightedChoice_norm c g (1/2) (by norm_num) (ordinaryTwoInput u)
    _ = _ := by rw [Real.sqrt_eq_rpow]; ring

def ordinaryFieldCompositionInput (f g : OneBoson) (u : (shiftedNumberPower Sector 1).domain) :
    (ordinaryField f).domain :=
  ordinaryShiftedToField f (ordinaryTwoMiddle false g u) + ordinaryShiftedToField f (ordinaryTwoMiddle true g u)

def ordinaryOneToRoot (u : (shiftedNumberPower Sector 1).domain) :
    (shiftedNumberPower Sector (1/2)).domain :=
  ⟨u.val,shiftedNumberDomain_mono (by norm_num) u.property⟩

lemma ordinaryFieldCompositionInput_val (f g : OneBoson) (u : (shiftedNumberPower Sector 1).domain) :
    (ordinaryFieldCompositionInput f g u).val = ordinaryField g (ordinaryShiftedToField g (ordinaryOneToRoot u)) := by
  rw [ordinaryField_action]
  rfl

lemma ordinaryFieldComposition_norm (f g : OneBoson) (u : (shiftedNumberPower Sector 1).domain) :
    ‖ordinaryField f (ordinaryFieldCompositionInput f g u)‖ ≤
      4 * Real.sqrt 2 * ‖f‖ * ‖g‖ * ‖shiftedNumberPower Sector 1 u‖ := by
  change ‖(ordinaryField f).toFun (ordinaryShiftedToField f (ordinaryTwoMiddle false g u) +
    ordinaryShiftedToField f (ordinaryTwoMiddle true g u))‖ ≤ _
  rw [map_add]
  change ‖ordinaryField f (ordinaryShiftedToField f (ordinaryTwoMiddle false g u)) +
    ordinaryField f (ordinaryShiftedToField f (ordinaryTwoMiddle true g u))‖ ≤ _
  rw [ordinaryField_weighted_action,ordinaryField_weighted_action]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add (norm_add_le _ _) (norm_add_le _ _)).trans ?_
  linarith [ordinaryTwoTerm_norm false false f g u, ordinaryTwoTerm_norm true false f g u,
    ordinaryTwoTerm_norm false true f g u, ordinaryTwoTerm_norm true true f g u]

lemma ordinaryFieldSquare_vector_bound (f : Fin 3 → OneBoson) (u : (shiftedNumberPower Sector 1).domain) :
    ‖∑ j, ordinaryField (f j) (ordinaryFieldCompositionInput (f j) (f j) u)‖ ≤
      4 * Real.sqrt 2 * (∑ j, ‖f j‖^2) * ‖shiftedNumberPower Sector 1 u‖ := by
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun j _ => ordinaryFieldComposition_norm (f j) (f j) u)).trans ?_)
  rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  exact (by ring : 4 * Real.sqrt 2 * ‖f j‖ * ‖f j‖ * ‖shiftedNumberPower Sector 1 u‖ =
    4 * Real.sqrt 2 * ‖f j‖^2 * ‖shiftedNumberPower Sector 1 u‖).le

lemma ordinaryNumber_shiftedOne_domain :
    numberOperator.domain = (shiftedNumberPower Sector 1).domain := by
  change (numberDiagonal Sector).domain = _
  rw [← numberPower_one,numberPower_domain_eq Sector 1 zero_lt_one]

lemma physicalNumber_shiftedOne_domain :
    physicalNumberOperator.domain = (physicalShiftedNumberPower 1).domain := by
  have he : physicalNumberPower 1 = physicalNumberOperator := bochnerNumberPower_one _ Sector
  rw [← he,physicalNumberPower_domain_map,physicalShiftedNumberPower_domain_map]
  exact congrArg (fun D : Submodule ℂ ElectronBosonSum => D.map electronBosonUnitary.toLinearMap)
    (numberPower_domain_eq ElectronSector 1 zero_lt_one)

lemma twoFields_shiftedInput_mem_root (u : (physicalShiftedNumberPower 1).domain) :
    u.val ∈ (physicalNumberPower (1/2)).domain := by
  let z := physicalShiftedSectorInput 1 u
  have hs : z.val ∈ (shiftedNumberPower ElectronSector (1/2)).domain :=
    shiftedNumberDomain_mono (by norm_num) z.property
  have hn : z.val ∈ (numberPower ElectronSector (1/2)).domain :=
    (congrArg (fun D : Submodule ℂ ElectronBosonSum => z.val ∈ D)
      (numberPower_domain_eq ElectronSector (1/2) (by norm_num))).mpr hs
  rw [physicalNumberPower_domain_map]
  exact Submodule.mem_map.mpr ⟨z.val,hn,electronBosonUnitary.apply_symm_apply u.val⟩

lemma twoFields_first_root_graph (b : Bool) (G : BosonKernel ElectronL2) (u : (physicalShiftedNumberPower 1).domain) :
    ∃ w : (physicalNumberPower (1/2)).domain, (u.val,w.val) ∈ (fieldChoice b G).graph := by
  let z := physicalShiftedSectorInput 1 u
  have he : (1/2:ℝ)+1/2 = 1 := by norm_num
  let x : (shiftedNumberPower ElectronSector (1/2+1/2)).domain := ⟨z.val,by rw [he]; exact z.property⟩
  let y := sectorWeightedChoice physicalSectorKernel b G (1/2) (by norm_num) x
  have hy : electronBosonUnitary y.val ∈ (physicalNumberPower (1/2)).domain := by
    have h : y.val ∈ (numberPower ElectronSector (1/2)).domain :=
      (congrArg (fun D : Submodule ℂ ElectronBosonSum => y.val ∈ D)
        (numberPower_domain_eq ElectronSector (1/2) (by norm_num))).mpr y.property
    rw [physicalNumberPower_domain_map]
    exact Submodule.mem_map.mpr ⟨y.val,h,rfl⟩
  refine ⟨⟨electronBosonUnitary y.val,hy⟩,?_⟩
  have h₁ : (z.val,y.val) ∈ (sectorFieldChoice physicalSectorKernel b G).graph :=
    sectorWeightedChoice_graph physicalSectorKernel b G (1/2) (by norm_num) x
  have h := fieldChoice_graph_transport b G z.val y.val h₁
  have hz : electronBosonUnitary z.val = u.val := electronBosonUnitary.apply_symm_apply _
  rw [hz] at h
  exact h

lemma twoFields_generalizedField_graph_sum (F : BosonKernel ElectronL2)
    (u : (physicalNumberPower (1/2)).domain) (a c : Physical)
    (ha : (u.val,a) ∈ (fieldChoice false F).graph)
    (hc : (u.val,c) ∈ (fieldChoice true F).graph) :
    (u.val,a+c) ∈ (generalizedField F).graph := by
  let v : (generalizedField F).domain := u
  let A := generalizedAnnihilation F
  let C := generalizedCreation F
  let xa : A.domain := ⟨u.val,generalizedAnnihilation_mem_root F u⟩
  let xc : C.domain := ⟨u.val,generalizedCreation_mem_root F u⟩
  have ha' : A xa = a := A.mem_graph_snd_inj (A.mem_graph xa) ha rfl
  have hc' : C xc = c := C.mem_graph_snd_inj (C.mem_graph xc) hc rfl
  have he : generalizedField F v = A xa + C xc := generalizedField_action F v
  exact (generalizedField F).mem_graph_iff.mpr ⟨v,rfl,he.trans (congrArg₂ (·+·) ha' hc')⟩

lemma generalizedField_composition_estimate (F G : BosonKernel ElectronL2)
    (u : (physicalShiftedNumberPower 1).domain) :
    ∃ w v : Physical, (u.val,w) ∈ (generalizedField G).graph ∧ (w,v) ∈ (generalizedField F).graph ∧
      ‖v‖ ≤ 4*Real.sqrt 2*‖F‖*‖G‖*‖physicalShiftedNumberPower 1 u‖ := by
  obtain ⟨a,ha⟩ := twoFields_first_root_graph false G u
  obtain ⟨c,hc⟩ := twoFields_first_root_graph true G u
  let x : (physicalNumberPower (1/2)).domain := ⟨u.val,twoFields_shiftedInput_mem_root u⟩
  let a' : (generalizedField F).domain := a
  let c' : (generalizedField F).domain := c
  obtain ⟨a₁,v₁,ha₁,hv₁,b₁⟩ := twoField_composition false false F G u
  obtain ⟨a₂,v₂,ha₂,hv₂,b₂⟩ := twoField_composition true false F G u
  obtain ⟨c₁,v₃,hc₁,hv₃,b₃⟩ := twoField_composition false true F G u
  obtain ⟨c₂,v₄,hc₂,hv₄,b₄⟩ := twoField_composition true true F G u
  rw [← (fieldChoice false G).mem_graph_snd_inj ha ha₁ rfl] at hv₁
  rw [← (fieldChoice false G).mem_graph_snd_inj ha ha₂ rfl] at hv₂
  rw [← (fieldChoice true G).mem_graph_snd_inj hc hc₁ rfl] at hv₃
  rw [← (fieldChoice true G).mem_graph_snd_inj hc hc₂ rfl] at hv₄
  refine ⟨a.val+c.val,(v₁+v₂)+(v₃+v₄),twoFields_generalizedField_graph_sum G x a.val c.val ha hc,?_,?_⟩
  · exact (generalizedField F).graph.add_mem
      (twoFields_generalizedField_graph_sum F a v₁ v₂ hv₁ hv₂)
      (twoFields_generalizedField_graph_sum F c v₃ v₄ hv₃ hv₄)
  · refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) (norm_add_le _ _)).trans ?_)
    linarith

def generalizedFieldSquare (F : BosonKernel ElectronL2) (u : (physicalShiftedNumberPower 1).domain) : Physical :=
  (generalizedField_composition_estimate F F u).choose_spec.choose

lemma generalizedFieldSquare_bound (F : BosonKernel ElectronL2) (u : (physicalShiftedNumberPower 1).domain) :
    ‖generalizedFieldSquare F u‖ ≤ 4*Real.sqrt 2*‖F‖^2*‖physicalShiftedNumberPower 1 u‖ := by
  unfold generalizedFieldSquare
  exact (generalizedField_composition_estimate F F u).choose_spec.choose_spec.2.2.trans_eq (by ring)

lemma generalizedFieldSquare_graph (F : BosonKernel ElectronL2) (u : (physicalShiftedNumberPower 1).domain) :
    ∃ w : Physical, (u.val,w) ∈ (generalizedField F).graph ∧ (w,generalizedFieldSquare F u) ∈ (generalizedField F).graph :=
  ⟨(generalizedField_composition_estimate F F u).choose,
    (generalizedField_composition_estimate F F u).choose_spec.choose_spec.1,
    (generalizedField_composition_estimate F F u).choose_spec.choose_spec.2.1⟩

lemma generalizedFieldSquare_vector_bound (F : Fin 3 → BosonKernel ElectronL2)
    (u : (physicalShiftedNumberPower 1).domain) :
    ‖∑ j, generalizedFieldSquare (F j) u‖ ≤
      4*Real.sqrt 2*(∑ j, ‖F j‖^2)*‖physicalShiftedNumberPower 1 u‖ := by
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun j _ => generalizedFieldSquare_bound (F j) u)).trans ?_)
  rw [Finset.mul_sum,Finset.sum_mul]

lemma phaseFieldSquare_vector_bound (f : Fin 3 → OneBoson) (u : (physicalShiftedNumberPower 1).domain) :
    ‖∑ j, generalizedFieldSquare (phaseMultiplicationKernel (f j)) u‖ ≤
      4*Real.sqrt 2*(∑ j, ‖f j‖^2)*‖physicalShiftedNumberPower 1 u‖ := by
  simpa only [phaseMultiplicationKernel_norm] using
    generalizedFieldSquare_vector_bound (fun j => phaseMultiplicationKernel (f j)) u

end GW.Fock
