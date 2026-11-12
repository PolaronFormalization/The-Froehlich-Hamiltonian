module
public import GW.Fock.FockWeightedFields
public import GW.Fock.FockFieldDefinition
public import GW.Operators.BasicFree
@[expose] public section
noncomputable section
open MeasureTheory
namespace GW.Fock

section Sector
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {G : ℕ → Type*} [∀ n, NormedAddCommGroup (G n)] [∀ n, InnerProductSpace ℂ (G n)]
  (R : ∀ n, G n ≃ₗᵢ[ℂ] kernelFixed (E := E) n) (F : BosonKernel E)

def numberOneShiftedSector (u : (numberDiagonal G).domain) : (shiftedNumberPower G 1).domain :=
  ⟨u.val,by
    rw [← numberPower_domain_eq G 1 zero_lt_one,numberPower_one]
    exact u.property⟩

def numberOneForWeightedSector (u : (numberDiagonal G).domain) :
    (shiftedNumberPower G ((1/2:ℝ)+1/2)).domain :=
  ⟨u.val,by
    rw [show (1/2:ℝ)+1/2=1 by norm_num]
    exact (numberOneShiftedSector u).property⟩

def rootNumberAnnihilationSector (u : (numberDiagonal G).domain) : (numberPower G (1/2)).domain :=
  ⟨(weightedAnnihilationSectorOutput R F (1/2) (by norm_num) (numberOneForWeightedSector u)).val,
    by rw [numberPower_domain_eq G (1/2) (by norm_num)]
       exact (weightedAnnihilationSectorOutput R F (1/2) (by norm_num) (numberOneForWeightedSector u)).property⟩

def rootNumberCreationSector (u : (numberDiagonal G).domain) : (numberPower G (1/2)).domain :=
  ⟨(weightedCreationSectorOutput R F (1/2) (by norm_num) (numberOneForWeightedSector u)).val,
    by rw [numberPower_domain_eq G (1/2) (by norm_num)]
       exact (weightedCreationSectorOutput R F (1/2) (by norm_num) (numberOneForWeightedSector u)).property⟩

lemma rootNumberAnnihilationSector_bound (u : (numberDiagonal G).domain) :
    ‖numberPower G (1/2) (rootNumberAnnihilationSector R F u)‖ ≤ ‖F‖ * ‖numberDiagonal G u‖ := by
  let v := numberPower G (1/2) (rootNumberAnnihilationSector R F u)
  let w := numberDiagonal G u
  change ‖v‖ ≤ ‖F‖ * ‖w‖
  have h (n : ℕ) : ‖v n‖ ≤ ‖F‖ * ‖w (n+1)‖ := by
    change ‖numberPower G (1/2) (rootNumberAnnihilationSector R F u) n‖ ≤ ‖F‖ * ‖numberDiagonal G u (n+1)‖
    rw [numberPower_apply G (1/2) (by norm_num), numberDiagonal_apply]
    change ‖(((n:ℝ)^(1/2:ℝ) : ℝ):ℂ) •
      maximalSectorAnnihilation (sectorAnnihilation R F)
        (weightedAnnihilationSectorInput R F (1/2) (by norm_num) (numberOneForWeightedSector u)) n‖ ≤ _
    rw [maximalSectorAnnihilation_apply]
    simp only [norm_smul,Complex.norm_real,← Real.sqrt_eq_rpow,
      Real.norm_of_nonneg (Real.sqrt_nonneg (n:ℝ)),Complex.norm_natCast]
    change Real.sqrt (n:ℝ) * ‖sectorAnnihilation R F n (u.val (n+1))‖ ≤
      ‖F‖ * (((n+1:ℕ):ℝ) * ‖u.val (n+1)‖)
    have hm := ((sectorAnnihilation R F n).le_opNorm (u.val (n+1))).trans
      (mul_le_mul_of_nonneg_right (sectorAnnihilation_norm R F n) (norm_nonneg _))
    refine (mul_le_mul_of_nonneg_left hm (Real.sqrt_nonneg _)).trans ?_
    have hk : Real.sqrt (n:ℝ) * Real.sqrt ((n+1:ℕ):ℝ) ≤ ((n+1:ℕ):ℝ) := by
      calc
        _ ≤ Real.sqrt ((n+1:ℕ):ℝ) * Real.sqrt ((n+1:ℕ):ℝ) :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by push_cast; linarith)) (Real.sqrt_nonneg _)
        _ = _ := Real.mul_self_sqrt (Nat.cast_nonneg _)
    have ht := mul_le_mul_of_nonneg_right hk (mul_nonneg (norm_nonneg F) (norm_nonneg (u.val (n+1))))
    convert ht using 1 <;> ring
  apply (sq_le_sq₀ (norm_nonneg v) (mul_nonneg (norm_nonneg F) (norm_nonneg w))).mp
  have hv := (GW.Analysis.memℓp_two_iff_sq _).mp v.property
  have hw := (GW.Analysis.memℓp_two_iff_sq _).mp w.property
  have hw' := (summable_nat_add_iff 1).mpr hw
  rw [GW.Analysis.lp_norm_sq,mul_pow,GW.Analysis.lp_norm_sq]
  calc
    _ ≤ ∑' n, ‖F‖^2*‖w (n+1)‖^2 := by
      apply Summable.tsum_le_tsum _ hv (hw'.mul_left _)
      intro n
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (h n) 2
    _ = ‖F‖^2 * (∑' n, ‖w (n+1)‖^2) := tsum_mul_left
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      rw [hw.tsum_eq_zero_add]
      exact le_add_of_nonneg_left (sq_nonneg _)

lemma rootNumberCreationSector_bound (u : (numberDiagonal G).domain) :
    ‖numberPower G (1/2) (rootNumberCreationSector R F u)‖ ≤
      ‖F‖ * ‖shiftedNumberPower G 1 (numberOneShiftedSector u)‖ := by
  let v := numberPower G (1/2) (rootNumberCreationSector R F u)
  let w := shiftedNumberPower G 1 (numberOneShiftedSector u)
  change ‖v‖ ≤ ‖F‖ * ‖w‖
  apply sector_norm_from_shifted_bounds v w (norm_nonneg F)
  · change numberPower G (1/2) (rootNumberCreationSector R F u) 0 = 0
    rw [numberPower_apply G (1/2) (by norm_num)]
    change _ • maximalSectorCreation (sectorCreation R F)
      (weightedCreationSectorInput R F (1/2) (by norm_num) (numberOneForWeightedSector u)) 0 = 0
    rw [maximalSectorCreation_zero,smul_zero]
  · intro n
    change ‖numberPower G (1/2) (rootNumberCreationSector R F u) (n+1)‖ ≤
      ‖F‖ * ‖shiftedNumberPower G 1 (numberOneShiftedSector u) n‖
    rw [numberPower_apply G (1/2) (by norm_num),shiftedNumberPower_apply]
    change ‖(((((n+1:ℕ):ℝ)^(1/2:ℝ)) : ℝ):ℂ) •
      maximalSectorCreation (sectorCreation R F)
        (weightedCreationSectorInput R F (1/2) (by norm_num) (numberOneForWeightedSector u)) (n+1)‖ ≤ _
    rw [maximalSectorCreation_succ]
    simp only [Real.rpow_one,norm_smul,Complex.norm_real,
      ← Real.sqrt_eq_rpow, Real.norm_of_nonneg (Real.sqrt_nonneg ((n+1:ℕ):ℝ)),
      Real.norm_of_nonneg (show 0 ≤ (n:ℝ)+1 by positivity)]
    change Real.sqrt ((n+1:ℕ):ℝ) * ‖sectorCreation R F n (u.val n)‖ ≤
      ‖F‖ * (((n:ℝ)+1) * ‖u.val n‖)
    have hm := ((sectorCreation R F n).le_opNorm (u.val n)).trans
      (mul_le_mul_of_nonneg_right (sectorCreation_norm R F n) (norm_nonneg _))
    refine (mul_le_mul_of_nonneg_left hm (Real.sqrt_nonneg _)).trans_eq ?_
    calc
      _ = (Real.sqrt ((n+1:ℕ):ℝ) * Real.sqrt ((n+1:ℕ):ℝ)) * (‖F‖ * ‖u.val n‖) := by ring
      _ = _ := by rw [Real.mul_self_sqrt (Nat.cast_nonneg _),Nat.cast_add,Nat.cast_one]; ring

end Sector
def physicalRegNumberInput (u : physicalNumberOperator.domain) : (numberDiagonal ElectronSector).domain :=
  ⟨electronBosonUnitary.symm u.val,u.property⟩

def physicalRegShiftedNumberInput (u : physicalNumberOperator.domain) :
    (physicalShiftedNumberPower 1).domain :=
  physicalShiftedSectorOutput 1 (numberOneShiftedSector (physicalRegNumberInput u))

lemma physicalRegShiftedNumberInput_val (u : physicalNumberOperator.domain) :
    (physicalRegShiftedNumberInput u).val = u.val :=
  electronBosonUnitary.apply_symm_apply u.val

def physicalRegRootOutput (v : (numberPower ElectronSector (1/2)).domain) :
    (physicalNumberPower (1/2)).domain :=
  ⟨electronBosonUnitary v.val,bochnerNumberPower_unitary_mem volume Sector (1/2) v⟩

lemma physicalRegRootOutput_norm (v : (numberPower ElectronSector (1/2)).domain) :
    ‖physicalNumberPower (1/2) (physicalRegRootOutput v)‖ = ‖numberPower ElectronSector (1/2) v‖ := by
  have he := bochnerNumberPower_intertwines (volume : Measure GW.Space) Sector (1/2) v
  exact (congrArg norm he).trans (electronBosonUnitary.norm_map _)

def physicalRegAnnihilation (F : BosonKernel ElectronL2) (u : physicalNumberOperator.domain) :
    (physicalNumberPower (1/2)).domain :=
  physicalRegRootOutput (rootNumberAnnihilationSector physicalSectorKernel F (physicalRegNumberInput u))

def physicalRegCreation (F : BosonKernel ElectronL2) (u : physicalNumberOperator.domain) :
    (physicalNumberPower (1/2)).domain :=
  physicalRegRootOutput (rootNumberCreationSector physicalSectorKernel F (physicalRegNumberInput u))

lemma physicalRegAnnihilation_graph (F : BosonKernel ElectronL2) (u : physicalNumberOperator.domain) :
    (u.val,(physicalRegAnnihilation F u).val) ∈ (generalizedAnnihilation F).graph := by
  let v := physicalRegNumberInput u
  let a := maximalSectorAnnihilation (sectorAnnihilation physicalSectorKernel F)
  apply (representationTransport_graph electronBosonUnitary.symm a _).mpr
  change (v.val,electronBosonUnitary.symm (electronBosonUnitary (rootNumberAnnihilationSector physicalSectorKernel F v).val)) ∈ a.graph
  rw [electronBosonUnitary.symm_apply_apply]
  exact a.mem_graph (weightedAnnihilationSectorInput physicalSectorKernel F (1/2) (by norm_num) (numberOneForWeightedSector v))

lemma physicalRegCreation_graph (F : BosonKernel ElectronL2) (u : physicalNumberOperator.domain) :
    (u.val,(physicalRegCreation F u).val) ∈ (generalizedCreation F).graph := by
  let v := physicalRegNumberInput u
  let a := maximalSectorCreation (sectorCreation physicalSectorKernel F)
  apply (representationTransport_graph electronBosonUnitary.symm a _).mpr
  change (v.val,electronBosonUnitary.symm (electronBosonUnitary (rootNumberCreationSector physicalSectorKernel F v).val)) ∈ a.graph
  rw [electronBosonUnitary.symm_apply_apply]
  exact a.mem_graph (weightedCreationSectorInput physicalSectorKernel F (1/2) (by norm_num) (numberOneForWeightedSector v))

lemma physicalRegAnnihilation_norm (F : BosonKernel ElectronL2) (u : physicalNumberOperator.domain) :
    ‖physicalNumberPower (1/2) (physicalRegAnnihilation F u)‖ ≤ ‖F‖ * ‖physicalNumberOperator u‖ := by
  let v := physicalRegNumberInput u
  change ‖physicalNumberPower (1/2) (physicalRegRootOutput (rootNumberAnnihilationSector physicalSectorKernel F v))‖ ≤ _
  rw [physicalRegRootOutput_norm]
  have he := bochnerDiagonal_norm_eq (fun n => (n:ℝ)) u v rfl
  change ‖physicalNumberOperator u‖ = ‖numberDiagonal ElectronSector v‖ at he
  rw [he]
  exact rootNumberAnnihilationSector_bound physicalSectorKernel F v

lemma physicalRegShiftedNumberInput_norm (u : physicalNumberOperator.domain) :
    ‖physicalShiftedNumberPower 1 (physicalRegShiftedNumberInput u)‖ =
      ‖shiftedNumberPower ElectronSector 1 (numberOneShiftedSector (physicalRegNumberInput u))‖ :=
  physicalShiftedSectorOutput_norm 1 (numberOneShiftedSector (physicalRegNumberInput u))

lemma physicalRegCreation_norm (F : BosonKernel ElectronL2) (u : physicalNumberOperator.domain) :
    ‖physicalNumberPower (1/2) (physicalRegCreation F u)‖ ≤
      ‖F‖ * ‖physicalShiftedNumberPower 1 (physicalRegShiftedNumberInput u)‖ := by
  let v := physicalRegNumberInput u
  let w := rootNumberCreationSector physicalSectorKernel F v
  have h₁ := physicalRegRootOutput_norm w
  have h₂ := physicalRegShiftedNumberInput_norm u
  have h₃ := rootNumberCreationSector_bound physicalSectorKernel F v
  calc
    _ = ‖numberPower ElectronSector (1/2) w‖ := h₁
    _ ≤ ‖F‖ * ‖shiftedNumberPower ElectronSector 1 (numberOneShiftedSector v)‖ := h₃
    _ = _ := congrArg (‖F‖ * ·) h₂.symm

lemma regNumber_norm_le_shifted (u : physicalNumberOperator.domain) :
    ‖physicalNumberOperator u‖ ≤ ‖physicalShiftedNumberPower 1 (physicalRegShiftedNumberInput u)‖ := by
  let v := physicalRegNumberInput u
  let w := numberOneShiftedSector v
  have he₀ := bochnerDiagonal_norm_eq (fun n => (n:ℝ)) u v rfl
  have he₁ := physicalRegShiftedNumberInput_norm u
  change ‖physicalNumberOperator u‖ = ‖numberDiagonal ElectronSector v‖ at he₀
  rw [he₀,he₁]
  let a := numberDiagonal ElectronSector v
  let b := shiftedNumberPower ElectronSector 1 w
  have ha := (GW.Analysis.memℓp_two_iff_sq _).mp a.property
  have hb := (GW.Analysis.memℓp_two_iff_sq _).mp b.property
  change ‖a‖ ≤ ‖b‖
  apply (sq_le_sq₀ (norm_nonneg a) (norm_nonneg b)).mp
  rw [GW.Analysis.lp_norm_sq,GW.Analysis.lp_norm_sq]
  apply Summable.tsum_le_tsum _ ha hb
  intro n
  apply pow_le_pow_left₀ (norm_nonneg (a n)) _ 2
  change ‖numberDiagonal ElectronSector v n‖ ≤ ‖shiftedNumberPower ElectronSector 1 w n‖
  rw [numberDiagonal_apply,shiftedNumberPower_apply,Real.rpow_one,norm_smul,norm_smul,Complex.norm_natCast,Complex.norm_real,Real.norm_of_nonneg (show 0 ≤ (n:ℝ)+1 by positivity)]
  change (n:ℝ)*‖v.val n‖ ≤ ((n:ℝ)+1)*‖v.val n‖
  exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

def physicalRegFieldOutput (F : BosonKernel ElectronL2) (u : physicalNumberOperator.domain) :
    (physicalNumberPower (1/2)).domain :=
  physicalRegAnnihilation F u + physicalRegCreation F u

lemma physicalRegNumber_mem_root (u : physicalNumberOperator.domain) :
    u.val ∈ (physicalNumberPower (1/2)).domain := by
  let v := numberOneShiftedSector (physicalRegNumberInput u)
  have hv : v.val ∈ (shiftedNumberPower ElectronSector (1/2)).domain :=
    shiftedNumberDomain_mono (by norm_num) v.property
  have hn : v.val ∈ (numberPower ElectronSector (1/2)).domain :=
    (congrArg (fun D : Submodule ℂ ElectronBosonSum => v.val ∈ D)
      (numberPower_domain_eq ElectronSector (1/2) (by norm_num))).mpr hv
  rw [physicalNumberPower_domain_map]
  exact Submodule.mem_map.mpr ⟨v.val,hn,electronBosonUnitary.apply_symm_apply u.val⟩

lemma initialField_graph_of_components {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (C A : H →ₗ.[ℂ] H) (V : Submodule ℂ H) (hC : V ≤ C.domain) (hA : V ≤ A.domain)
    (u a c : H) (hu : u ∈ V) (ha : (u,a) ∈ A.graph) (hc : (u,c) ∈ C.graph) :
    (u,a+c) ∈ (initialField C A V hC hA).graph := by
  let x : (initialField C A V hC hA).domain := ⟨u,hu⟩
  apply (initialField C A V hC hA).mem_graph_iff.mpr
  refine ⟨x,rfl,?_⟩
  rw [initialField_action]
  exact congrArg₂ (·+·)
    (A.mem_graph_snd_inj (A.mem_graph ⟨u,hA hu⟩) ha rfl)
    (C.mem_graph_snd_inj (C.mem_graph ⟨u,hC hu⟩) hc rfl)

lemma physicalRegField_graph (F : BosonKernel ElectronL2) (u : physicalNumberOperator.domain) :
    (u.val,(physicalRegFieldOutput F u).val) ∈ (generalizedField F).graph :=
  initialField_graph_of_components (generalizedCreation F) (generalizedAnnihilation F)
    (physicalNumberPower (1/2)).domain
    (fun u hu => generalizedCreation_mem_root F ⟨u,hu⟩)
    (fun u hu => generalizedAnnihilation_mem_root F ⟨u,hu⟩)
    u.val (physicalRegAnnihilation F u).val (physicalRegCreation F u).val
    (physicalRegNumber_mem_root u) (physicalRegAnnihilation_graph F u) (physicalRegCreation_graph F u)

lemma physicalRegField_norm (F : BosonKernel ElectronL2) (u : physicalNumberOperator.domain) :
    ‖physicalNumberPower (1/2) (physicalRegFieldOutput F u)‖ ≤
      2 * ‖F‖ * ‖physicalShiftedNumberPower 1 (physicalRegShiftedNumberInput u)‖ := by
  change ‖(physicalNumberPower (1/2)).toFun (physicalRegAnnihilation F u + physicalRegCreation F u)‖ ≤ _
  rw [map_add]
  refine (norm_add_le _ _).trans ?_
  have hA := (physicalRegAnnihilation_norm F u).trans (mul_le_mul_of_nonneg_left
    (regNumber_norm_le_shifted u) (norm_nonneg _))
  have hC := physicalRegCreation_norm F u
  exact (add_le_add hA hC).trans_eq (by ring)

lemma physicalRegPhaseField_norm (f : OneBoson) (u : physicalNumberOperator.domain) :
    ‖physicalNumberPower (1/2) (physicalRegFieldOutput (phaseMultiplicationKernel f) u)‖ ≤
      2 * ‖f‖ * ‖physicalShiftedNumberPower 1 (physicalRegShiftedNumberInput u)‖ := by
  simpa only [phaseMultiplicationKernel_norm] using physicalRegField_norm (phaseMultiplicationKernel f) u

end GW.Fock
