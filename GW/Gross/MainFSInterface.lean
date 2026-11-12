module
public import GW.Fock.FockFrankSchlein
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace ENNReal
namespace GW.Gross
open GW.Fock

lemma main_FS_interface (f : OneBoson) (u : freeHamiltonian.domain) :
    ∃ ha : u.val ∈ (generalizedAnnihilation (phaseMultiplicationKernel f)).domain,
      ‖generalizedAnnihilation (phaseMultiplicationKernel f) ⟨u.val,ha⟩‖ ≤
          frankSchleinConstant f *
            ‖frankSchleinJointOperator ⟨u.val,frankSchlein_H0_mem_joint u⟩‖ ∧
      frankSchleinConstant f *
          ‖frankSchleinJointOperator ⟨u.val,frankSchlein_H0_mem_joint u⟩‖ ≤
        (1/2 : ℝ) * frankSchleinConstant f * ‖freeHamiltonian u + u.val‖ := by
  obtain ⟨ha,hb⟩ := frankSchlein_H0_bound f u
  let g : freeGraphOperator.domain := ⟨u.val,by rw [freeGraphOperator_domain];exact u.property⟩
  obtain ⟨hj,hjbound⟩ := freeGraph_mixed_rootNumber g
  have he : (⟨u.val,hj⟩ : frankSchleinJointOperator.domain) =
      ⟨u.val,frankSchlein_H0_mem_joint u⟩ := Subtype.ext rfl
  have hjb : ‖frankSchleinJointOperator ⟨u.val,frankSchlein_H0_mem_joint u⟩‖ ≤
      (1/2 : ℝ) * ‖freeGraphOperator g‖ := by
    change ‖frankSchleinJointOperator (⟨u.val,hj⟩ : frankSchleinJointOperator.domain)‖ ≤
      (1/2 : ℝ) * ‖freeGraphOperator g‖ at hjbound
    exact (congrArg (fun z => ‖frankSchleinJointOperator z‖) he).symm.trans_le hjbound
  have hg : freeGraphOperator g = freeHamiltonian u + u.val := freeGraphOperator_action g
  refine ⟨ha,hb,?_⟩
  calc
    _ ≤ frankSchleinConstant f * ((1/2 : ℝ) * ‖freeGraphOperator g‖) :=
      mul_le_mul_of_nonneg_left hjb (frankSchleinConstant_nonneg f)
    _ = (1/2 : ℝ) * frankSchleinConstant f * ‖freeHamiltonian u + u.val‖ := by
      rw [hg];ring

lemma main_FS_interface_difference (f₁ f₂ : OneBoson) (u : freeHamiltonian.domain) :
    ∃ ha : u.val ∈ (generalizedAnnihilation (phaseMultiplicationKernel (f₁-f₂))).domain,
      ‖generalizedAnnihilation (phaseMultiplicationKernel (f₁-f₂)) ⟨u.val,ha⟩‖ ≤
          frankSchleinConstant (f₁-f₂) *
            ‖frankSchleinJointOperator ⟨u.val,frankSchlein_H0_mem_joint u⟩‖ ∧
      frankSchleinConstant (f₁-f₂) *
          ‖frankSchleinJointOperator ⟨u.val,frankSchlein_H0_mem_joint u⟩‖ ≤
        (1/2 : ℝ) * frankSchleinConstant (f₁-f₂) * ‖freeHamiltonian u + u.val‖ :=
  main_FS_interface (f₁-f₂) u

end GW.Gross
