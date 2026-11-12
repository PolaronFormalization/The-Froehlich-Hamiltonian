module
public import GW.Fock.FockAdjoints
public import GW.Fock.FockGeneralizedBounds
@[expose] public section
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace GW.Fock
section InitialField
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The initial field is defined on the prescribed subspace of both maximal domains. -/
def initialField (C A : H →ₗ.[ℂ] H) (V : Submodule ℂ H) (hC : V ≤ C.domain) (hA : V ≤ A.domain) :
    H →ₗ.[ℂ] H where
  domain := V
  toFun := A.toFun.comp (Submodule.inclusion hA) + C.toFun.comp (Submodule.inclusion hC)

lemma initialField_domain (C A : H →ₗ.[ℂ] H) (V : Submodule ℂ H)
    (hC : V ≤ C.domain) (hA : V ≤ A.domain) :
    (initialField C A V hC hA).domain = V := rfl

lemma initialField_action (C A : H →ₗ.[ℂ] H) (V : Submodule ℂ H)
    (hC : V ≤ C.domain) (hA : V ≤ A.domain) (u : (initialField C A V hC hA).domain) :
    initialField C A V hC hA u =
      A ⟨u,hA u.property⟩ + C ⟨u,hC u.property⟩ := rfl

lemma initialField_symmetric (C A : H →ₗ.[ℂ] H) (V : Submodule ℂ H)
    (hC : V ≤ C.domain) (hA : V ≤ A.domain)
    (hpair : ∀ (u : C.domain) (v : A.domain), ⟪C u,(v : H)⟫_ℂ = ⟪(u : H),A v⟫_ℂ) :
    (initialField C A V hC hA).IsFormalAdjoint (initialField C A V hC hA) := by
  intro u v
  let uc : C.domain := ⟨u,hC u.property⟩
  let ua : A.domain := ⟨u,hA u.property⟩
  let vc : C.domain := ⟨v,hC v.property⟩
  let va : A.domain := ⟨v,hA v.property⟩
  change ⟪A ua + C uc,(v : H)⟫_ℂ = ⟪(u : H),A va + C vc⟫_ℂ
  rw [inner_add_left,inner_add_right]
  have h₁ : ⟪(u : H),A va⟫_ℂ = ⟪C uc,(v : H)⟫_ℂ := (hpair uc va).symm
  have h₂ : ⟪(u : H),C vc⟫_ℂ = ⟪A ua,(v : H)⟫_ℂ := by
    calc
      _ = starRingEnd ℂ ⟪C vc,(u : H)⟫_ℂ := (inner_conj_symm _ _).symm
      _ = starRingEnd ℂ ⟪(v : H),A ua⟫_ℂ := congrArg (starRingEnd ℂ) (hpair vc ua)
      _ = _ := inner_conj_symm _ _
  rw [h₁,h₂,add_comm]

end InitialField

def generalizedField (F : BosonKernel ElectronL2) : Physical →ₗ.[ℂ] Physical :=
  initialField (generalizedCreation F) (generalizedAnnihilation F) (physicalNumberPower (1/2)).domain
    (fun u hu => generalizedCreation_mem_root F ⟨u,hu⟩)
    (fun u hu => generalizedAnnihilation_mem_root F ⟨u,hu⟩)

lemma generalizedField_domain (F : BosonKernel ElectronL2) :
    (generalizedField F).domain = (physicalNumberPower (1/2)).domain := rfl

lemma generalizedField_action (F : BosonKernel ElectronL2) (u : (generalizedField F).domain) :
    generalizedField F u =
      generalizedAnnihilation F ⟨u.val,generalizedAnnihilation_mem_root F u⟩ +
        generalizedCreation F ⟨u.val,generalizedCreation_mem_root F u⟩ := rfl

lemma generalizedField_dense (F : BosonKernel ElectronL2) :
    Dense ((generalizedField F).domain : Set Physical) :=
  bochnerDiagonal_dense volume Sector (numberPowerCoefficient (1/2))

lemma generalizedField_symmetric (F : BosonKernel ElectronL2) :
    (generalizedField F).IsFormalAdjoint (generalizedField F) := by
  apply initialField_symmetric
  intro u v
  have hd : Dense ((generalizedCreation F).domain : Set Physical) :=
    representationTransport_dense electronBosonUnitary.symm _
      (maximalSectorCreation_dense (generalizedCreationSector F))
  have he := generalizedCreation_adjoint_eq F
  have h : (v : Physical) ∈ (generalizedCreation F).adjoint.domain := he.symm ▸ v.property
  let va : (generalizedCreation F).adjoint.domain := ⟨v,h⟩
  have hp := GW.Operators.adjoint_pairing (generalizedCreation F) hd u va
  have hv : (generalizedCreation F).adjoint va = generalizedAnnihilation F v := by
    let w : Physical := (generalizedCreation F).adjoint va
    have hg : ((v : Physical),w) ∈ (generalizedCreation F).adjoint.graph :=
      (generalizedCreation F).adjoint.mem_graph va
    have hg' : ((v : Physical),w) ∈ (generalizedAnnihilation F).graph :=
      (congrArg LinearPMap.graph he) ▸ hg
    exact (generalizedAnnihilation F).mem_graph_snd_inj hg' ((generalizedAnnihilation F).mem_graph v) rfl
  exact hp.trans (congrArg (fun z : Physical => ⟪(u : Physical),z⟫_ℂ) hv)

def ordinaryCreationRootInput (f : OneBoson) (u : (numberPower Sector (1/2)).domain) :
    (ordinaryCreation f).domain :=
  ⟨u,creation_mem_shiftedRoot ordinarySectorKernel (ordinaryKernel f)
    (shiftedNumberInput Sector (1/2) (by norm_num) u)⟩

def ordinaryAnnihilationRootInput (f : OneBoson) (u : (numberPower Sector (1/2)).domain) :
    (ordinaryAnnihilation f).domain :=
  ⟨u,annihilation_mem_root ordinarySectorKernel (ordinaryKernel f) u⟩

def ordinaryField (f : OneBoson) : Carrier →ₗ.[ℂ] Carrier :=
  initialField (ordinaryCreation f) (ordinaryAnnihilation f) (numberPower Sector (1/2)).domain
    (fun u hu => (ordinaryCreationRootInput f ⟨u,hu⟩).property)
    (fun u hu => (ordinaryAnnihilationRootInput f ⟨u,hu⟩).property)

def ordinaryMomentumField (f : OneBoson) : Carrier →ₗ.[ℂ] Carrier := ordinaryField (Complex.I • f)

lemma ordinaryField_domain (f : OneBoson) :
    (ordinaryField f).domain = (numberPower Sector (1/2)).domain := rfl

lemma ordinaryField_action (f : OneBoson) (u : (ordinaryField f).domain) :
    ordinaryField f u =
      ordinaryAnnihilation f (ordinaryAnnihilationRootInput f u) +
        ordinaryCreation f (ordinaryCreationRootInput f u) := rfl

lemma ordinaryMomentumField_domain (f : OneBoson) :
    (ordinaryMomentumField f).domain = (numberPower Sector (1/2)).domain := rfl

lemma ordinaryField_dense (f : OneBoson) :
    Dense ((ordinaryField f).domain : Set Carrier) :=
  scalarDiagonal_dense Sector (numberPowerCoefficient (1/2))

lemma ordinaryField_symmetric (f : OneBoson) :
    (ordinaryField f).IsFormalAdjoint (ordinaryField f) := by
  apply initialField_symmetric
  exact creation_annihilation_pairing _ _ (sectorCreation_pairing ordinarySectorKernel (ordinaryKernel f))

lemma ordinaryMomentumField_symmetric (f : OneBoson) :
    (ordinaryMomentumField f).IsFormalAdjoint (ordinaryMomentumField f) :=
  ordinaryField_symmetric (Complex.I • f)

end GW.Fock
