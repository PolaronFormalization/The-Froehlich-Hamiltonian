module
public import GW.Analysis.Fourier
public import GW.Fock.BochnerGraph
public import GW.Operators.CanonicalForm
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ENNReal
namespace GW.Fock
section DirectSumUnitary
variable {E F : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℂ (E n)]
  [∀ n, NormedAddCommGroup (F n)] [∀ n, InnerProductSpace ℂ (F n)]

def directSumUnitaryMap (U : ∀ n, E n ≃ₗᵢ[ℂ] F n) (u : lp E 2) : lp F 2 :=
  ⟨fun n => U n (u n),(GW.Analysis.memℓp_two_iff_sq _).mpr (by
    simp only [LinearIsometryEquiv.norm_map]
    exact (GW.Analysis.memℓp_two_iff_sq _).mp (lp.memℓp u))⟩

lemma directSumUnitaryMap_apply (U : ∀ n, E n ≃ₗᵢ[ℂ] F n) (u : lp E 2) (n : ℕ) :
    directSumUnitaryMap U u n = U n (u n) := rfl

def directSumUnitary (U : ∀ n, E n ≃ₗᵢ[ℂ] F n) : lp E 2 ≃ₗᵢ[ℂ] lp F 2 where
  toFun := directSumUnitaryMap U
  invFun := directSumUnitaryMap (fun n => (U n).symm)
  left_inv u := by
    apply lp.ext
    funext n
    exact (U n).symm_apply_apply (u n)
  right_inv u := by
    apply lp.ext
    funext n
    exact (U n).apply_symm_apply (u n)
  map_add' u v := by
    apply lp.ext
    funext n
    exact map_add (U n) (u n) (v n)
  map_smul' c u := by
    apply lp.ext
    funext n
    exact map_smul (U n) c (u n)
  norm_map' u := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [GW.Analysis.lp_norm_sq,GW.Analysis.lp_norm_sq]
    apply tsum_congr
    intro n
    exact congrArg (fun r : ℝ => r^2) ((U n).norm_map (u n))
end DirectSumUnitary

/-- The source's electron Fourier map, separately in every complete boson sector. -/
def sectorFourierUnitary : ElectronBosonSum ≃ₗᵢ[ℂ] ElectronBosonSum :=
  directSumUnitary (fun n => GW.Analysis.physicalFourierUnitary (H := Sector n))

lemma sectorFourierUnitary_apply (u : ElectronBosonSum) (n : ℕ) :
    sectorFourierUnitary u n = GW.Analysis.physicalFourierUnitary (H := Sector n) (u n) := rfl

/-- The specified transport T = F_oplus B^-1 on the EXISTING physical Hilbert space. -/
def freeFourierRepresentation : Physical ≃ₗᵢ[ℂ] ElectronBosonSum :=
  electronBosonUnitary.symm.trans sectorFourierUnitary
section MaximalDirectSum
variable (E : ℕ → Type*) [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℂ (E n)]
  (A : ∀ n, E n →ₗ.[ℂ] E n)

/-- The actual component graph with a square-summable output, not a formal diagonal expression. -/
def operatorSumGraph : Submodule ℂ (lp E 2 × lp E 2) where
  carrier := {p | ∀ n, (p.1 n,p.2 n) ∈ (A n).graph}
  zero_mem' := fun n => (A n).graph.zero_mem
  add_mem' := fun hp hq n => (A n).graph.add_mem (hp n) (hq n)
  smul_mem' := fun c _p hp n => (A n).graph.smul_mem c (hp n)

lemma operatorSumGraph_single_valued (p : lp E 2 × lp E 2) (hp : p ∈ operatorSumGraph E A)
    (h0 : p.1 = 0) : p.2 = 0 := by
  apply lp.ext
  funext n
  exact (A n).graph_fst_eq_zero_snd (hp n) (by rw [h0];rfl)

/-- This native graph constructor is used only after proving the actual graph single-valued. -/
def operatorSum : lp E 2 →ₗ.[ℂ] lp E 2 := (operatorSumGraph E A).toLinearPMap

lemma operatorSum_graph : (operatorSum E A).graph = operatorSumGraph E A :=
  Submodule.toLinearPMap_graph_eq _ (operatorSumGraph_single_valued E A)

lemma operatorSum_graph_iff (u v : lp E 2) : (u,v) ∈ (operatorSum E A).graph ↔
    ∀ n, (u n,v n) ∈ (A n).graph := by
  rw [operatorSum_graph]
  rfl

lemma operatorSum_component (u : (operatorSum E A).domain) (n : ℕ) :
    ((u : lp E 2) n,operatorSum E A u n) ∈ (A n).graph :=
  (operatorSum_graph_iff E A _ _).mp ((operatorSum E A).mem_graph u) n

lemma operatorSum_domain_iff (u : lp E 2) : u ∈ (operatorSum E A).domain ↔
    ∃ v : lp E 2, ∀ n, (u n,v n) ∈ (A n).graph := by
  rw [LinearPMap.mem_domain_iff]
  exact exists_congr (fun v => operatorSum_graph_iff E A u v)

lemma operatorSum_single_graph (n : ℕ) (u : (A n).domain) :
    (lp.single 2 n (u : E n),lp.single 2 n (A n u)) ∈ (operatorSum E A).graph := by
  rw [operatorSum_graph_iff]
  intro j
  by_cases hj : j = n
  · subst j
    simp only [lp.single_apply_self]
    exact (A n).mem_graph u
  · simp only [lp.single_apply_ne _ _ _ hj]
    exact (A j).graph.zero_mem

lemma operatorSum_dense (hA : ∀ n, Dense ((A n).domain : Set (E n))) :
    Dense ((operatorSum E A).domain : Set (lp E 2)) := by
  let C := (operatorSum E A).domain.topologicalClosure
  have hsingle (n : ℕ) (x : E n) : lp.single 2 n x ∈ C := by
    have hc : IsClosed {x : E n | lp.single 2 n x ∈ C} :=
      (operatorSum E A).domain.isClosed_topologicalClosure.preimage (lp.singleContinuousLinearMap ℂ E 2 n).continuous
    have hs : ((A n).domain : Set (E n)) ⊆ {x : E n | lp.single 2 n x ∈ C} := by
      intro x hx
      exact (operatorSum E A).domain.le_topologicalClosure
        ((operatorSum E A).mem_domain_of_mem_graph (operatorSum_single_graph E A n ⟨x,hx⟩))
    exact closure_minimal hs hc (hA n x)
  have hfinite (m : ℕ) (u : lp E 2) : cutoff E m u ∈ C := by
    rw [cutoff_sum]
    exact C.sum_mem (fun n _ => hsingle n (u n))
  intro u
  change u ∈ C
  exact (operatorSum E A).domain.isClosed_topologicalClosure.mem_of_tendsto
    (cutoff_tendsto E u) (Eventually.of_forall (fun m => hfinite m u))
def operatorSumInput (u : (operatorSum E A).domain) (n : ℕ) : (A n).domain :=
  ⟨(u : lp E 2) n,(A n).mem_domain_of_mem_graph (operatorSum_component E A u n)⟩

lemma operatorSum_apply_component (u : (operatorSum E A).domain) (n : ℕ) :
    A n (operatorSumInput E A u n) = operatorSum E A u n :=
  (A n).mem_graph_snd_inj ((A n).mem_graph (operatorSumInput E A u n))
    (operatorSum_component E A u n) rfl

lemma operatorSum_symmetric (hA : ∀ n, (A n).IsFormalAdjoint (A n)) :
    (operatorSum E A).IsFormalAdjoint (operatorSum E A) := by
  intro u v
  rw [lp.inner_eq_tsum,lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  rw [← operatorSum_apply_component E A u n,← operatorSum_apply_component E A v n]
  exact hA n (operatorSumInput E A u n) (operatorSumInput E A v n)

variable [∀ n, CompleteSpace (E n)]

lemma operatorSum_adjoint_component (hA : ∀ n, IsSelfAdjointOperator (A n))
    (v : (operatorSum E A).adjoint.domain) (n : ℕ) :
    ((v : lp E 2) n,(operatorSum E A).adjoint v n) ∈ (A n).graph := by
  have hd := operatorSum_dense E A (fun n => (hA n).1)
  have hw (a : (A n).domain) : ⟪A n a,(v : lp E 2) n⟫_ℂ =
      ⟪(a : E n),(operatorSum E A).adjoint v n⟫_ℂ := by
    have hsg := operatorSum_single_graph E A n a
    let x : (operatorSum E A).domain :=
      ⟨lp.single 2 n (a : E n),(operatorSum E A).mem_domain_of_mem_graph hsg⟩
    have hx : operatorSum E A x = lp.single 2 n (A n a) :=
      (operatorSum E A).mem_graph_snd_inj ((operatorSum E A).mem_graph x) hsg rfl
    have hp := GW.Operators.adjoint_pairing (operatorSum E A) hd x v
    rw [hx] at hp
    change ⟪lp.single 2 n (A n a),(v : lp E 2)⟫_ℂ =
      ⟪lp.single 2 n (a : E n),(operatorSum E A).adjoint v⟫_ℂ at hp
    simpa only [lp.inner_single_left] using hp
  have hg := (GW.Operators.adjoint_graph_iff (A n) (hA n).1
    ((v : lp E 2) n,(operatorSum E A).adjoint v n)).mpr hw
  rwa [(hA n).2] at hg

lemma operatorSum_selfadjoint (hA : ∀ n, IsSelfAdjointOperator (A n)) :
    IsSelfAdjointOperator (operatorSum E A) := by
  have hd := operatorSum_dense E A (fun n => (hA n).1)
  have hs : (operatorSum E A).IsFormalAdjoint (operatorSum E A) :=
    operatorSum_symmetric E A (fun n => by simpa only [(hA n).2] using
      (LinearPMap.adjoint_isFormalAdjoint (hA n).1))
  refine ⟨hd,le_antisymm ?_ (LinearPMap.IsFormalAdjoint.le_adjoint hd hs)⟩
  apply LinearPMap.le_of_le_graph
  intro p hp
  obtain ⟨v,hv⟩ := (operatorSum E A).adjoint.mem_graph_iff'.mp hp
  rw [← hv]
  exact (operatorSum_graph_iff E A _ _).mpr (operatorSum_adjoint_component E A hA v)

lemma operatorSum_nonnegative
    (hA : ∀ n (u : (A n).domain), 0 ≤ (⟪(u : E n),A n u⟫_ℂ).re)
    (u : (operatorSum E A).domain) : 0 ≤ (⟪(u : lp E 2),operatorSum E A u⟫_ℂ).re := by
  rw [lp.inner_eq_tsum,Complex.re_tsum (lp.summable_inner (u : lp E 2) (operatorSum E A u))]
  apply tsum_nonneg
  intro n
  rw [← operatorSum_apply_component E A u n]
  exact hA n (operatorSumInput E A u n)

end MaximalDirectSum

section RepresentationTransport
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (U : H ≃ₗᵢ[ℂ] K) (A : K →ₗ.[ℂ] K)

def representationInput : (A.domain.comap U.toLinearMap) →ₗ[ℂ] A.domain where
  toFun u := ⟨U u,u.property⟩
  map_add' u v := Subtype.ext (map_add U (u : H) (v : H))
  map_smul' c u := Subtype.ext (map_smul U c (u : H))

/-- Full maximal-domain transport between the actual two carriers. -/
def representationTransport : H →ₗ.[ℂ] H where
  domain := A.domain.comap U.toLinearMap
  toFun := U.symm.toLinearMap.comp (A.toFun.comp (representationInput U A))

lemma representationTransport_apply (u : (representationTransport U A).domain) :
    representationTransport U A u = U.symm (A (representationInput U A u)) := rfl

lemma representationTransport_domain (u : H) : u ∈ (representationTransport U A).domain ↔ U u ∈ A.domain := Iff.rfl

lemma representationTransport_action (u : (representationTransport U A).domain) :
    U (representationTransport U A u) = A (representationInput U A u) := U.apply_symm_apply _

lemma representationTransport_graph (p : H × H) :
    p ∈ (representationTransport U A).graph ↔ (U p.1,U p.2) ∈ A.graph := by
  constructor
  · intro hp
    obtain ⟨u,hu⟩ := (representationTransport U A).mem_graph_iff'.mp hp
    rw [← hu,representationTransport_action]
    exact A.mem_graph (representationInput U A u)
  · intro hp
    have hm : p.1 ∈ (representationTransport U A).domain := A.mem_domain_of_mem_graph hp
    let u : (representationTransport U A).domain := ⟨p.1,hm⟩
    have he : A (representationInput U A u) = U p.2 :=
      A.mem_graph_snd_inj (A.mem_graph (representationInput U A u)) hp rfl
    have ha : representationTransport U A u = p.2 := by
      apply U.injective
      rw [representationTransport_action,he]
    exact (representationTransport U A).mem_graph_iff.mpr ⟨u,rfl,ha⟩


lemma representationTransport_domain_image :
    (representationTransport U A).domain = A.domain.map U.symm.toLinearMap := by
  ext u
  constructor
  · intro hu; exact ⟨U u,hu,U.symm_apply_apply u⟩
  · rintro ⟨v,hv,rfl⟩
    change U (U.symm v) ∈ A.domain
    rw [U.apply_symm_apply]
    exact hv

lemma representationTransport_dense (hA : Dense (A.domain : Set K)) :
    Dense ((representationTransport U A).domain : Set H) := by
  change Dense (U ⁻¹' (A.domain : Set K))
  exact hA.preimage U.toHomeomorph.isOpenMap

def representationDomainEquiv : (representationTransport U A).domain ≃ₗ[ℂ] A.domain where
  toLinearMap := representationInput U A
  invFun v := ⟨U.symm v,by
    change U (U.symm v) ∈ A.domain
    simpa only [LinearIsometryEquiv.apply_symm_apply] using v.property⟩
  left_inv u := Subtype.ext (U.symm_apply_apply u)
  right_inv v := Subtype.ext (U.apply_symm_apply v)

lemma representation_inner_symm (a : K) (b : H) : ⟪U.symm a,b⟫_ℂ = ⟪a,U b⟫_ℂ := by
  simpa only [LinearIsometryEquiv.symm_symm] using U.symm.inner_map_eq_flip a b

lemma representationTransport_witness (y h : H) :
    (∀ u : (representationTransport U A).domain, ⟪representationTransport U A u,y⟫_ℂ = ⟪(u : H),h⟫_ℂ) ↔
    (∀ v : A.domain, ⟪A v,U y⟫_ℂ = ⟪(v : K),U h⟫_ℂ) := by
  constructor
  · intro hw v
    let u := (representationDomainEquiv U A).symm v
    have he := hw u
    change ⟪U.symm (A (representationInput U A u)),y⟫_ℂ = ⟪(u : H),h⟫_ℂ at he
    rw [representation_inner_symm,← U.inner_map_map (u : H) h] at he
    change ⟪A (representationInput U A u),U y⟫_ℂ = ⟪(representationInput U A u : K),U h⟫_ℂ at he
    have hu : representationInput U A u = v := (representationDomainEquiv U A).apply_symm_apply v
    rwa [hu] at he
  · intro hw u
    have he := hw (representationInput U A u)
    change ⟪A (representationInput U A u),U y⟫_ℂ = ⟪U (u : H),U h⟫_ℂ at he
    rw [U.inner_map_map] at he
    change ⟪U.symm (A (representationInput U A u)),y⟫_ℂ = ⟪(u : H),h⟫_ℂ
    rw [representation_inner_symm]
    exact he

variable [CompleteSpace H] [CompleteSpace K]

lemma representationTransport_adjoint (hA : Dense (A.domain : Set K)) :
    (representationTransport U A).adjoint = representationTransport U A.adjoint := by
  apply LinearPMap.eq_of_eq_graph
  ext p
  rw [GW.Operators.adjoint_graph_iff (representationTransport U A) (representationTransport_dense U A hA),
    representationTransport_graph,GW.Operators.adjoint_graph_iff A hA]
  exact representationTransport_witness U A p.1 p.2

lemma representationTransport_selfadjoint (hA : IsSelfAdjointOperator A) :
    IsSelfAdjointOperator (representationTransport U A) := by
  refine ⟨representationTransport_dense U A hA.1,?_⟩
  rw [representationTransport_adjoint U A hA.1,hA.2]

end RepresentationTransport

/-- Actual maximal Fourier-sector real multiplication on the established sector sum. -/
def fourierSectorMultiplier (m : ℕ → GW.Space → ℝ) : ElectronBosonSum →ₗ.[ℂ] ElectronBosonSum :=
  operatorSum ElectronSector (fun n => GW.Analysis.realMultiplier (H := Sector n) (m n) volume)

lemma fourierSectorMultiplier_selfadjoint {m : ℕ → GW.Space → ℝ} (hm : ∀ n, Measurable (m n)) :
    IsSelfAdjointOperator (fourierSectorMultiplier m) :=
  operatorSum_selfadjoint ElectronSector _ (fun n => GW.Analysis.realMultiplier_selfadjoint (hm n))

/-- Every later physical weight uses this same specified T, not a new isomorphic model. -/
def physicalSectorMultiplier (m : ℕ → GW.Space → ℝ) : Physical →ₗ.[ℂ] Physical :=
  representationTransport freeFourierRepresentation (fourierSectorMultiplier m)

lemma physicalSectorMultiplier_selfadjoint {m : ℕ → GW.Space → ℝ} (hm : ∀ n, Measurable (m n)) :
    IsSelfAdjointOperator (physicalSectorMultiplier m) :=
  representationTransport_selfadjoint _ _ (fourierSectorMultiplier_selfadjoint hm)


lemma realMultiplier_graph_ae {X B : Type*} [MeasurableSpace X] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] (μ : Measure X) (m : X → ℝ) (u v : Lp B 2 μ) :
    (u,v) ∈ (GW.Analysis.realMultiplier m μ).graph ↔
      (fun x => (m x : ℂ) • u x) =ᵐ[μ] v := by
  constructor
  · intro h
    obtain ⟨w,hw⟩ := (GW.Analysis.realMultiplier m μ).mem_graph_iff'.mp h
    have hu : (w : Lp B 2 μ) = u := congrArg Prod.fst hw
    have hv : GW.Analysis.realMultiplier m μ w = v := congrArg Prod.snd hw
    rw [← hu,← hv]
    exact GW.Analysis.realMultiplier_ae m w
  · intro h
    have hu : u ∈ (GW.Analysis.realMultiplier m μ).domain := ⟨v,h⟩
    have he : GW.Analysis.realMultiplier m μ ⟨u,hu⟩ = v :=
      (GW.Analysis.maximalMultiplier_eq_iff (fun x => (m x : ℂ)) ⟨u,hu⟩ v).mpr h
    exact (GW.Analysis.realMultiplier m μ).mem_graph_iff.mpr ⟨⟨u,hu⟩,rfl,he⟩

lemma fourierSectorMultiplier_domain (m : ℕ → GW.Space → ℝ) (u : ElectronBosonSum) :
    u ∈ (fourierSectorMultiplier m).domain ↔
      ∃ v : ElectronBosonSum, ∀ n, (fun p => (m n p : ℂ) • u n p) =ᵐ[volume] v n := by
  exact (operatorSum_domain_iff ElectronSector
    (fun n => GW.Analysis.realMultiplier (H := Sector n) (m n) volume) u).trans
      (exists_congr (fun v => forall_congr' (fun n => realMultiplier_graph_ae volume (m n) (u n) (v n))))

lemma fourierSectorMultiplier_weightDomain (m : ℕ → GW.Space → ℝ) :
    (fourierSectorMultiplier m).domain = GW.Spaces.sumWeightDomain
      (F := Sector) (fun _ : ℕ => (volume : Measure GW.Space)) m := by
  ext u
  exact fourierSectorMultiplier_domain m u

lemma physicalSectorMultiplier_domain (m : ℕ → GW.Space → ℝ) (u : Physical) :
    u ∈ (physicalSectorMultiplier m).domain ↔ freeFourierRepresentation u ∈
      GW.Spaces.sumWeightDomain (F := Sector) (fun _ : ℕ => (volume : Measure GW.Space)) m := by
  change u ∈ (representationTransport freeFourierRepresentation (fourierSectorMultiplier m)).domain ↔ _
  change freeFourierRepresentation u ∈ (fourierSectorMultiplier m).domain ↔ _
  exact Iff.of_eq (congrArg (fun D : Submodule ℂ ElectronBosonSum => freeFourierRepresentation u ∈ D)
    (fourierSectorMultiplier_weightDomain m))

set_option backward.isDefEq.respectTransparency.types false in
lemma physicalSectorMultiplier_action (m : ℕ → GW.Space → ℝ) (u : (physicalSectorMultiplier m).domain) (n : ℕ) :
    (fun p => (m n p : ℂ) • freeFourierRepresentation (u : Physical) n p) =ᵐ[volume]
      freeFourierRepresentation (physicalSectorMultiplier m u) n := by
  have he := representationTransport_action freeFourierRepresentation (fourierSectorMultiplier m) u
  change freeFourierRepresentation (physicalSectorMultiplier m u) =
    fourierSectorMultiplier m (representationInput freeFourierRepresentation (fourierSectorMultiplier m) u) at he
  rw [he]
  exact (realMultiplier_graph_ae volume (m n) _ _).mp
    (operatorSum_component ElectronSector _ (representationInput freeFourierRepresentation (fourierSectorMultiplier m) u) n)

lemma fourierSectorMultiplier_nonnegative (m : ℕ → GW.Space → ℝ) (hm0 : ∀ n p, 0 ≤ m n p)
    (u : (fourierSectorMultiplier m).domain) :
    0 ≤ (⟪(u : ElectronBosonSum),fourierSectorMultiplier m u⟫_ℂ).re :=
  operatorSum_nonnegative ElectronSector _ (fun n => GW.Operators.multiplier_nonnegative volume (m n) (hm0 n)) u

set_option backward.isDefEq.respectTransparency.types false in
lemma physicalSectorMultiplier_nonnegative (m : ℕ → GW.Space → ℝ) (hm0 : ∀ n p, 0 ≤ m n p)
    (u : (physicalSectorMultiplier m).domain) :
    0 ≤ (⟪(u : Physical),physicalSectorMultiplier m u⟫_ℂ).re := by
  rw [← freeFourierRepresentation.inner_map_map (u : Physical) (physicalSectorMultiplier m u)]
  have he := representationTransport_action freeFourierRepresentation (fourierSectorMultiplier m) u
  change freeFourierRepresentation (physicalSectorMultiplier m u) =
    fourierSectorMultiplier m (representationInput freeFourierRepresentation (fourierSectorMultiplier m) u) at he
  rw [he]
  exact fourierSectorMultiplier_nonnegative m hm0 (representationInput freeFourierRepresentation (fourierSectorMultiplier m) u)
/-- The manuscript's original, unshifted energy symbol. -/
def freeEnergySymbol (n : ℕ) (p : GW.Space) : ℝ := ‖p‖^2 + (n : ℝ)

lemma freeEnergySymbol_measurable (n : ℕ) : Measurable (freeEnergySymbol n) :=
  (continuous_norm.pow 2 |>.add continuous_const).measurable

lemma freeEnergySymbol_nonnegative (n : ℕ) (p : GW.Space) : 0 ≤ freeEnergySymbol n p :=
  add_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

/-- H0 acts on the existing Physical, with the full transported maximal multiplier domain. -/
def freeHamiltonian : Physical →ₗ.[ℂ] Physical := physicalSectorMultiplier freeEnergySymbol

lemma freeHamiltonian_selfadjoint : IsSelfAdjointOperator freeHamiltonian :=
  physicalSectorMultiplier_selfadjoint freeEnergySymbol_measurable


lemma freeHamiltonian_nonnegative (u : freeHamiltonian.domain) :
    0 ≤ (⟪(u : Physical),freeHamiltonian u⟫_ℂ).re :=
  physicalSectorMultiplier_nonnegative freeEnergySymbol freeEnergySymbol_nonnegative u

def freeNonnegativeData : GW.Operators.NonnegativeOperatorData Physical where
  operator := freeHamiltonian
  selfadjoint := freeHamiltonian_selfadjoint
  nonnegative := freeHamiltonian_nonnegative
/-- The actual positive energy and form weights in the specified Fourier representation. -/
def freeGraphWeight (n : ℕ) (p : GW.Space) : ℝ := 1 + freeEnergySymbol n p

def freeFormWeight (n : ℕ) (p : GW.Space) : ℝ := Real.sqrt (freeGraphWeight n p)

lemma freeGraphWeight_measurable (n : ℕ) : Measurable (freeGraphWeight n) :=
  measurable_const.add (freeEnergySymbol_measurable n)

lemma freeGraphWeight_one (n : ℕ) (p : GW.Space) : 1 ≤ freeGraphWeight n p := by
  exact le_add_of_nonneg_right (freeEnergySymbol_nonnegative n p)

lemma freeFormWeight_measurable (n : ℕ) : Measurable (freeFormWeight n) :=
  Real.continuous_sqrt.measurable.comp (freeGraphWeight_measurable n)

lemma freeFormWeight_one (n : ℕ) (p : GW.Space) : 1 ≤ freeFormWeight n p := by
  exact Real.one_le_sqrt.mpr (freeGraphWeight_one n p)

lemma freeFormWeight_sq (n : ℕ) (p : GW.Space) : freeFormWeight n p ^ 2 = freeGraphWeight n p :=
  Real.sq_sqrt ((zero_le_one.trans (freeGraphWeight_one n p)))

def freeFormOperator : Physical →ₗ.[ℂ] Physical := physicalSectorMultiplier freeFormWeight

def freeGraphOperator : Physical →ₗ.[ℂ] Physical := physicalSectorMultiplier freeGraphWeight

lemma freeFormOperator_selfadjoint : IsSelfAdjointOperator freeFormOperator :=
  physicalSectorMultiplier_selfadjoint freeFormWeight_measurable

lemma freeGraphOperator_selfadjoint : IsSelfAdjointOperator freeGraphOperator :=
  physicalSectorMultiplier_selfadjoint freeGraphWeight_measurable

section FreeWeightedCarrier
variable (w : ℕ → GW.Space → ℝ) (hw : ∀ n, Measurable (w n)) (hw1 : ∀ n p, 1 ≤ w n p)

/-- The existing Fourier-sector Hilbert space is the complete coordinate carrier for each weight. -/
def physicalWeightEmbedding : ElectronBosonSum →L[ℂ] Physical :=
  freeFourierRepresentation.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (GW.Spaces.sumReciprocal (F := Sector) (fun _ : ℕ => (volume : Measure GW.Space)) hw hw1)

lemma physicalWeightEmbedding_fourier (f : ElectronBosonSum) :
    freeFourierRepresentation (physicalWeightEmbedding w hw hw1 f) =
      GW.Spaces.sumReciprocal (F := Sector) (fun _ : ℕ => (volume : Measure GW.Space)) hw hw1 f :=
  freeFourierRepresentation.apply_symm_apply _

lemma physicalWeightEmbedding_mem (f : ElectronBosonSum) :
    physicalWeightEmbedding w hw hw1 f ∈ (physicalSectorMultiplier w).domain := by
  rw [physicalSectorMultiplier_domain,physicalWeightEmbedding_fourier]
  exact GW.Spaces.sumReciprocal_mem (F := Sector) (fun _ : ℕ => (volume : Measure GW.Space)) hw hw1 f

def physicalWeightInput (u : (physicalSectorMultiplier w).domain) :
    GW.Spaces.sumWeightDomain (F := Sector) (fun _ : ℕ => (volume : Measure GW.Space)) w :=
  ⟨freeFourierRepresentation u,(physicalSectorMultiplier_domain w u).mp u.property⟩

def physicalWeightProduct : (physicalSectorMultiplier w).domain →ₗ[ℂ] ElectronBosonSum :=
  freeFourierRepresentation.toLinearMap.comp (physicalSectorMultiplier w).toFun

lemma physicalWeightProduct_value (u : (physicalSectorMultiplier w).domain) :
    physicalWeightProduct w u = GW.Spaces.sumWeightValue (F := Sector)
      (fun _ : ℕ => (volume : Measure GW.Space)) (physicalWeightInput w u) := by
  apply lp.ext
  funext n
  apply Lp.ext
  exact (physicalSectorMultiplier_action w u n).symm.trans
    (GW.Spaces.sumWeightValue_ae (F := Sector) (fun _ : ℕ => (volume : Measure GW.Space)) (physicalWeightInput w u) n)

lemma physicalWeightEmbedding_product (u : (physicalSectorMultiplier w).domain) :
    physicalWeightEmbedding w hw hw1 (physicalWeightProduct w u) = (u : Physical) := by
  apply freeFourierRepresentation.injective
  rw [physicalWeightEmbedding_fourier,physicalWeightProduct_value]
  exact GW.Spaces.sumReciprocal_value (F := Sector) (fun _ : ℕ => (volume : Measure GW.Space)) hw hw1 (physicalWeightInput w u)

lemma physicalWeightEmbedding_injective : Function.Injective (physicalWeightEmbedding w hw hw1) := by
  intro f g h
  apply GW.Spaces.sumReciprocal_injective (F := Sector) (fun _ : ℕ => (volume : Measure GW.Space)) hw hw1
  have he := congrArg freeFourierRepresentation h
  simpa only [physicalWeightEmbedding_fourier] using he

lemma physicalWeightProduct_embedding (f : ElectronBosonSum) :
    physicalWeightProduct w ⟨physicalWeightEmbedding w hw hw1 f,physicalWeightEmbedding_mem w hw hw1 f⟩ = f := by
  apply physicalWeightEmbedding_injective w hw hw1
  exact physicalWeightEmbedding_product w hw hw1 _

lemma physicalWeightEmbedding_range : Set.range (physicalWeightEmbedding w hw hw1) =
    ((physicalSectorMultiplier w).domain : Set Physical) := by
  ext u
  constructor
  · rintro ⟨f,rfl⟩; exact physicalWeightEmbedding_mem w hw hw1 f
  · intro hu; exact ⟨physicalWeightProduct w ⟨u,hu⟩,physicalWeightEmbedding_product w hw hw1 ⟨u,hu⟩⟩

lemma physicalWeightEmbedding_norm : ‖physicalWeightEmbedding w hw hw1‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖freeFourierRepresentation.symm (GW.Spaces.sumReciprocal (F := Sector)
    (fun _ : ℕ => (volume : Measure GW.Space)) hw hw1 f)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map,one_mul]
  exact (ContinuousLinearMap.le_opNorm _ f).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (GW.Spaces.sumReciprocal_norm (F := Sector) (fun _ : ℕ => (volume : Measure GW.Space)) hw hw1) (norm_nonneg f))

def physicalWeightedGraph : GW.Spaces.WeightedGraph Physical ElectronBosonSum where
  domain := (physicalSectorMultiplier w).domain
  embedding := physicalWeightEmbedding w hw hw1
  embedding_injective := physicalWeightEmbedding_injective w hw hw1
  embedding_norm_le := physicalWeightEmbedding_norm w hw hw1
  embedding_dense := by
    change Dense (Set.range (physicalWeightEmbedding w hw hw1))
    rw [physicalWeightEmbedding_range]
    exact (physicalSectorMultiplier_selfadjoint hw).1
  product := physicalWeightProduct w
  embedding_mem := physicalWeightEmbedding_mem w hw hw1
  product_embedding := physicalWeightProduct_embedding w hw hw1
  embedding_product := physicalWeightEmbedding_product w hw hw1

end FreeWeightedCarrier

/-- The declared H1 and H2 use the same existing complete Fourier-sector carrier,
with their distinct, proved reciprocal embeddings into Physical. -/
def freeFormWeightedGraph : GW.Spaces.WeightedGraph Physical ElectronBosonSum :=
  physicalWeightedGraph freeFormWeight freeFormWeight_measurable freeFormWeight_one

def freeGraphWeightedGraph : GW.Spaces.WeightedGraph Physical ElectronBosonSum :=
  physicalWeightedGraph freeGraphWeight freeGraphWeight_measurable freeGraphWeight_one

abbrev FreeFormDomain := GW.Spaces.WeightedDomain freeFormWeightedGraph
abbrev FreeGraphDomain := GW.Spaces.WeightedDomain freeGraphWeightedGraph

lemma freeFormDomain_complete : CompleteSpace FreeFormDomain := inferInstance
lemma freeGraphDomain_complete : CompleteSpace FreeGraphDomain := inferInstance

lemma freeFormDomain_norm (u : FreeFormDomain) : ‖u‖ = ‖freeFormOperator u‖ := by
  change ‖freeFourierRepresentation (freeFormOperator u)‖ = ‖freeFormOperator u‖
  exact freeFourierRepresentation.norm_map _

lemma freeGraphDomain_norm (u : FreeGraphDomain) : ‖u‖ = ‖freeGraphOperator u‖ := by
  change ‖freeFourierRepresentation (freeGraphOperator u)‖ = ‖freeGraphOperator u‖
  exact freeFourierRepresentation.norm_map _


def freeFormDomainInclusion : FreeFormDomain →L[ℂ] Physical :=
  freeFormWeightedGraph.embedding.comp
    (GW.Spaces.weightedDomainIsometry freeFormWeightedGraph).toContinuousLinearEquiv.toContinuousLinearMap

def freeGraphDomainInclusion : FreeGraphDomain →L[ℂ] Physical :=
  freeGraphWeightedGraph.embedding.comp
    (GW.Spaces.weightedDomainIsometry freeGraphWeightedGraph).toContinuousLinearEquiv.toContinuousLinearMap

lemma freeFormDomainInclusion_apply (u : FreeFormDomain) :
    freeFormDomainInclusion u = (show freeFormWeightedGraph.domain from u).val :=
  GW.Spaces.weightedDomain_embedding freeFormWeightedGraph u

lemma freeGraphDomainInclusion_apply (u : FreeGraphDomain) :
    freeGraphDomainInclusion u = (show freeGraphWeightedGraph.domain from u).val :=
  GW.Spaces.weightedDomain_embedding freeGraphWeightedGraph u

lemma freeFormDomain_embedding (u : FreeFormDomain) : ‖freeFormDomainInclusion u‖ ≤ ‖u‖ := by
  have h := freeFormWeightedGraph.embedding.le_opNorm (GW.Spaces.weightedDomainIsometry freeFormWeightedGraph u)
  change ‖freeFormDomainInclusion u‖ ≤ _ at h
  exact h.trans (by simpa only [LinearIsometryEquiv.norm_map,one_mul] using
    mul_le_mul_of_nonneg_right freeFormWeightedGraph.embedding_norm_le (norm_nonneg u))

lemma sumWeightDomain_add_one (m : ℕ → GW.Space → ℝ) :
    GW.Spaces.sumWeightDomain (F := Sector) (fun _ : ℕ => (volume : Measure GW.Space)) (fun n p => 1+m n p) =
      GW.Spaces.sumWeightDomain (F := Sector) (fun _ : ℕ => (volume : Measure GW.Space)) m := by
  ext u
  constructor
  · rintro ⟨v,hv⟩
    refine ⟨v-u,fun n => ?_⟩
    filter_upwards [hv n,Lp.coeFn_sub (v n) (u n)] with p hp hs
    change (m n p : ℂ) • u n p = (v n-u n) p
    rw [hs]
    change _ = v n p-u n p
    rw [← hp,Complex.ofReal_add,Complex.ofReal_one,add_smul,one_smul,add_sub_cancel_left]
  · rintro ⟨v,hv⟩
    refine ⟨u+v,fun n => ?_⟩
    filter_upwards [hv n,Lp.coeFn_add (u n) (v n)] with p hp hs
    change ((1+m n p : ℝ) : ℂ) • u n p = (u n+v n) p
    rw [hs]
    change _ = u n p+v n p
    rw [← hp,Complex.ofReal_add,Complex.ofReal_one,add_smul,one_smul]

lemma freeGraphOperator_domain : freeGraphOperator.domain = freeHamiltonian.domain := by
  ext u
  change u ∈ (physicalSectorMultiplier freeGraphWeight).domain ↔ u ∈ (physicalSectorMultiplier freeEnergySymbol).domain
  rw [physicalSectorMultiplier_domain,physicalSectorMultiplier_domain]
  exact Iff.of_eq (congrArg (fun D : Submodule ℂ ElectronBosonSum => freeFourierRepresentation u ∈ D)
    (sumWeightDomain_add_one freeEnergySymbol))

set_option backward.isDefEq.respectTransparency.types false in
lemma freeGraphOperator_action (u : freeGraphOperator.domain) :
    freeGraphOperator u = freeHamiltonian ⟨u,by rw [← freeGraphOperator_domain];exact u.property⟩ + (u : Physical) := by
  let v : freeHamiltonian.domain := ⟨u,by rw [← freeGraphOperator_domain];exact u.property⟩
  apply freeFourierRepresentation.injective
  rw [map_add]
  apply lp.ext
  funext n
  apply Lp.ext
  filter_upwards [physicalSectorMultiplier_action freeGraphWeight u n,
    physicalSectorMultiplier_action freeEnergySymbol v n,
    Lp.coeFn_add (freeFourierRepresentation (freeHamiltonian v) n) (freeFourierRepresentation (u : Physical) n)] with p hg he ha
  change freeFourierRepresentation (freeGraphOperator u) n p =
    (freeFourierRepresentation (freeHamiltonian v) n + freeFourierRepresentation (u : Physical) n) p
  rw [ha]
  simp only [Pi.add_apply]
  change (freeGraphWeight n p : ℂ) • freeFourierRepresentation (u : Physical) n p =
    freeFourierRepresentation (freeGraphOperator u) n p at hg
  change (freeEnergySymbol n p : ℂ) • freeFourierRepresentation (u : Physical) n p =
    freeFourierRepresentation (freeHamiltonian v) n p at he
  rw [← hg,← he]
  change ((1+freeEnergySymbol n p : ℝ) : ℂ) • freeFourierRepresentation (u : Physical) n p =
    (freeEnergySymbol n p : ℂ) • freeFourierRepresentation (u : Physical) n p + freeFourierRepresentation (u : Physical) n p
  rw [Complex.ofReal_add,Complex.ofReal_one,add_smul,one_smul,add_comm]

/-- The source pointwise comparison, squared and integrated before claiming the smaller domain. -/
lemma realMultiplier_domination {X B : Type*} [MeasurableSpace X] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] (μ : Measure X) (a b : X → ℝ) (ha : Measurable a)
    {C : ℝ} (hC : 0 ≤ C) (hab : ∀ x, |a x| ≤ C * |b x|)
    (u : (GW.Analysis.realMultiplier (H := B) b μ).domain) :
    ∃ hu : (u : Lp B 2 μ) ∈ (GW.Analysis.realMultiplier (H := B) a μ).domain,
      ‖GW.Analysis.realMultiplier (H := B) a μ ⟨(u : Lp B 2 μ),hu⟩‖ ≤ C * ‖GW.Analysis.realMultiplier (H := B) b μ u‖ := by
  have hb : ∀ᵐ x ∂μ, ‖(a x : ℂ) • (u : Lp B 2 μ) x‖ ≤ C * ‖GW.Analysis.realMultiplier (H := B) b μ u x‖ := by
    filter_upwards [GW.Analysis.realMultiplier_ae b u] with x hx
    rw [← hx,norm_smul,norm_smul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (hab x) (norm_nonneg _)).trans_eq (mul_assoc _ _ _)
  have hm : MemLp (fun x => (a x : ℂ) • (u : Lp B 2 μ) x) 2 μ :=
    (Lp.memLp (GW.Analysis.realMultiplier (H := B) b μ u)).of_le_mul
      ((Complex.continuous_ofReal.measurable.comp ha).aestronglyMeasurable.smul (Lp.memLp (u : Lp B 2 μ)).aestronglyMeasurable) hb
  let hu : (u : Lp B 2 μ) ∈ (GW.Analysis.realMultiplier (H := B) a μ).domain :=
    (GW.Analysis.realMultiplier_domain a (u : Lp B 2 μ)).mpr hm
  refine ⟨hu,?_⟩
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [GW.Analysis.realMultiplier_ae a ⟨(u : Lp B 2 μ),hu⟩,hb] with x hx hbx
  rwa [← hx]

section SumDomination
variable (E : ℕ → Type*) [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℂ (E n)]
    (A B : ∀ n, E n →ₗ.[ℂ] E n) {C : ℝ} (hC : 0 ≤ C)

include hC in
lemma operatorSum_domination
    (hAB : ∀ n (u : (B n).domain), ∃ hu : (u : E n) ∈ (A n).domain,
      ‖A n ⟨u,hu⟩‖ ≤ C * ‖B n u‖) (u : (operatorSum E B).domain) :
    ∃ hu : (u : lp E 2) ∈ (operatorSum E A).domain,
      ‖operatorSum E A ⟨u,hu⟩‖ ≤ C * ‖operatorSum E B u‖ := by
  let ha n := Classical.choose (hAB n (operatorSumInput E B u n))
  let v n := A n ⟨(u : lp E 2) n,ha n⟩
  have hv n : ‖v n‖ ≤ C * ‖operatorSum E B u n‖ := by
    have h := Classical.choose_spec (hAB n (operatorSumInput E B u n))
    exact h.trans_eq (congrArg (fun x : E n => C * ‖x‖) (operatorSum_apply_component E B u n))
  have hb n : ‖v n‖^2 ≤ C^2 * ‖operatorSum E B u n‖^2 := by
    have h := (sq_le_sq₀ (norm_nonneg (v n)) (mul_nonneg hC (norm_nonneg _))).mpr (hv n)
    simpa only [mul_pow] using h
  have hs := (GW.Analysis.memℓp_two_iff_sq _).mp (lp.memℓp (operatorSum E B u))
  have ht : Summable (fun n => C^2 * ‖operatorSum E B u n‖^2) := hs.mul_left _
  have hvs : Summable (fun n => ‖v n‖^2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hb ht
  let V : lp E 2 := GW.Analysis.squareSumVector v hvs
  have hg : ((u : lp E 2),V) ∈ (operatorSum E A).graph := by
    apply (operatorSum_graph_iff E A _ _).mpr
    intro n
    exact (A n).mem_graph ⟨(u : lp E 2) n,ha n⟩
  have hu := (operatorSum E A).mem_domain_of_mem_graph hg
  have he : operatorSum E A ⟨u,hu⟩ = V :=
    (operatorSum E A).mem_graph_snd_inj ((operatorSum E A).mem_graph ⟨u,hu⟩) hg rfl
  refine ⟨hu,?_⟩
  rw [he]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  rw [mul_pow,GW.Analysis.lp_norm_sq,GW.Analysis.lp_norm_sq]
  have hsum := Summable.tsum_le_tsum hb hvs ht
  change (∑' n, ‖v n‖^2) ≤ C^2 * ∑' n, ‖operatorSum E B u n‖^2
  simpa only [tsum_mul_left] using hsum
end SumDomination

lemma fourierSectorMultiplier_domination (a b : ℕ → GW.Space → ℝ) (ha : ∀ n, Measurable (a n))
    {C : ℝ} (hC : 0 ≤ C) (hab : ∀ n p, |a n p| ≤ C * |b n p|)
    (u : (fourierSectorMultiplier b).domain) :
    ∃ hu : (u : ElectronBosonSum) ∈ (fourierSectorMultiplier a).domain,
      ‖fourierSectorMultiplier a ⟨u,hu⟩‖ ≤ C * ‖fourierSectorMultiplier b u‖ :=
  operatorSum_domination ElectronSector _ _ hC
    (fun n v => realMultiplier_domination volume (a n) (b n) (ha n) hC (hab n) v) u

lemma physicalSectorMultiplier_domination (a b : ℕ → GW.Space → ℝ) (ha : ∀ n, Measurable (a n))
    {C : ℝ} (hC : 0 ≤ C) (hab : ∀ n p, |a n p| ≤ C * |b n p|)
    (u : (physicalSectorMultiplier b).domain) :
    ∃ hu : (u : Physical) ∈ (physicalSectorMultiplier a).domain,
      ‖physicalSectorMultiplier a ⟨u,hu⟩‖ ≤ C * ‖physicalSectorMultiplier b u‖ := by
  let v := representationInput freeFourierRepresentation (fourierSectorMultiplier b) u
  obtain ⟨hm,hbound⟩ := fourierSectorMultiplier_domination a b ha hC hab v
  have hu : (u : Physical) ∈ (physicalSectorMultiplier a).domain := hm
  let ua : (physicalSectorMultiplier a).domain := ⟨u,hu⟩
  refine ⟨hu,?_⟩
  have hA : freeFourierRepresentation (physicalSectorMultiplier a ua) = fourierSectorMultiplier a ⟨v,hm⟩ :=
    representationTransport_action freeFourierRepresentation (fourierSectorMultiplier a) ua
  have hB : freeFourierRepresentation (physicalSectorMultiplier b u) = fourierSectorMultiplier b v :=
    representationTransport_action freeFourierRepresentation (fourierSectorMultiplier b) u
  calc
    _ = ‖freeFourierRepresentation (physicalSectorMultiplier a ua)‖ := (freeFourierRepresentation.norm_map _).symm
    _ = ‖fourierSectorMultiplier a ⟨v,hm⟩‖ := congrArg norm hA
    _ ≤ C * ‖fourierSectorMultiplier b v‖ := hbound
    _ = C * ‖physicalSectorMultiplier b u‖ := by rw [← hB,LinearIsometryEquiv.norm_map]

lemma fourierSectorMultiplier_constant_graph (a : ℕ → ℝ) (u v : ElectronBosonSum) :
    (u,v) ∈ (fourierSectorMultiplier (fun n _ => a n)).graph ↔ ∀ n, v n = (a n : ℂ) • u n := by
  change (u,v) ∈ (operatorSum ElectronSector
    (fun n => GW.Analysis.realMultiplier (H := Sector n) (fun _ : GW.Space => a n) volume)).graph ↔ _
  rw [operatorSum_graph_iff]
  apply forall_congr'
  intro n
  rw [realMultiplier_graph_ae]
  constructor
  · intro h
    apply Lp.ext
    exact h.symm.trans (Lp.coeFn_smul (a n : ℂ) (u n)).symm
  · intro h
    have hs := Lp.coeFn_smul (a n : ℂ) (u n)
    rw [← h] at hs
    exact hs.symm

lemma fourierSectorMultiplier_constant (a : ℕ → ℝ) :
    fourierSectorMultiplier (fun n _ => a n) = scalarDiagonal ElectronSector a := by
  apply LinearPMap.eq_of_eq_graph
  ext p
  exact (fourierSectorMultiplier_constant_graph a p.1 p.2).trans
    (scalarDiagonal_graph_iff ElectronSector a p).symm

lemma sectorFourier_constant_graph (a : ℕ → ℝ) (u v : ElectronBosonSum) :
    (sectorFourierUnitary u,sectorFourierUnitary v) ∈ (scalarDiagonal ElectronSector a).graph ↔
      (u,v) ∈ (scalarDiagonal ElectronSector a).graph := by
  rw [scalarDiagonal_graph_iff,scalarDiagonal_graph_iff]
  apply forall_congr'
  intro n
  change GW.Analysis.physicalFourierUnitary (H := Sector n) (v n) =
    (a n : ℂ) • GW.Analysis.physicalFourierUnitary (H := Sector n) (u n) ↔ _
  rw [← map_smul]
  exact (GW.Analysis.physicalFourierUnitary (H := Sector n)).injective.eq_iff

lemma physicalSectorMultiplier_constant (a : ℕ → ℝ) :
    physicalSectorMultiplier (fun n _ => a n) = bochnerDiagonal volume Sector a := by
  have hb : bochnerDiagonal volume Sector a =
      representationTransport electronBosonUnitary.symm (scalarDiagonal ElectronSector a) := by
    rfl
  apply LinearPMap.eq_of_eq_graph
  ext p
  change p ∈ (representationTransport freeFourierRepresentation (fourierSectorMultiplier (fun n _ => a n))).graph ↔ _
  rw [hb,representationTransport_graph,representationTransport_graph,fourierSectorMultiplier_constant]
  exact sectorFourier_constant_graph a _ _

def freeMomentumSquare : Physical →ₗ.[ℂ] Physical := physicalSectorMultiplier (fun _ p => ‖p‖^2)
def freeMomentumModulus : Physical →ₗ.[ℂ] Physical := physicalSectorMultiplier (fun _ p => ‖p‖)
def freeRootNumber : Physical →ₗ.[ℂ] Physical := physicalSectorMultiplier (fun n _ => Real.sqrt (n : ℝ))

lemma physicalNumber_eq_sectorMultiplier :
    physicalNumberOperator = physicalSectorMultiplier (fun n _ => (n : ℝ)) :=
  (physicalSectorMultiplier_constant (fun n => (n : ℝ))).symm

lemma sumWeightDomain_add_mem (a b : ℕ → GW.Space → ℝ) (u : ElectronBosonSum)
    (ha : u ∈ GW.Spaces.sumWeightDomain (F := Sector) (fun _ : ℕ => (volume : Measure GW.Space)) a)
    (hb : u ∈ GW.Spaces.sumWeightDomain (F := Sector) (fun _ : ℕ => (volume : Measure GW.Space)) b) :
    u ∈ GW.Spaces.sumWeightDomain (F := Sector) (fun _ : ℕ => (volume : Measure GW.Space)) (fun n p => a n p+b n p) := by
  obtain ⟨v,hv⟩ := ha
  obtain ⟨w,hw⟩ := hb
  refine ⟨v+w,fun n => ?_⟩
  filter_upwards [hv n,hw n,Lp.coeFn_add (v n) (w n)] with p hp hq hs
  change ((a n p+b n p : ℝ) : ℂ) • u n p = (v n+w n) p
  rw [hs]
  simp only [Pi.add_apply]
  rw [← hp,← hq,Complex.ofReal_add,add_smul]

lemma freeHamiltonian_momentum_mem (u : freeHamiltonian.domain) :
    (u : Physical) ∈ freeMomentumSquare.domain := by
  have h := physicalSectorMultiplier_domination (fun _ p => ‖p‖^2) freeEnergySymbol
    (fun _ => continuous_norm.measurable.pow_const 2) zero_le_one
    (fun n p => by
      rw [abs_of_nonneg (sq_nonneg _),abs_of_nonneg (freeEnergySymbol_nonnegative n p),one_mul]
      exact le_add_of_nonneg_right (Nat.cast_nonneg n)) u
  exact h.choose

lemma freeHamiltonian_number_mem (u : freeHamiltonian.domain) :
    (u : Physical) ∈ physicalNumberOperator.domain := by
  rw [physicalNumber_eq_sectorMultiplier]
  have h := physicalSectorMultiplier_domination (fun n _ => (n : ℝ)) freeEnergySymbol
    (fun _ => measurable_const) zero_le_one (fun n p => by
      rw [abs_of_nonneg (Nat.cast_nonneg n),abs_of_nonneg (freeEnergySymbol_nonnegative n p),one_mul]
      exact le_add_of_nonneg_left (sq_nonneg _)) u
  exact h.choose

lemma freeHamiltonian_domain_intersection :
    freeHamiltonian.domain = freeMomentumSquare.domain ⊓ physicalNumberOperator.domain := by
  ext u
  constructor
  · intro hu
    exact ⟨freeHamiltonian_momentum_mem ⟨u,hu⟩,freeHamiltonian_number_mem ⟨u,hu⟩⟩
  · rintro ⟨hp,hn⟩
    rw [physicalNumber_eq_sectorMultiplier] at hn
    apply (physicalSectorMultiplier_domain freeEnergySymbol u).mpr
    exact sumWeightDomain_add_mem (fun _ p => ‖p‖^2) (fun n _ => (n : ℝ)) (freeFourierRepresentation u)
      ((physicalSectorMultiplier_domain _ u).mp hp) ((physicalSectorMultiplier_domain _ u).mp hn)

lemma physicalSectorMultiplier_composition (a b : ℕ → GW.Space → ℝ)
    (u : Physical) (ha : u ∈ (physicalSectorMultiplier a).domain)
    (hab : u ∈ (physicalSectorMultiplier (fun n p => b n p*a n p)).domain) :
    ∃ hb : physicalSectorMultiplier a ⟨u,ha⟩ ∈ (physicalSectorMultiplier b).domain,
      physicalSectorMultiplier b ⟨physicalSectorMultiplier a ⟨u,ha⟩,hb⟩ =
        physicalSectorMultiplier (fun n p => b n p*a n p) ⟨u,hab⟩ := by
  let v := physicalSectorMultiplier a ⟨u,ha⟩
  let w := physicalSectorMultiplier (fun n p => b n p*a n p) ⟨u,hab⟩
  have hw (n : ℕ) : (fun p => (b n p : ℂ) • freeFourierRepresentation v n p) =ᵐ[volume]
      freeFourierRepresentation w n := by
    filter_upwards [physicalSectorMultiplier_action a ⟨u,ha⟩ n,
      physicalSectorMultiplier_action (fun n p => b n p*a n p) ⟨u,hab⟩ n] with p h₁ h₂
    change (b n p : ℂ) • freeFourierRepresentation v n p = freeFourierRepresentation w n p
    change (a n p : ℂ) • freeFourierRepresentation u n p = freeFourierRepresentation v n p at h₁
    change ((b n p*a n p : ℝ) : ℂ) • freeFourierRepresentation u n p = freeFourierRepresentation w n p at h₂
    rw [← h₁,← h₂,Complex.ofReal_mul,smul_smul]
  have hb : v ∈ (physicalSectorMultiplier b).domain :=
    (physicalSectorMultiplier_domain b v).mpr ⟨freeFourierRepresentation w,hw⟩
  refine ⟨hb,?_⟩
  apply freeFourierRepresentation.injective
  apply lp.ext
  funext n
  apply Lp.ext
  exact (physicalSectorMultiplier_action b ⟨v,hb⟩ n).symm.trans (hw n)

lemma two_sqrt_mul_le_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * Real.sqrt a * Real.sqrt b ≤ a+b := by
  nlinarith [sq_nonneg (Real.sqrt a-Real.sqrt b),Real.sq_sqrt ha,Real.sq_sqrt hb]

def mixedNumberMomentumSymbol (n : ℕ) (p : GW.Space) : ℝ := Real.sqrt ((n : ℝ)+1) * ‖p‖
def mixedRootNumberSymbol (n : ℕ) (p : GW.Space) : ℝ := Real.sqrt (n : ℝ) * Real.sqrt (1+‖p‖^2)

lemma mixedNumberMomentum_measurable (n : ℕ) : Measurable (mixedNumberMomentumSymbol n) :=
  measurable_const.mul continuous_norm.measurable

lemma mixedRootNumber_measurable (n : ℕ) : Measurable (mixedRootNumberSymbol n) :=
  measurable_const.mul (Real.continuous_sqrt.measurable.comp (measurable_const.add (continuous_norm.pow 2).measurable))

lemma mixedNumberMomentum_bound (n : ℕ) (p : GW.Space) :
    |mixedNumberMomentumSymbol n p| ≤ (1/2 : ℝ) * |freeGraphWeight n p| := by
  have hn : (0 : ℝ) ≤ (n : ℝ)+1 := by positivity
  have h := two_sqrt_mul_le_add hn (sq_nonneg ‖p‖)
  rw [Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg p)] at h
  rw [abs_of_nonneg (show 0 ≤ mixedNumberMomentumSymbol n p from mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)),
    abs_of_nonneg (zero_le_one.trans (freeGraphWeight_one n p))]
  change Real.sqrt ((n : ℝ)+1)*‖p‖ ≤ (1/2 : ℝ)*(1+(‖p‖^2+(n : ℝ)))
  linarith

lemma mixedRootNumber_bound (n : ℕ) (p : GW.Space) :
    |mixedRootNumberSymbol n p| ≤ (1/2 : ℝ) * |freeGraphWeight n p| := by
  have hp : (0 : ℝ) ≤ 1+‖p‖^2 := by positivity
  have h := two_sqrt_mul_le_add (Nat.cast_nonneg (α := ℝ) n) hp
  rw [abs_of_nonneg (show 0 ≤ mixedRootNumberSymbol n p from mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)),
    abs_of_nonneg (zero_le_one.trans (freeGraphWeight_one n p))]
  change Real.sqrt (n : ℝ)*Real.sqrt (1+‖p‖^2) ≤ (1/2 : ℝ)*(1+(‖p‖^2+(n : ℝ)))
  linarith

lemma freeGraph_mixed_momentum (u : freeGraphOperator.domain) :
    ∃ hu : (u : Physical) ∈ (physicalSectorMultiplier mixedNumberMomentumSymbol).domain,
      ‖physicalSectorMultiplier mixedNumberMomentumSymbol ⟨u,hu⟩‖ ≤ (1/2 : ℝ)*‖freeGraphOperator u‖ :=
  physicalSectorMultiplier_domination mixedNumberMomentumSymbol freeGraphWeight
    mixedNumberMomentum_measurable (by norm_num) mixedNumberMomentum_bound u

lemma freeGraph_mixed_rootNumber (u : freeGraphOperator.domain) :
    ∃ hu : (u : Physical) ∈ (physicalSectorMultiplier mixedRootNumberSymbol).domain,
      ‖physicalSectorMultiplier mixedRootNumberSymbol ⟨u,hu⟩‖ ≤ (1/2 : ℝ)*‖freeGraphOperator u‖ :=
  physicalSectorMultiplier_domination mixedRootNumberSymbol freeGraphWeight
    mixedRootNumber_measurable (by norm_num) mixedRootNumber_bound u

lemma physicalShiftedNumberPower_eq_sectorMultiplier (r : ℝ) :
    physicalShiftedNumberPower r = physicalSectorMultiplier (fun n _ => ((n : ℝ)+1)^r) :=
  (physicalSectorMultiplier_constant (fun n => ((n : ℝ)+1)^r)).symm

lemma physicalNumberHalf_eq_sectorMultiplier :
    physicalNumberPower (1/2 : ℝ) = physicalSectorMultiplier (fun n _ => Real.sqrt (n : ℝ)) := by
  have h : numberPowerCoefficient (1/2 : ℝ) = fun (n : ℕ) => Real.sqrt (n : ℝ) := by
    funext n
    simp [numberPowerCoefficient,Real.sqrt_eq_rpow]
  change bochnerDiagonal volume Sector (numberPowerCoefficient (1/2 : ℝ)) = _
  rw [h]
  exact (physicalSectorMultiplier_constant (fun n => Real.sqrt (n : ℝ))).symm

lemma physicalShiftedNumberHalf_eq_sectorMultiplier :
    physicalShiftedNumberPower (1/2 : ℝ) = physicalSectorMultiplier (fun n _ => Real.sqrt ((n : ℝ)+1)) := by
  simpa only [Real.sqrt_eq_rpow] using physicalShiftedNumberPower_eq_sectorMultiplier (1/2 : ℝ)

lemma freeRootNumber_eq : freeRootNumber = physicalNumberPower (1/2 : ℝ) :=
  physicalNumberHalf_eq_sectorMultiplier.symm

lemma freeGraph_shiftedNumber_bound (u : freeGraphOperator.domain) :
    ∃ hu : (u : Physical) ∈ (physicalShiftedNumberPower 1).domain,
      ‖physicalShiftedNumberPower 1 ⟨u,hu⟩‖ ≤ ‖freeGraphOperator u‖ := by
  have h := physicalSectorMultiplier_domination (fun n _ => (n : ℝ)+1) freeGraphWeight
    (fun _ => measurable_const) zero_le_one (fun n p => by
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)+1),
        abs_of_nonneg (zero_le_one.trans (freeGraphWeight_one n p)),one_mul]
      change (n : ℝ)+1 ≤ 1+(‖p‖^2+(n : ℝ))
      nlinarith [sq_nonneg ‖p‖,sq_nonneg (Real.sqrt (1+‖p‖^2)-1)]) u
  have he : physicalShiftedNumberPower 1 = physicalSectorMultiplier (fun n _ => (n : ℝ)+1) := by
    simpa only [Real.rpow_one] using physicalShiftedNumberPower_eq_sectorMultiplier 1
  rw [he]
  obtain ⟨hu,hbound⟩ := h
  refine ⟨hu,?_⟩
  change ‖physicalSectorMultiplier (fun n _ => (n : ℝ)+1) ⟨u,hu⟩‖ ≤
    ‖physicalSectorMultiplier freeGraphWeight u‖
  simpa only [one_mul] using hbound

lemma freeGraph_momentum_mem (u : freeGraphOperator.domain) : (u : Physical) ∈ freeMomentumModulus.domain := by
  have h := physicalSectorMultiplier_domination (fun _ p => ‖p‖) freeGraphWeight
    (fun _ => continuous_norm.measurable) zero_le_one (fun n p => by
      rw [abs_of_nonneg (norm_nonneg _),abs_of_nonneg (zero_le_one.trans (freeGraphWeight_one n p)),one_mul]
      change ‖p‖ ≤ 1+(‖p‖^2+(n : ℝ))
      nlinarith [sq_nonneg (‖p‖-1),Nat.cast_nonneg (α := ℝ) n]) u
  exact h.choose

lemma freeGraph_mixed_momentum_composition (u : freeGraphOperator.domain) :
    ∃ hp : (u : Physical) ∈ freeMomentumModulus.domain,
      ∃ hn : freeMomentumModulus ⟨u,hp⟩ ∈ (physicalShiftedNumberPower (1/2 : ℝ)).domain,
        ‖physicalShiftedNumberPower (1/2 : ℝ) ⟨freeMomentumModulus ⟨u,hp⟩,hn⟩‖ ≤
          (1/2 : ℝ)*‖freeGraphOperator u‖ := by
  rw [physicalShiftedNumberHalf_eq_sectorMultiplier]
  have hp := freeGraph_momentum_mem u
  obtain ⟨hm,hbound⟩ := freeGraph_mixed_momentum u
  obtain ⟨hn,hact⟩ := physicalSectorMultiplier_composition (fun _ p => ‖p‖)
    (fun n _ => Real.sqrt ((n : ℝ)+1)) u hp hm
  refine ⟨hp,hn,?_⟩
  exact (congrArg (fun x : Physical => ‖x‖) hact).le.trans hbound

lemma freeGraph_regularizedMomentum_mem (u : freeGraphOperator.domain) :
    (u : Physical) ∈ (physicalSectorMultiplier (fun _ p => Real.sqrt (1+‖p‖^2))).domain := by
  have h := physicalSectorMultiplier_domination (fun _ p => Real.sqrt (1+‖p‖^2)) freeGraphWeight
    (fun _ => Real.continuous_sqrt.measurable.comp (measurable_const.add (continuous_norm.pow 2).measurable))
    zero_le_one (fun n p => by
      rw [abs_of_nonneg (Real.sqrt_nonneg _),abs_of_nonneg (zero_le_one.trans (freeGraphWeight_one n p)),one_mul]
      have hp : (0 : ℝ) ≤ 1+‖p‖^2 := by positivity
      have hs := Real.sq_sqrt hp
      have hz := Real.sqrt_nonneg (1+‖p‖^2)
      have hn := Nat.cast_nonneg (α := ℝ) n
      change Real.sqrt (1+‖p‖^2) ≤ 1+(‖p‖^2+(n : ℝ))
      nlinarith [sq_nonneg ‖p‖,sq_nonneg (Real.sqrt (1+‖p‖^2)-1)]) u
  exact h.choose

lemma freeGraph_mixed_rootNumber_composition (u : freeGraphOperator.domain) :
    ∃ hp : (u : Physical) ∈ (physicalSectorMultiplier (fun _ p => Real.sqrt (1+‖p‖^2))).domain,
      ∃ hn : physicalSectorMultiplier (fun _ p => Real.sqrt (1+‖p‖^2)) ⟨u,hp⟩ ∈ (physicalNumberPower (1/2 : ℝ)).domain,
        ‖physicalNumberPower (1/2 : ℝ)
          ⟨physicalSectorMultiplier (fun _ p => Real.sqrt (1+‖p‖^2)) ⟨u,hp⟩,hn⟩‖ ≤ (1/2 : ℝ)*‖freeGraphOperator u‖ := by
  rw [physicalNumberHalf_eq_sectorMultiplier]
  have hp := freeGraph_regularizedMomentum_mem u
  obtain ⟨hm,hbound⟩ := freeGraph_mixed_rootNumber u
  obtain ⟨hn,hact⟩ := physicalSectorMultiplier_composition (fun _ p => Real.sqrt (1+‖p‖^2))
    (fun n _ => Real.sqrt (n : ℝ)) u hp hm
  refine ⟨hp,hn,?_⟩
  exact (congrArg (fun x : Physical => ‖x‖) hact).le.trans hbound

lemma realMultiplier_quadratic_weight {X B : Type*} [MeasurableSpace X] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] (μ : Measure X) (a b c : X → ℝ) (hc : Measurable c)
    (hcsq : ∀ x, c x^2 = 1+a x^2+b x^2) (u : Lp B 2 μ)
    (ha : u ∈ (GW.Analysis.realMultiplier (H := B) a μ).domain)
    (hb : u ∈ (GW.Analysis.realMultiplier (H := B) b μ).domain) :
    ∃ hmem : u ∈ (GW.Analysis.realMultiplier (H := B) c μ).domain,
      ‖GW.Analysis.realMultiplier c μ ⟨u,hmem⟩‖^2 = ‖u‖^2+
        ‖GW.Analysis.realMultiplier a μ ⟨u,ha⟩‖^2+‖GW.Analysis.realMultiplier b μ ⟨u,hb⟩‖^2 := by
  let A := GW.Analysis.realMultiplier a μ ⟨u,ha⟩
  let Bv := GW.Analysis.realMultiplier b μ ⟨u,hb⟩
  have hi := ((Lp.memLp u).integrable_norm_pow (p := 2) (by norm_num)).add
    ((Lp.memLp A).integrable_norm_pow (p := 2) (by norm_num)) |>.add
    ((Lp.memLp Bv).integrable_norm_pow (p := 2) (by norm_num))
  have he : (fun x => ‖(c x : ℂ) • u x‖^2) =ᵐ[μ] fun x => ‖u x‖^2+‖A x‖^2+‖Bv x‖^2 := by
    filter_upwards [GW.Analysis.realMultiplier_ae a ⟨u,ha⟩,GW.Analysis.realMultiplier_ae b ⟨u,hb⟩] with x hx hy
    change ‖(c x : ℂ) • u x‖^2 = ‖u x‖^2+‖A x‖^2+‖Bv x‖^2
    change (a x : ℂ) • u x = A x at hx
    change (b x : ℂ) • u x = Bv x at hy
    rw [← hx,← hy,norm_smul,norm_smul,norm_smul,mul_pow,mul_pow,mul_pow,
      Complex.norm_real,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,Real.norm_eq_abs,
      sq_abs,sq_abs,sq_abs,hcsq]
    ring
  have hm : u ∈ (GW.Analysis.realMultiplier (H := B) c μ).domain := by
    apply (GW.Analysis.realMultiplier_domain c u).mpr
    apply (memLp_two_iff_integrable_sq_norm
      ((Complex.continuous_ofReal.measurable.comp hc).aestronglyMeasurable.smul (Lp.memLp u).aestronglyMeasurable)).mpr
    exact hi.congr he.symm
  refine ⟨hm,?_⟩
  rw [GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
  calc
    _ = ∫ x, ‖u x‖^2+‖A x‖^2+‖Bv x‖^2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [GW.Analysis.realMultiplier_ae c ⟨u,hm⟩,he] with x hx heq
      rw [← hx]
      exact heq
    _ = ((∫ x, ‖u x‖^2 ∂μ)+(∫ x, ‖A x‖^2 ∂μ))+(∫ x, ‖Bv x‖^2 ∂μ) := by
      have iu := (Lp.memLp u).integrable_norm_pow (p := 2) (by norm_num)
      have ia := (Lp.memLp A).integrable_norm_pow (p := 2) (by norm_num)
      have ib := (Lp.memLp Bv).integrable_norm_pow (p := 2) (by norm_num)
      have h1 : (∫ x, ‖u x‖^2+‖A x‖^2+‖Bv x‖^2 ∂μ) =
          (∫ x, ‖u x‖^2+‖A x‖^2 ∂μ)+(∫ x, ‖Bv x‖^2 ∂μ) := integral_add (iu.add ia) ib
      have h2 : (∫ x, ‖u x‖^2+‖A x‖^2 ∂μ) = (∫ x, ‖u x‖^2 ∂μ)+(∫ x, ‖A x‖^2 ∂μ) :=
        integral_add iu ia
      exact h1.trans (congrArg (fun r : ℝ => r+(∫ x, ‖Bv x‖^2 ∂μ)) h2)
    _ = _ := by
      rw [← GW.Analysis.l2_norm_sq (𝕜 := ℂ) u,← GW.Analysis.l2_norm_sq (𝕜 := ℂ) A,
        ← GW.Analysis.l2_norm_sq (𝕜 := ℂ) Bv]

section SumQuadratic
variable (E : ℕ → Type*) [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℂ (E n)]
  (A B C : ∀ n, E n →ₗ.[ℂ] E n)

lemma operatorSum_quadratic
    (h : ∀ n (x : E n) (ha : x ∈ (A n).domain) (hb : x ∈ (B n).domain),
      ∃ hc : x ∈ (C n).domain, ‖C n ⟨x,hc⟩‖^2 = ‖x‖^2+‖A n ⟨x,ha⟩‖^2+‖B n ⟨x,hb⟩‖^2)
    (u : lp E 2) (ha : u ∈ (operatorSum E A).domain) (hb : u ∈ (operatorSum E B).domain) :
    ∃ hc : u ∈ (operatorSum E C).domain,
      ‖operatorSum E C ⟨u,hc⟩‖^2 = ‖u‖^2+‖operatorSum E A ⟨u,ha⟩‖^2+‖operatorSum E B ⟨u,hb⟩‖^2 := by
  let a n := operatorSumInput E A ⟨u,ha⟩ n
  let b n := operatorSumInput E B ⟨u,hb⟩ n
  let hc n := Classical.choose (h n (u n) (a n).property (b n).property)
  let z n := C n ⟨u n,hc n⟩
  let v := operatorSum E A ⟨u,ha⟩
  let w := operatorSum E B ⟨u,hb⟩
  have hz n : ‖z n‖^2 = ‖u n‖^2+‖v n‖^2+‖w n‖^2 := by
    calc
      _ = ‖u n‖^2+‖A n (a n)‖^2+‖B n (b n)‖^2 :=
        Classical.choose_spec (h n (u n) (a n).property (b n).property)
      _ = _ := by
        rw [operatorSum_apply_component E A ⟨u,ha⟩ n,operatorSum_apply_component E B ⟨u,hb⟩ n]
  have hu := (GW.Analysis.memℓp_two_iff_sq _).mp (lp.memℓp u)
  have hv := (GW.Analysis.memℓp_two_iff_sq _).mp (lp.memℓp v)
  have hw := (GW.Analysis.memℓp_two_iff_sq _).mp (lp.memℓp w)
  have hzs : Summable (fun n => ‖z n‖^2) := by simpa only [hz] using (hu.add hv).add hw
  let Z : lp E 2 := GW.Analysis.squareSumVector z hzs
  have hg : (u,Z) ∈ (operatorSum E C).graph :=
    (operatorSum_graph_iff E C _ _).mpr (fun n => (C n).mem_graph ⟨u n,hc n⟩)
  have hm := (operatorSum E C).mem_domain_of_mem_graph hg
  have hZ : operatorSum E C ⟨u,hm⟩ = Z :=
    (operatorSum E C).mem_graph_snd_inj ((operatorSum E C).mem_graph ⟨u,hm⟩) hg rfl
  refine ⟨hm,?_⟩
  rw [hZ]
  calc
    ‖Z‖^2 = ∑' n, ‖z n‖^2 := GW.Analysis.lp_norm_sq _
    _ = ∑' n, (‖u n‖^2+‖v n‖^2+‖w n‖^2) := tsum_congr hz
    _ = ((∑' n, ‖u n‖^2)+(∑' n, ‖v n‖^2))+(∑' n, ‖w n‖^2) :=
      ((hu.add hv).tsum_add hw).trans (congrArg (fun r : ℝ => r+(∑' n, ‖w n‖^2)) (hu.tsum_add hv))
    _ = _ := by rw [← GW.Analysis.lp_norm_sq u,← GW.Analysis.lp_norm_sq v,← GW.Analysis.lp_norm_sq w]
end SumQuadratic

lemma physicalSectorMultiplier_norm (m : ℕ → GW.Space → ℝ) (u : (physicalSectorMultiplier m).domain) :
    ‖physicalSectorMultiplier m u‖ =
      ‖fourierSectorMultiplier m (representationInput freeFourierRepresentation (fourierSectorMultiplier m) u)‖ :=
  freeFourierRepresentation.symm.norm_map _

lemma physicalSectorMultiplier_quadratic (a b c : ℕ → GW.Space → ℝ)
    (hc : ∀ n, Measurable (c n)) (hc2 : ∀ n p, c n p^2 = 1+a n p^2+b n p^2)
    (u : Physical) (ha : u ∈ (physicalSectorMultiplier a).domain)
    (hb : u ∈ (physicalSectorMultiplier b).domain) :
    ∃ hm : u ∈ (physicalSectorMultiplier c).domain,
      ‖physicalSectorMultiplier c ⟨u,hm⟩‖^2 = ‖u‖^2+
        ‖physicalSectorMultiplier a ⟨u,ha⟩‖^2+‖physicalSectorMultiplier b ⟨u,hb⟩‖^2 := by
  obtain ⟨hm,hs⟩ := operatorSum_quadratic ElectronSector
    (fun n => GW.Analysis.realMultiplier (H := Sector n) (a n) volume)
    (fun n => GW.Analysis.realMultiplier (H := Sector n) (b n) volume)
    (fun n => GW.Analysis.realMultiplier (H := Sector n) (c n) volume)
    (fun n x ha hb => realMultiplier_quadratic_weight volume (a n) (b n) (c n) (hc n) (hc2 n) x ha hb)
    (freeFourierRepresentation u) ha hb
  refine ⟨hm,?_⟩
  rw [physicalSectorMultiplier_norm c ⟨u,hm⟩,physicalSectorMultiplier_norm a ⟨u,ha⟩,
    physicalSectorMultiplier_norm b ⟨u,hb⟩]
  rw [freeFourierRepresentation.norm_map] at hs
  exact hs

lemma freeFormWeight_square_split (n : ℕ) (p : GW.Space) :
    freeFormWeight n p^2 = 1+‖p‖^2+(Real.sqrt (n : ℝ))^2 := by
  rw [freeFormWeight_sq,Real.sq_sqrt (Nat.cast_nonneg n)]
  change 1+(‖p‖^2+(n : ℝ)) = 1+‖p‖^2+(n : ℝ)
  ring

lemma freeFormDomain_mem_norm (u : Physical) (hp : u ∈ freeMomentumModulus.domain)
    (hn : u ∈ freeRootNumber.domain) :
    ∃ hu : u ∈ freeFormOperator.domain,
      ‖freeFormOperator ⟨u,hu⟩‖^2 = ‖u‖^2+
        ‖freeMomentumModulus ⟨u,hp⟩‖^2+‖freeRootNumber ⟨u,hn⟩‖^2 :=
  physicalSectorMultiplier_quadratic (fun _ p => ‖p‖) (fun n _ => Real.sqrt (n : ℝ))
    freeFormWeight freeFormWeight_measurable freeFormWeight_square_split u hp hn

lemma freeForm_momentum_mem (u : freeFormOperator.domain) : (u : Physical) ∈ freeMomentumModulus.domain := by
  have h := physicalSectorMultiplier_domination (fun _ p => ‖p‖) freeFormWeight
    (fun _ => continuous_norm.measurable) zero_le_one (fun n p => by
      rw [abs_of_nonneg (norm_nonneg _),abs_of_nonneg (zero_le_one.trans (freeFormWeight_one n p)),one_mul]
      apply (sq_le_sq₀ (norm_nonneg _) (zero_le_one.trans (freeFormWeight_one n p))).mp
      rw [freeFormWeight_square_split]
      nlinarith [sq_nonneg (Real.sqrt (n : ℝ))]) u
  exact h.choose

lemma freeForm_rootNumber_mem (u : freeFormOperator.domain) : (u : Physical) ∈ freeRootNumber.domain := by
  have h := physicalSectorMultiplier_domination (fun n _ => Real.sqrt (n : ℝ)) freeFormWeight
    (fun _ => measurable_const) zero_le_one (fun n p => by
      rw [abs_of_nonneg (Real.sqrt_nonneg _),abs_of_nonneg (zero_le_one.trans (freeFormWeight_one n p)),one_mul]
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) (zero_le_one.trans (freeFormWeight_one n p))).mp
      rw [freeFormWeight_square_split]
      nlinarith [sq_nonneg ‖p‖]) u
  exact h.choose

lemma freeForm_domain_intersection :
    freeFormOperator.domain = freeMomentumModulus.domain ⊓ (physicalNumberPower (1/2 : ℝ)).domain := by
  rw [← freeRootNumber_eq]
  ext u
  constructor
  · intro hu
    exact ⟨freeForm_momentum_mem ⟨u,hu⟩,freeForm_rootNumber_mem ⟨u,hu⟩⟩
  · rintro ⟨hp,hn⟩
    exact (freeFormDomain_mem_norm u hp hn).choose

lemma freeForm_norm_identity (u : FreeFormDomain) :
    let v : freeFormOperator.domain := u
    ‖u‖^2 = ‖(v : Physical)‖^2+
      ‖freeMomentumModulus ⟨v,freeForm_momentum_mem v⟩‖^2+
      ‖freeRootNumber ⟨v,freeForm_rootNumber_mem v⟩‖^2 := by
  let v : freeFormOperator.domain := u
  change ‖u‖^2 = ‖(v : Physical)‖^2+‖freeMomentumModulus ⟨v,freeForm_momentum_mem v⟩‖^2+
    ‖freeRootNumber ⟨v,freeForm_rootNumber_mem v⟩‖^2
  rw [freeFormDomain_norm]
  exact (freeFormDomain_mem_norm (v : Physical) (freeForm_momentum_mem v) (freeForm_rootNumber_mem v)).choose_spec

def freeCutoffSet (R n : ℕ) : Set GW.Space := {p | n ≤ R ∧ ‖p‖ ≤ (R : ℝ)}

lemma freeCutoffSet_measurable (R n : ℕ) : MeasurableSet (freeCutoffSet R n) :=
  MeasurableSet.inter (MeasurableSet.const _) (measurableSet_le continuous_norm.measurable measurable_const)

def freeCutoffFiber (R n : ℕ) : ElectronSector n →L[ℂ] ElectronSector n :=
  GW.Spaces.WeightedL2.cutoff (H := Sector n) (w := fun _ : GW.Space => (1 : ℝ)) (μ := volume)
    (freeCutoffSet R n) (freeCutoffSet_measurable R n)

lemma freeCutoffFiber_ae (R n : ℕ) (u : ElectronSector n) :
    freeCutoffFiber R n u =ᵐ[volume] (freeCutoffSet R n).indicator (u : GW.Space → Sector n) :=
  (GW.Spaces.WeightedL2.cutoff_ae (w := fun _ : GW.Space => (1 : ℝ)) (freeCutoffSet R n)
    (freeCutoffSet_measurable R n) u).symm

lemma freeCutoffFiber_norm (R n : ℕ) : ‖freeCutoffFiber R n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [freeCutoffFiber_ae R n u] with p hp
  rw [hp,one_mul]
  exact norm_indicator_le_norm_self _ _

def freeFourierCutoff (R : ℕ) : ElectronBosonSum →L[ℂ] ElectronBosonSum :=
  GW.Spaces.diagonalMap (freeCutoffFiber R) zero_le_one (freeCutoffFiber_norm R)

lemma freeFourierCutoff_ae (R : ℕ) (u : ElectronBosonSum) (n : ℕ) :
    freeFourierCutoff R u n =ᵐ[volume] (freeCutoffSet R n).indicator (u n : GW.Space → Sector n) :=
  freeCutoffFiber_ae R n (u n)

lemma freeCutoffFiber_tendsto (n : ℕ) (u : ElectronSector n) :
    Tendsto (fun R => freeCutoffFiber R n u) atTop (𝓝 u) := by
  apply GW.Spaces.WeightedL2.cutoff_tendsto (w := fun _ : GW.Space => (1 : ℝ))
    (fun R => freeCutoffSet R n) (fun R => freeCutoffSet_measurable R n)
  apply Eventually.of_forall
  intro p
  filter_upwards [eventually_ge_atTop n,
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop ‖p‖)] with R hn hp
  exact ⟨hn,hp⟩

lemma freeFourierCutoff_tendsto (u : ElectronBosonSum) :
    Tendsto (fun R => freeFourierCutoff R u) atTop (𝓝 u) :=
  GW.Spaces.diagonalMap_tendsto freeCutoffFiber freeCutoffFiber_norm freeCutoffFiber_tendsto u

def freeCutoff (R : ℕ) : Physical →L[ℂ] Physical :=
  freeFourierRepresentation.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((freeFourierCutoff R).comp freeFourierRepresentation.toContinuousLinearEquiv.toContinuousLinearMap)

lemma freeCutoff_fourier (R : ℕ) (u : Physical) :
    freeFourierRepresentation (freeCutoff R u) = freeFourierCutoff R (freeFourierRepresentation u) :=
  freeFourierRepresentation.apply_symm_apply _

lemma freeCutoff_tendsto (u : Physical) : Tendsto (fun R => freeCutoff R u) atTop (𝓝 u) := by
  apply freeFourierRepresentation.isometry.tendsto_nhds_iff.mpr
  simpa only [Function.comp_def,freeCutoff_fourier] using freeFourierCutoff_tendsto (freeFourierRepresentation u)

lemma freeCutoffSet_mono (n : ℕ) : Monotone (fun R => freeCutoffSet R n) := by
  intro R S h p hp
  exact ⟨hp.1.trans h,hp.2.trans (Nat.cast_le.mpr h)⟩

lemma freeFourierCutoff_absorb {R S : ℕ} (h : R ≤ S) (u : ElectronBosonSum) :
    freeFourierCutoff S (freeFourierCutoff R u) = freeFourierCutoff R u := by
  apply lp.ext
  funext n
  apply Lp.ext
  filter_upwards [freeFourierCutoff_ae S (freeFourierCutoff R u) n,freeFourierCutoff_ae R u n] with p hs hr
  rw [hs]
  by_cases hp : p ∈ freeCutoffSet S n
  · exact Set.indicator_of_mem hp _
  · have hrp : p ∉ freeCutoffSet R n := fun hp' => hp (freeCutoffSet_mono n h hp')
    rw [Set.indicator_of_notMem hp,hr,Set.indicator_of_notMem hrp]

lemma freeCutoff_absorb {R S : ℕ} (h : R ≤ S) (u : Physical) :
    freeCutoff S (freeCutoff R u) = freeCutoff R u := by
  apply freeFourierRepresentation.injective
  rw [freeCutoff_fourier,freeCutoff_fourier]
  exact freeFourierCutoff_absorb h (freeFourierRepresentation u)

lemma freeCutoff_fixed_of_le {R S : ℕ} (h : R ≤ S) {u : Physical} (hu : freeCutoff R u = u) :
    freeCutoff S u = u :=
  (congrArg (freeCutoff S) hu.symm).trans ((freeCutoff_absorb h u).trans hu)

/-- The actual union of the finite-sector, bounded-momentum ranges, for R≥1. -/
def freeCutoffCore : Submodule ℂ Physical where
  carrier := {u | ∃ R : ℕ, freeCutoff (R+1) u = u}
  zero_mem' := ⟨0,map_zero _⟩
  add_mem' := by
    rintro u v ⟨R,hu⟩ ⟨S,hv⟩
    refine ⟨max R S,?_⟩
    rw [map_add,freeCutoff_fixed_of_le (Nat.succ_le_succ (le_max_left R S)) hu,
      freeCutoff_fixed_of_le (Nat.succ_le_succ (le_max_right R S)) hv]
  smul_mem' := by
    rintro c u ⟨R,hu⟩
    exact ⟨R,by rw [map_smul,hu]⟩

lemma freeCutoffCore_range : (freeCutoffCore : Set Physical) = ⋃ R : ℕ, Set.range (freeCutoff (R+1)) := by
  ext u
  constructor
  · rintro ⟨R,hu⟩
    exact Set.mem_iUnion.mpr ⟨R,⟨u,hu⟩⟩
  · intro hu
    obtain ⟨R,v,rfl⟩ := Set.mem_iUnion.mp hu
    exact ⟨R,freeCutoff_absorb le_rfl v⟩

lemma freeCutoff_mem_core (R : ℕ) (u : Physical) : freeCutoff (R+1) u ∈ freeCutoffCore :=
  ⟨R,freeCutoff_absorb le_rfl u⟩

lemma freeCutoff_weighted (w : ℕ → GW.Space → ℝ) (R : ℕ) (u : (physicalSectorMultiplier w).domain) :
    ∃ hmem : freeCutoff R (u : Physical) ∈ (physicalSectorMultiplier w).domain,
      physicalSectorMultiplier w ⟨freeCutoff R u,hmem⟩ = freeCutoff R (physicalSectorMultiplier w u) := by
  let v := freeCutoff R (u : Physical)
  let z := freeCutoff R (physicalSectorMultiplier w u)
  have he (n : ℕ) : (fun p => (w n p : ℂ) • freeFourierRepresentation v n p) =ᵐ[volume]
      freeFourierRepresentation z n := by
    change (fun p => (w n p : ℂ) • freeFourierRepresentation (freeCutoff R (u : Physical)) n p) =ᵐ[volume]
      freeFourierRepresentation (freeCutoff R (physicalSectorMultiplier w u)) n
    rw [freeCutoff_fourier R (u : Physical),freeCutoff_fourier R (physicalSectorMultiplier w u)]
    filter_upwards [freeFourierCutoff_ae R (freeFourierRepresentation (u : Physical)) n,
      freeFourierCutoff_ae R (freeFourierRepresentation (physicalSectorMultiplier w u)) n,
      physicalSectorMultiplier_action w u n] with p hp hq hw
    rw [hp,hq]
    by_cases hp' : p ∈ freeCutoffSet R n
    · simpa only [Set.indicator_of_mem hp'] using hw
    · simp only [Set.indicator_of_notMem hp',smul_zero]
  have hm : v ∈ (physicalSectorMultiplier w).domain :=
    (physicalSectorMultiplier_domain w v).mpr ⟨freeFourierRepresentation z,he⟩
  refine ⟨hm,?_⟩
  apply freeFourierRepresentation.injective
  apply lp.ext
  funext n
  apply Lp.ext
  exact (physicalSectorMultiplier_action w ⟨v,hm⟩ n).symm.trans (he n)

def freeCutoffEnergyCoefficient (R n : ℕ) : GW.Space → ℂ :=
  (freeCutoffSet R n).indicator (fun p => (freeEnergySymbol n p : ℂ))

lemma freeCutoffEnergyCoefficient_measurable (R n : ℕ) : Measurable (freeCutoffEnergyCoefficient R n) :=
  (Complex.continuous_ofReal.measurable.comp (freeEnergySymbol_measurable n)).indicator (freeCutoffSet_measurable R n)

lemma freeCutoffEnergyCoefficient_bound (R n : ℕ) :
    ∀ᵐ p ∂(volume : Measure GW.Space), ‖freeCutoffEnergyCoefficient R n p‖ ≤ (R : ℝ)^2+(R : ℝ) := by
  apply Eventually.of_forall
  intro p
  by_cases hp : p ∈ freeCutoffSet R n
  · rw [freeCutoffEnergyCoefficient,Set.indicator_of_mem hp,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (freeEnergySymbol_nonnegative n p)]
    have hn : (n : ℝ) ≤ (R : ℝ) := Nat.cast_le.mpr hp.1
    have hq := (sq_le_sq₀ (norm_nonneg p) (Nat.cast_nonneg (α := ℝ) R)).mpr hp.2
    exact add_le_add hq hn
  · rw [freeCutoffEnergyCoefficient,Set.indicator_of_notMem hp,norm_zero]
    positivity

def freeCutoffEnergy (R : ℕ) : ElectronBosonSum →L[ℂ] ElectronBosonSum :=
  GW.Spaces.diagonalMap
    (fun n => GW.Analysis.boundedMultiplier (E := Sector n) (freeCutoffEnergyCoefficient R n)
      (freeCutoffEnergyCoefficient_measurable R n) (freeCutoffEnergyCoefficient_bound R n))
    (by positivity) (fun n => GW.Analysis.boundedMultiplier_opNorm_le _
      (freeCutoffEnergyCoefficient_measurable R n) (by positivity) (freeCutoffEnergyCoefficient_bound R n))

lemma freeCutoffEnergy_ae (R n : ℕ) (v : ElectronBosonSum) :
    (fun p => freeCutoffEnergyCoefficient R n p • v n p) =ᵐ[volume] freeCutoffEnergy R v n :=
  GW.Analysis.boundedMultiplier_ae (freeCutoffEnergyCoefficient R n)
    (freeCutoffEnergyCoefficient_measurable R n) (freeCutoffEnergyCoefficient_bound R n) (v n)

lemma freeCutoff_mem_H0 (R : ℕ) (u : Physical) : freeCutoff R u ∈ freeHamiltonian.domain := by
  change freeCutoff R u ∈ (physicalSectorMultiplier freeEnergySymbol).domain
  apply (physicalSectorMultiplier_domain freeEnergySymbol _).mpr
  rw [freeCutoff_fourier]
  let v := freeFourierRepresentation u
  refine ⟨freeCutoffEnergy R v,fun n => ?_⟩
  filter_upwards [freeCutoffEnergy_ae R n v,freeFourierCutoff_ae R v n] with p h₁ h₂
  change (freeEnergySymbol n p : ℂ) • freeFourierCutoff R v n p = freeCutoffEnergy R v n p
  rw [← h₁,h₂]
  by_cases hp : p ∈ freeCutoffSet R n <;> simp [freeCutoffEnergyCoefficient,hp]

lemma freeCutoffCore_le_H0 : freeCutoffCore ≤ freeHamiltonian.domain := by
  rintro u ⟨R,hR⟩
  exact hR ▸ freeCutoff_mem_H0 (R+1) u

lemma freeHamiltonian_cutoff_graph_tendsto (u : freeHamiltonian.domain) :
    Tendsto (fun R : ℕ => (freeCutoff (R+1) (u : Physical),freeCutoff (R+1) (freeHamiltonian u))) atTop
      (𝓝 ((u : Physical),freeHamiltonian u)) :=
  (((freeCutoff_tendsto (u : Physical)).prodMk_nhds (freeCutoff_tendsto (freeHamiltonian u))).comp
    (tendsto_add_atTop_nat 1))

lemma freeHamiltonian_cutoff_core : freeHamiltonian.HasCore freeCutoffCore := by
  have hclosed := GW.Operators.selfadjoint_closed freeHamiltonian freeHamiltonian_selfadjoint
  have hle : freeHamiltonian.domRestrict freeCutoffCore ≤ freeHamiltonian := LinearPMap.domRestrict_le
  have hc := hclosed.isClosable.leIsClosable hle
  refine ⟨freeCutoffCore_le_H0,LinearPMap.eq_of_eq_graph ?_⟩
  rw [← hc.graph_closure_eq_closure_graph]
  apply SetLike.coe_injective
  change closure ((freeHamiltonian.domRestrict freeCutoffCore).graph : Set (Physical × Physical)) =
    (freeHamiltonian.graph : Set (Physical × Physical))
  apply le_antisymm
  · exact closure_minimal (LinearPMap.le_graph_of_le hle) hclosed
  · intro p hp
    obtain ⟨u,hu⟩ := freeHamiltonian.mem_graph_iff'.mp hp
    rw [← hu]
    apply mem_closure_of_tendsto (freeHamiltonian_cutoff_graph_tendsto u)
    apply Eventually.of_forall
    intro R
    obtain ⟨hm,he⟩ := freeCutoff_weighted freeEnergySymbol (R+1) u
    exact (freeHamiltonian.domRestrict freeCutoffCore).mem_graph_iff.mpr
      ⟨⟨freeCutoff (R+1) u,⟨freeCutoff_mem_core R u,hm⟩⟩,rfl,he⟩

section WeightedCutoff
variable (w : ℕ → GW.Space → ℝ) (hw : ∀ n, Measurable (w n)) (hw1 : ∀ n p, 1 ≤ w n p)

def physicalWeightedCutoff (R : ℕ) (u : GW.Spaces.WeightedDomain (physicalWeightedGraph w hw hw1)) :
    GW.Spaces.WeightedDomain (physicalWeightedGraph w hw hw1) :=
  (show (physicalSectorMultiplier w).domain from
    ⟨freeCutoff R ((show (physicalSectorMultiplier w).domain from u) : Physical),
      (freeCutoff_weighted w R (show (physicalSectorMultiplier w).domain from u)).choose⟩)

lemma physicalWeightedCutoff_coordinates (R : ℕ) (u : GW.Spaces.WeightedDomain (physicalWeightedGraph w hw hw1)) :
    GW.Spaces.weightedDomainIsometry (physicalWeightedGraph w hw hw1) (physicalWeightedCutoff w hw hw1 R u) =
      freeFourierCutoff R (GW.Spaces.weightedDomainIsometry (physicalWeightedGraph w hw hw1) u) := by
  let v : (physicalSectorMultiplier w).domain := u
  have he := (freeCutoff_weighted w R v).choose_spec
  change freeFourierRepresentation (physicalSectorMultiplier w
    (show (physicalSectorMultiplier w).domain from physicalWeightedCutoff w hw hw1 R u)) =
      freeFourierCutoff R (freeFourierRepresentation (physicalSectorMultiplier w v))
  rw [show physicalSectorMultiplier w
      (show (physicalSectorMultiplier w).domain from physicalWeightedCutoff w hw hw1 R u) =
      freeCutoff R (physicalSectorMultiplier w v) from he]
  exact freeCutoff_fourier R _

lemma physicalWeightedCutoff_tendsto (u : GW.Spaces.WeightedDomain (physicalWeightedGraph w hw hw1)) :
    Tendsto (fun R => physicalWeightedCutoff w hw hw1 R u) atTop (𝓝 u) := by
  let U := GW.Spaces.weightedDomainIsometry (physicalWeightedGraph w hw hw1)
  apply U.isometry.tendsto_nhds_iff.mpr
  have he (R : ℕ) : U (physicalWeightedCutoff w hw hw1 R u) = freeFourierCutoff R (U u) :=
    physicalWeightedCutoff_coordinates w hw hw1 R u
  simpa only [Function.comp_def,he] using freeFourierCutoff_tendsto (U u)
end WeightedCutoff

def freeFormCutoff (R : ℕ) (u : FreeFormDomain) : FreeFormDomain :=
  physicalWeightedCutoff freeFormWeight freeFormWeight_measurable freeFormWeight_one R u

def freeGraphCutoff (R : ℕ) (u : FreeGraphDomain) : FreeGraphDomain :=
  physicalWeightedCutoff freeGraphWeight freeGraphWeight_measurable freeGraphWeight_one R u

lemma freeFormCutoff_tendsto (u : FreeFormDomain) : Tendsto (fun R => freeFormCutoff R u) atTop (𝓝 u) :=
  physicalWeightedCutoff_tendsto freeFormWeight freeFormWeight_measurable freeFormWeight_one u

lemma freeGraphCutoff_tendsto (u : FreeGraphDomain) : Tendsto (fun R => freeGraphCutoff R u) atTop (𝓝 u) :=
  physicalWeightedCutoff_tendsto freeGraphWeight freeGraphWeight_measurable freeGraphWeight_one u

def freeFormCore : Submodule ℂ FreeFormDomain := freeCutoffCore.comap freeFormDomainInclusion.toLinearMap

lemma freeFormCore_dense : Dense (freeFormCore : Set FreeFormDomain) := by
  intro u
  have ht := (freeFormCutoff_tendsto u).comp (tendsto_add_atTop_nat 1)
  apply mem_closure_of_tendsto ht
  apply Eventually.of_forall
  intro R
  change freeFormDomainInclusion (freeFormCutoff (R+1) u) ∈ freeCutoffCore
  rw [freeFormDomainInclusion_apply]
  exact freeCutoff_mem_core R ((show freeFormOperator.domain from u) : Physical)

lemma freeFormDomainInclusion_range : Set.range freeFormDomainInclusion = (freeFormOperator.domain : Set Physical) := by
  ext u
  constructor
  · rintro ⟨v,rfl⟩
    rw [freeFormDomainInclusion_apply]
    exact (show freeFormOperator.domain from v).property
  · intro hu
    let v : FreeFormDomain := (⟨u,hu⟩ : freeFormOperator.domain)
    exact ⟨v,freeFormDomainInclusion_apply v⟩

lemma freeGraphDomainInclusion_range : Set.range freeGraphDomainInclusion = (freeHamiltonian.domain : Set Physical) := by
  rw [← freeGraphOperator_domain]
  ext u
  constructor
  · rintro ⟨v,rfl⟩
    rw [freeGraphDomainInclusion_apply]
    exact (show freeGraphOperator.domain from v).property
  · intro hu
    let v : FreeGraphDomain := (⟨u,hu⟩ : freeGraphOperator.domain)
    exact ⟨v,freeGraphDomainInclusion_apply v⟩

lemma freeFormDomainInclusion_dense : DenseRange freeFormDomainInclusion := by
  change Dense (Set.range freeFormDomainInclusion)
  rw [freeFormDomainInclusion_range]
  exact freeFormOperator_selfadjoint.1

lemma freeGraphDomainInclusion_dense : DenseRange freeGraphDomainInclusion := by
  change Dense (Set.range freeGraphDomainInclusion)
  rw [freeGraphDomainInclusion_range]
  exact freeHamiltonian_selfadjoint.1

lemma freeGraphOperator_eq_shift : freeGraphOperator = GW.Operators.realShift freeHamiltonian (-1) := by
  apply LinearPMap.ext
  · exact freeGraphOperator_domain
  · intro u hu hv
    have he := freeGraphOperator_action ⟨u,hu⟩
    have hs : GW.Operators.realShift freeHamiltonian (-1) ⟨u,hv⟩ =
        freeHamiltonian (⟨u,hv⟩ : freeHamiltonian.domain) + u := by
      change freeHamiltonian (⟨u,hv⟩ : freeHamiltonian.domain) -
        ((↑(-1 : ℝ) : ℂ) • u) = _
      norm_num
    exact he.trans hs.symm

def freeGraphH0Input (u : FreeGraphDomain) : freeHamiltonian.domain :=
  ⟨(show freeGraphOperator.domain from u).val,by
    rw [← freeGraphOperator_domain]
    exact (show freeGraphOperator.domain from u).property⟩

lemma freeGraph_norm_identity (u : FreeGraphDomain) :
    ‖u‖ = ‖freeHamiltonian (freeGraphH0Input u)+freeGraphDomainInclusion u‖ := by
  let v : freeGraphOperator.domain := u
  calc
    ‖u‖ = ‖freeGraphOperator v‖ := freeGraphDomain_norm u
    _ = _ := by
      rw [freeGraphDomainInclusion_apply]
      exact congrArg (fun z : Physical => ‖z‖) (freeGraphOperator_action v)

lemma freeGraph_norm_upper (u : FreeGraphDomain) :
    ‖u‖ ≤ ‖freeGraphDomainInclusion u‖+‖freeHamiltonian (freeGraphH0Input u)‖ := by
  rw [freeGraph_norm_identity,add_comm ‖freeGraphDomainInclusion u‖]
  exact norm_add_le _ _

lemma freeGraph_norm_lower (u : FreeGraphDomain) :
    ‖freeGraphDomainInclusion u‖ ≤ ‖u‖ ∧ ‖freeHamiltonian (freeGraphH0Input u)‖ ≤ ‖u‖ := by
  constructor
  · have h := freeGraphWeightedGraph.embedding.le_opNorm (GW.Spaces.weightedDomainIsometry freeGraphWeightedGraph u)
    change ‖freeGraphDomainInclusion u‖ ≤ _ at h
    exact h.trans (by simpa only [LinearIsometryEquiv.norm_map,one_mul] using
      mul_le_mul_of_nonneg_right freeGraphWeightedGraph.embedding_norm_le (norm_nonneg u))
  · let v : freeGraphOperator.domain := u
    obtain ⟨hv,hh⟩ := physicalSectorMultiplier_domination freeEnergySymbol freeGraphWeight freeEnergySymbol_measurable
      zero_le_one (fun n p => by
        rw [abs_of_nonneg (freeEnergySymbol_nonnegative n p),
          abs_of_nonneg (zero_le_one.trans (freeGraphWeight_one n p)),one_mul]
        change freeEnergySymbol n p ≤ 1+freeEnergySymbol n p
        linarith) v
    change ‖physicalSectorMultiplier freeEnergySymbol ⟨(v : Physical),hv⟩‖ ≤ ‖u‖
    rw [freeGraphDomain_norm]
    change ‖physicalSectorMultiplier freeEnergySymbol ⟨(v : Physical),hv⟩‖ ≤
      ‖physicalSectorMultiplier freeGraphWeight v‖
    simpa only [one_mul] using hh

lemma freeHamiltonian_mem_form (u : freeHamiltonian.domain) : (u : Physical) ∈ freeFormOperator.domain := by
  apply (physicalSectorMultiplier_domain freeFormWeight (u : Physical)).mpr
  exact GW.Spaces.sumEnergyWeight_mem (F := Sector) (fun _ : ℕ => (volume : Measure GW.Space))
    freeEnergySymbol_measurable freeEnergySymbol_nonnegative (physicalWeightInput freeEnergySymbol u)

lemma freeForm_norm_on_H0 (u : freeHamiltonian.domain) :
    ‖freeFormOperator ⟨u,freeHamiltonian_mem_form u⟩‖^2 =
      ‖(u : Physical)‖^2+(⟪(u : Physical),freeHamiltonian u⟫_ℂ).re := by
  let v : freeFormOperator.domain := ⟨u,freeHamiltonian_mem_form u⟩
  let μ := fun _ : ℕ => (volume : Measure GW.Space)
  let x := physicalWeightInput freeEnergySymbol u
  have h := GW.Spaces.sumEnergyWeight_norm_sq (F := Sector) μ
    freeEnergySymbol_measurable freeEnergySymbol_nonnegative x
  have hi : physicalWeightInput freeFormWeight v =
      GW.Spaces.sumEnergyInput (F := Sector) μ freeEnergySymbol_measurable freeEnergySymbol_nonnegative x :=
    Subtype.ext rfl
  have hA := physicalWeightProduct_value freeFormWeight v
  rw [hi] at hA
  change freeFourierRepresentation (freeFormOperator v) = _ at hA
  have hB := physicalWeightProduct_value freeEnergySymbol u
  change freeFourierRepresentation (freeHamiltonian u) = GW.Spaces.sumWeightValue (F := Sector) μ x at hB
  calc
    ‖freeFormOperator v‖^2 = ‖freeFourierRepresentation (freeFormOperator v)‖^2 := by rw [LinearIsometryEquiv.norm_map]
    _ = ‖freeFourierRepresentation (u : Physical)‖^2 +
        (⟪freeFourierRepresentation (u : Physical),freeFourierRepresentation (freeHamiltonian u)⟫_ℂ).re := by
      rw [hA,hB]
      exact h
    _ = _ := by rw [LinearIsometryEquiv.norm_map,freeFourierRepresentation.inner_map_map]

/-- The original operator domain with its canonical energy norm includes isometrically into Q. -/
def freeEnergyToFormLinear : GW.Operators.CanonicalDomain freeNonnegativeData →ₗ[ℂ] FreeFormDomain where
  toFun u := (show freeFormOperator.domain from
    ⟨GW.Operators.canonicalInclusionLinear freeNonnegativeData u,
      freeHamiltonian_mem_form (GW.Operators.canonicalCoordinates freeNonnegativeData u)⟩)
  map_add' u v := Subtype.ext (map_add (GW.Operators.canonicalInclusionLinear freeNonnegativeData) u v)
  map_smul' c u := Subtype.ext (map_smul (GW.Operators.canonicalInclusionLinear freeNonnegativeData) c u)

def freeEnergyToFormIsometry : GW.Operators.CanonicalDomain freeNonnegativeData →ₗᵢ[ℂ] FreeFormDomain where
  toLinearMap := freeEnergyToFormLinear
  norm_map' u := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [freeFormDomain_norm,GW.Operators.canonicalDomain_norm_sq]
    exact freeForm_norm_on_H0 (GW.Operators.canonicalCoordinates freeNonnegativeData u)

lemma freeEnergyToForm_dense : DenseRange freeEnergyToFormIsometry := by
  intro u
  have ht := (freeFormCutoff_tendsto u).comp (tendsto_add_atTop_nat 1)
  apply mem_closure_of_tendsto ht
  apply Eventually.of_forall
  intro R
  let v : freeHamiltonian.domain := ⟨freeCutoff (R+1) ((show freeFormOperator.domain from u) : Physical),
    freeCutoff_mem_H0 (R+1) ((show freeFormOperator.domain from u) : Physical)⟩
  let z := (GW.Operators.canonicalCoordinates freeNonnegativeData).symm v
  refine ⟨z,?_⟩
  change (show freeFormOperator.domain from freeEnergyToFormIsometry z) =
    (show freeFormOperator.domain from freeFormCutoff (R+1) u)
  apply Subtype.ext
  rfl

/-- The completed energy space of this SAME H0 is exactly the specified form space. -/
def freeCanonicalFormEquiv : GW.Operators.CanonicalEnergySpace freeNonnegativeData ≃ₗᵢ[ℂ] FreeFormDomain :=
  GW.Operators.completionTransportEquiv freeEnergyToFormIsometry freeEnergyToForm_dense

lemma freeCanonicalFormEquiv_embedding (u : GW.Operators.CanonicalEnergySpace freeNonnegativeData) :
    freeFormDomainInclusion (freeCanonicalFormEquiv u) = GW.Operators.canonicalEmbedding freeNonnegativeData u := by
  refine UniformSpace.Completion.induction_on u (isClosed_eq
    (freeFormDomainInclusion.continuous.comp freeCanonicalFormEquiv.continuous)
    (GW.Operators.canonicalEmbedding freeNonnegativeData).continuous) ?_
  intro v
  change freeFormDomainInclusion (freeCanonicalFormEquiv (v : GW.Operators.CanonicalEnergySpace freeNonnegativeData)) =
    GW.Operators.canonicalEmbedding freeNonnegativeData (v : GW.Operators.CanonicalEnergySpace freeNonnegativeData)
  rw [GW.Operators.canonicalEmbedding_coe]
  have he : freeCanonicalFormEquiv (v : GW.Operators.CanonicalEnergySpace freeNonnegativeData) =
      freeEnergyToFormIsometry v := GW.Operators.completionTransportEquiv_coe _ _ v
  rw [he,freeFormDomainInclusion_apply]
  rfl

end GW.Fock
