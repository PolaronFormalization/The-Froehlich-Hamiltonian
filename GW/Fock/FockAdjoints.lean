module
public import GW.Fock.FockGeneralized
@[expose] public section
noncomputable section
open Filter
open scoped Topology InnerProductSpace
namespace GW.Fock
section ShiftedGraphs
variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℂ (E n)]

lemma sectorOutputMap_closed (W : lp E 2 →ₗ[ℂ] (∀ n, E n))
    (hW : ∀ n, Continuous (fun u : lp E 2 => W u n)) :
    IsClosed ((sectorOutputMap W).graph : Set (lp E 2 × lp E 2)) := by
  rw [sectorOutputMap_graph]
  have he : (sectorOutputGraph W : Set (lp E 2 × lp E 2)) =
      ⋂ n, {p : lp E 2 × lp E 2 | p.2 n = W p.1 n} := by
    ext p
    simp only [Set.mem_iInter,Set.mem_setOf_eq]
    rfl
  rw [he]
  exact isClosed_iInter (fun n =>
    isClosed_eq ((lp.evalCLM ℂ E 2 n).continuous.comp continuous_snd) ((hW n).comp continuous_fst))

lemma maximalSectorCreation_closed (C : ∀ n, E n →L[ℂ] E (n+1)) :
    IsClosed ((maximalSectorCreation C).graph : Set (lp E 2 × lp E 2)) := by
  apply sectorOutputMap_closed
  intro n
  cases n with
  | zero => exact continuous_const
  | succ n => exact (C n).continuous.comp (lp.evalCLM ℂ E 2 n).continuous

lemma maximalSectorAnnihilation_closed (A : ∀ n, E (n+1) →L[ℂ] E n) :
    IsClosed ((maximalSectorAnnihilation A).graph : Set (lp E 2 × lp E 2)) :=
  sectorOutputMap_closed _ (fun n => (A n).continuous.comp (lp.evalCLM ℂ E 2 (n+1)).continuous)

lemma finiteSector_le_creation (C : ∀ n, E n →L[ℂ] E (n+1)) :
    finiteSectorDomain E ≤ (maximalSectorCreation C).domain := by
  intro u hu
  obtain ⟨m,hm⟩ := (finiteSectorDomain_iff E u).mp hu
  apply (maximalSectorCreation_domain C u).mpr
  apply summable_of_ne_finset_zero (s := Finset.range (m+1))
  intro n hn
  have hlt : m < n := by
    have h := show ¬ n < m+1 from fun h => hn (Finset.mem_range.mpr h)
    omega
  rw [hm n hlt,map_zero,norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0)]

lemma finiteSector_le_annihilation (A : ∀ n, E (n+1) →L[ℂ] E n) :
    finiteSectorDomain E ≤ (maximalSectorAnnihilation A).domain := by
  intro u hu
  obtain ⟨m,hm⟩ := (finiteSectorDomain_iff E u).mp hu
  apply (maximalSectorAnnihilation_domain A u).mpr
  apply summable_of_ne_finset_zero (s := Finset.range (m+1))
  intro n hn
  have hlt : m < n+1 := by
    have h := show ¬ n < m+1 from fun h => hn (Finset.mem_range.mpr h)
    omega
  rw [hm (n+1) hlt,map_zero,norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0)]

lemma maximalSectorCreation_cutoff (C : ∀ n, E n →L[ℂ] E (n+1)) (m : ℕ)
    (u : (maximalSectorCreation C).domain) :
    maximalSectorCreation C ⟨cutoff E m u,finiteSector_le_creation C (cutoff_mem_finiteSectorDomain E m u)⟩ =
      cutoff E (m+1) (maximalSectorCreation C u) := by
  apply lp.ext
  funext n
  rw [cutoff_apply]
  cases n with
  | zero => simp [maximalSectorCreation_zero]
  | succ n =>
    rw [maximalSectorCreation_succ,maximalSectorCreation_succ,cutoff_apply]
    by_cases h : n ≤ m
    · simp [h]
    · simp [h]

lemma maximalSectorAnnihilation_cutoff_succ (A : ∀ n, E (n+1) →L[ℂ] E n) (m : ℕ)
    (u : (maximalSectorAnnihilation A).domain) :
    maximalSectorAnnihilation A
      ⟨cutoff E (m+1) u,finiteSector_le_annihilation A (cutoff_mem_finiteSectorDomain E (m+1) u)⟩ =
        cutoff E m (maximalSectorAnnihilation A u) := by
  apply lp.ext
  funext n
  rw [cutoff_apply,maximalSectorAnnihilation_apply,maximalSectorAnnihilation_apply,cutoff_apply]
  by_cases h : n ≤ m <;> simp [h]

lemma maximalSectorAnnihilation_cutoff_zero (A : ∀ n, E (n+1) →L[ℂ] E n) (u : lp E 2) :
    maximalSectorAnnihilation A
      ⟨cutoff E 0 u,finiteSector_le_annihilation A (cutoff_mem_finiteSectorDomain E 0 u)⟩ = 0 := by
  apply lp.ext
  funext n
  rw [maximalSectorAnnihilation_apply,cutoff_apply,if_neg (by omega),map_zero]
  rfl

lemma finiteSector_dense : Dense (finiteSectorDomain E : Set (lp E 2)) := by
  intro u
  exact mem_closure_of_tendsto (cutoff_tendsto E u)
    (Eventually.of_forall (fun m => cutoff_mem_finiteSectorDomain E m u))

lemma maximalSectorCreation_dense (C : ∀ n, E n →L[ℂ] E (n+1)) :
    Dense ((maximalSectorCreation C).domain : Set (lp E 2)) :=
  finiteSector_dense.mono (finiteSector_le_creation C)

lemma maximalSectorAnnihilation_dense (A : ∀ n, E (n+1) →L[ℂ] E n) :
    Dense ((maximalSectorAnnihilation A).domain : Set (lp E 2)) :=
  finiteSector_dense.mono (finiteSector_le_annihilation A)

lemma finiteSector_core_of_cutoffs (T : lp E 2 →ₗ.[ℂ] lp E 2)
    (hT : IsClosed (T.graph : Set (lp E 2 × lp E 2))) (hfin : finiteSectorDomain E ≤ T.domain)
    (r : ℕ → ℕ)
    (hc : ∀ u : T.domain, Tendsto (fun m => (cutoff E (r m) u,
      T ⟨cutoff E (r m) u,hfin (cutoff_mem_finiteSectorDomain E (r m) u)⟩)) atTop
        (𝓝 ((u : lp E 2),T u))) :
    T.HasCore (finiteSectorDomain E) := by
  have hle : T.domRestrict (finiteSectorDomain E) ≤ T := LinearPMap.domRestrict_le
  have hclose := (LinearPMap.IsClosed.isClosable (f := T) hT).leIsClosable hle
  refine ⟨hfin,LinearPMap.eq_of_eq_graph ?_⟩
  rw [← hclose.graph_closure_eq_closure_graph]
  apply SetLike.coe_injective
  change closure ((T.domRestrict (finiteSectorDomain E)).graph : Set (lp E 2 × lp E 2)) =
    (T.graph : Set (lp E 2 × lp E 2))
  apply le_antisymm
  · exact closure_minimal (LinearPMap.le_graph_of_le hle) hT
  · intro p hp
    obtain ⟨u,hu⟩ := T.mem_graph_iff'.mp hp
    rw [← hu]
    apply mem_closure_of_tendsto (hc u)
    apply Eventually.of_forall
    intro m
    exact (T.domRestrict (finiteSectorDomain E)).mem_graph_iff.mpr
      ⟨⟨cutoff E (r m) u,cutoff_mem_finiteSectorDomain E (r m) u,
          hfin (cutoff_mem_finiteSectorDomain E (r m) u)⟩,rfl,rfl⟩

lemma maximalSectorCreation_core (C : ∀ n, E n →L[ℂ] E (n+1)) :
    (maximalSectorCreation C).HasCore (finiteSectorDomain E) := by
  apply finiteSector_core_of_cutoffs _ (maximalSectorCreation_closed C) (finiteSector_le_creation C) id
  intro u
  simp only [id_eq,maximalSectorCreation_cutoff]
  exact (cutoff_tendsto E (u : lp E 2)).prodMk_nhds
    ((cutoff_tendsto E (maximalSectorCreation C u)).comp (tendsto_add_atTop_nat 1))

lemma maximalSectorAnnihilation_core (A : ∀ n, E (n+1) →L[ℂ] E n) :
    (maximalSectorAnnihilation A).HasCore (finiteSectorDomain E) := by
  apply finiteSector_core_of_cutoffs _ (maximalSectorAnnihilation_closed A) (finiteSector_le_annihilation A) (·+1)
  intro u
  simp only [maximalSectorAnnihilation_cutoff_succ]
  exact ((cutoff_tendsto E (u : lp E 2)).comp (tendsto_add_atTop_nat 1)).prodMk_nhds
    (cutoff_tendsto E (maximalSectorAnnihilation A u))

lemma creation_single_graph (C : ∀ n, E n →L[ℂ] E (n+1)) (n : ℕ) (x : E n) :
    (lp.single 2 n x,lp.single 2 (n+1) (C n x)) ∈ (maximalSectorCreation C).graph := by
  change _ ∈ (sectorOutputMap (creationSectorOutput C)).graph
  rw [sectorOutputMap_graph]
  intro j
  cases j with
  | zero => exact lp.single_apply_ne _ _ _ (by omega)
  | succ j =>
    change lp.single 2 (n+1) (C n x) (j+1) = C j (lp.single 2 n x j)
    by_cases hj : j = n
    · subst j; rw [lp.single_apply_self,lp.single_apply_self]
    · rw [lp.single_apply_ne _ _ _ (by omega),lp.single_apply_ne _ _ _ hj,map_zero]

lemma annihilation_single_graph (A : ∀ n, E (n+1) →L[ℂ] E n) (n : ℕ) (x : E (n+1)) :
    (lp.single 2 (n+1) x,lp.single 2 n (A n x)) ∈ (maximalSectorAnnihilation A).graph := by
  change _ ∈ (sectorOutputMap (annihilationSectorOutput A)).graph
  rw [sectorOutputMap_graph]
  intro j
  change lp.single 2 n (A n x) j = A j (lp.single 2 (n+1) x (j+1))
  by_cases hj : j = n
  · subst j; rw [lp.single_apply_self,lp.single_apply_self]
  · rw [lp.single_apply_ne _ _ _ hj,lp.single_apply_ne _ _ _ (by omega),map_zero]

lemma annihilation_vacuum_graph (A : ∀ n, E (n+1) →L[ℂ] E n) (x : E 0) :
    (lp.single 2 0 x,0) ∈ (maximalSectorAnnihilation A).graph := by
  change _ ∈ (sectorOutputMap (annihilationSectorOutput A)).graph
  rw [sectorOutputMap_graph]
  intro j
  change (0 : E j) = A j (lp.single 2 0 x (j+1))
  rw [lp.single_apply_ne _ _ _ (by omega),map_zero]

variable (C : ∀ n, E n →L[ℂ] E (n+1)) (A : ∀ n, E (n+1) →L[ℂ] E n)
  (hCA : ∀ n (x : E n) (y : E (n+1)), ⟪C n x,y⟫_ℂ = ⟪x,A n y⟫_ℂ)

include hCA in
lemma creation_annihilation_pairing (u : (maximalSectorCreation C).domain)
    (v : (maximalSectorAnnihilation A).domain) :
    ⟪maximalSectorCreation C u,(v : lp E 2)⟫_ℂ =
      ⟪(u : lp E 2),maximalSectorAnnihilation A v⟫_ℂ := by
  let w := maximalSectorCreation C u
  let z := maximalSectorAnnihilation A v
  let g : ℕ → ℂ := fun n => ⟪w n,(v : lp E 2) n⟫_ℂ
  have hg : Summable g := lp.summable_inner w (v : lp E 2)
  have h₀ : g 0 = 0 := by
    change ⟪maximalSectorCreation C u 0,(v : lp E 2) 0⟫_ℂ = _
    rw [maximalSectorCreation_zero,inner_zero_left]
  calc
    _ = ∑' n, g n := lp.inner_eq_tsum _ _
    _ = ∑' n, g (n+1) := by rw [hg.tsum_eq_zero_add,h₀,zero_add]
    _ = ∑' n, ⟪(u : lp E 2) n,z n⟫_ℂ := by
      apply tsum_congr
      intro n
      change ⟪maximalSectorCreation C u (n+1),(v : lp E 2) (n+1)⟫_ℂ =
        ⟪(u : lp E 2) n,maximalSectorAnnihilation A v n⟫_ℂ
      rw [maximalSectorCreation_succ,maximalSectorAnnihilation_apply]
      exact hCA n _ _
    _ = _ := (lp.inner_eq_tsum _ _).symm

include hCA in
lemma annihilation_creation_pairing (u : (maximalSectorAnnihilation A).domain)
    (v : (maximalSectorCreation C).domain) :
    ⟪maximalSectorAnnihilation A u,(v : lp E 2)⟫_ℂ =
      ⟪(u : lp E 2),maximalSectorCreation C v⟫_ℂ := by
  rw [← inner_conj_symm (maximalSectorAnnihilation A u),← inner_conj_symm (u : lp E 2),
    creation_annihilation_pairing C A hCA v u]

variable [∀ n, CompleteSpace (E n)]

include hCA in
lemma creation_adjoint_eq : (maximalSectorCreation C).adjoint = maximalSectorAnnihilation A := by
  apply le_antisymm
  · apply LinearPMap.le_of_le_graph
    intro p hp
    obtain ⟨v,hv⟩ := (maximalSectorCreation C).adjoint.mem_graph_iff'.mp hp
    rw [← hv]
    change _ ∈ (sectorOutputMap (annihilationSectorOutput A)).graph
    rw [sectorOutputMap_graph]
    intro n
    change (maximalSectorCreation C).adjoint v n = A n ((v : lp E 2) (n+1))
    apply ext_inner_left ℂ
    intro x
    have hg := creation_single_graph C n x
    let u : (maximalSectorCreation C).domain := ⟨_,(maximalSectorCreation C).mem_domain_of_mem_graph hg⟩
    have hu : maximalSectorCreation C u = lp.single 2 (n+1) (C n x) :=
      (maximalSectorCreation C).mem_graph_snd_inj ((maximalSectorCreation C).mem_graph u) hg rfl
    have h := GW.Operators.adjoint_pairing (maximalSectorCreation C) (maximalSectorCreation_dense C) u v
    rw [hu] at h
    change ⟪lp.single 2 (n+1) (C n x),(v : lp E 2)⟫_ℂ =
      ⟪lp.single 2 n x,(maximalSectorCreation C).adjoint v⟫_ℂ at h
    rw [lp.inner_single_left,lp.inner_single_left] at h
    exact h.symm.trans (hCA n x _)
  · apply LinearPMap.IsFormalAdjoint.le_adjoint (maximalSectorCreation_dense C)
    exact creation_annihilation_pairing C A hCA

include hCA in
lemma annihilation_adjoint_eq : (maximalSectorAnnihilation A).adjoint = maximalSectorCreation C := by
  apply le_antisymm
  · apply LinearPMap.le_of_le_graph
    intro p hp
    obtain ⟨v,hv⟩ := (maximalSectorAnnihilation A).adjoint.mem_graph_iff'.mp hp
    rw [← hv]
    change _ ∈ (sectorOutputMap (creationSectorOutput C)).graph
    rw [sectorOutputMap_graph]
    intro n
    cases n with
    | zero =>
      change (maximalSectorAnnihilation A).adjoint v 0 = 0
      apply ext_inner_left ℂ
      intro x
      have hg := annihilation_vacuum_graph A x
      let u : (maximalSectorAnnihilation A).domain := ⟨_,(maximalSectorAnnihilation A).mem_domain_of_mem_graph hg⟩
      have hu : maximalSectorAnnihilation A u = 0 :=
        (maximalSectorAnnihilation A).mem_graph_snd_inj ((maximalSectorAnnihilation A).mem_graph u) hg rfl
      have h := GW.Operators.adjoint_pairing (maximalSectorAnnihilation A)
        (maximalSectorAnnihilation_dense A) u v
      rw [hu] at h
      change ⟪(0 : lp E 2),(v : lp E 2)⟫_ℂ =
        ⟪lp.single 2 0 x,(maximalSectorAnnihilation A).adjoint v⟫_ℂ at h
      rw [inner_zero_left,lp.inner_single_left] at h
      simpa only [inner_zero_right] using h.symm
    | succ n =>
      change (maximalSectorAnnihilation A).adjoint v (n+1) = C n ((v : lp E 2) n)
      apply ext_inner_left ℂ
      intro x
      have hg := annihilation_single_graph A n x
      let u : (maximalSectorAnnihilation A).domain := ⟨_,(maximalSectorAnnihilation A).mem_domain_of_mem_graph hg⟩
      have hu : maximalSectorAnnihilation A u = lp.single 2 n (A n x) :=
        (maximalSectorAnnihilation A).mem_graph_snd_inj ((maximalSectorAnnihilation A).mem_graph u) hg rfl
      have h := GW.Operators.adjoint_pairing (maximalSectorAnnihilation A)
        (maximalSectorAnnihilation_dense A) u v
      rw [hu] at h
      change ⟪lp.single 2 n (A n x),(v : lp E 2)⟫_ℂ =
        ⟪lp.single 2 (n+1) x,(maximalSectorAnnihilation A).adjoint v⟫_ℂ at h
      rw [lp.inner_single_left,lp.inner_single_left] at h
      calc
        _ = ⟪A n x,(v : lp E 2) n⟫_ℂ := h.symm
        _ = starRingEnd ℂ ⟪(v : lp E 2) n,A n x⟫_ℂ := (inner_conj_symm _ _).symm
        _ = starRingEnd ℂ ⟪C n ((v : lp E 2) n),x⟫_ℂ :=
          congrArg (starRingEnd ℂ) (hCA n ((v : lp E 2) n) x).symm
        _ = _ := inner_conj_symm _ _
  · apply LinearPMap.IsFormalAdjoint.le_adjoint (maximalSectorAnnihilation_dense A)
    exact annihilation_creation_pairing C A hCA

end ShiftedGraphs
lemma transportedGraph_closed {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] (U : H ≃ₗᵢ[ℂ] K) (A : K →ₗ.[ℂ] K)
    (hA : IsClosed (A.graph : Set (K × K))) :
    IsClosed ((representationTransport U A).graph : Set (H × H)) := by
  have he : ((representationTransport U A).graph : Set (H × H)) =
      (fun p : H × H => (U p.1,U p.2)) ⁻¹' (A.graph : Set (K × K)) :=
    Set.ext (representationTransport_graph U A)
  rw [he]
  exact hA.preimage ((U.continuous.comp continuous_fst).prodMk (U.continuous.comp continuous_snd))

lemma generalizedCreation_closed (F : BosonKernel ElectronL2) :
    (generalizedCreation F).IsClosed :=
  transportedGraph_closed electronBosonUnitary.symm _ (maximalSectorCreation_closed (generalizedCreationSector F))

lemma generalizedAnnihilation_closed (F : BosonKernel ElectronL2) :
    (generalizedAnnihilation F).IsClosed :=
  transportedGraph_closed electronBosonUnitary.symm _ (maximalSectorAnnihilation_closed (generalizedAnnihilationSector F))

lemma generalizedCreation_adjoint_eq (F : BosonKernel ElectronL2) :
    (generalizedCreation F).adjoint = generalizedAnnihilation F := by
  let C := sectorCreation physicalSectorKernel F
  let A := sectorAnnihilation physicalSectorKernel F
  change (representationTransport electronBosonUnitary.symm (maximalSectorCreation C)).adjoint =
    representationTransport electronBosonUnitary.symm (maximalSectorAnnihilation A)
  exact (representationTransport_adjoint _ _ (maximalSectorCreation_dense C)).trans
    (congrArg (representationTransport electronBosonUnitary.symm)
      (creation_adjoint_eq C A (sectorCreation_pairing physicalSectorKernel F)))

lemma generalizedAnnihilation_adjoint_eq (F : BosonKernel ElectronL2) :
    (generalizedAnnihilation F).adjoint = generalizedCreation F := by
  let C := sectorCreation physicalSectorKernel F
  let A := sectorAnnihilation physicalSectorKernel F
  change (representationTransport electronBosonUnitary.symm (maximalSectorAnnihilation A)).adjoint =
    representationTransport electronBosonUnitary.symm (maximalSectorCreation C)
  exact (representationTransport_adjoint _ _ (maximalSectorAnnihilation_dense A)).trans
    (congrArg (representationTransport electronBosonUnitary.symm)
      (annihilation_adjoint_eq C A (sectorCreation_pairing physicalSectorKernel F)))

lemma ordinaryCreation_adjoint_eq (f : OneBoson) : (ordinaryCreation f).adjoint = ordinaryAnnihilation f :=
  creation_adjoint_eq _ _ (sectorCreation_pairing ordinarySectorKernel (ordinaryKernel f))

lemma ordinaryAnnihilation_adjoint_eq (f : OneBoson) : (ordinaryAnnihilation f).adjoint = ordinaryCreation f :=
  annihilation_adjoint_eq _ _ (sectorCreation_pairing ordinarySectorKernel (ordinaryKernel f))

lemma restrictedGraph_iff {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (T : H →ₗ.[ℂ] H) (V : Submodule ℂ H) (p : H × H) :
    p ∈ (T.domRestrict V).graph ↔ p ∈ T.graph ∧ p.1 ∈ V := by
  constructor
  · intro hp
    obtain ⟨u,hu⟩ := (T.domRestrict V).mem_graph_iff'.mp hp
    rw [← hu]
    exact ⟨LinearPMap.le_graph_of_le LinearPMap.domRestrict_le ((T.domRestrict V).mem_graph u), u.property.1⟩
  · rintro ⟨hp,hV⟩
    obtain ⟨u,hu⟩ := T.mem_graph_iff'.mp hp
    have hx : (u : H) ∈ V := by
      have h : (u : H) = p.1 := congrArg Prod.fst hu
      rw [h]
      exact hV
    exact (T.domRestrict V).mem_graph_iff'.mpr ⟨⟨u, hx,u.property⟩,hu⟩

lemma transportedGraph_hasCore {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (U : H ≃ₗᵢ[ℂ] K) (T : K →ₗ.[ℂ] K) (V : Submodule ℂ K)
    (hc : T.HasCore V) (hT : T.IsClosed) :
    (representationTransport U T).HasCore (V.comap U.toLinearMap) := by
  let S := representationTransport U T
  let W := V.comap U.toLinearMap
  let P := U.toHomeomorph.prodCongr U.toHomeomorph
  have hS : S.IsClosed := transportedGraph_closed U T hT
  have he (p : H × H) : p ∈ S.graph ↔ P p ∈ T.graph :=
    representationTransport_graph U T p
  have he' : ((S.domRestrict W).graph : Set (H × H)) =
      P ⁻¹' ((T.domRestrict V).graph : Set (K × K)) := by
    ext p
    change p ∈ (S.domRestrict W).graph ↔ P p ∈ (T.domRestrict V).graph
    rw [restrictedGraph_iff,restrictedGraph_iff,he]
    rfl
  have hA := hT.isClosable.leIsClosable (show T.domRestrict V ≤ T from LinearPMap.domRestrict_le)
  have hB := hS.isClosable.leIsClosable (show S.domRestrict W ≤ S from LinearPMap.domRestrict_le)
  have hcl : closure ((T.domRestrict V).graph : Set (K × K)) = (T.graph : Set (K × K)) := by
    have h := congrArg LinearPMap.graph hc.closure_eq
    rw [← hA.graph_closure_eq_closure_graph] at h
    exact congrArg (fun V : Submodule ℂ (K × K) => (V : Set (K × K))) h
  refine ⟨fun u hu => hc.le_domain hu,LinearPMap.eq_of_eq_graph ?_⟩
  change (S.domRestrict W).closure.graph = S.graph
  rw [← hB.graph_closure_eq_closure_graph]
  apply SetLike.coe_injective
  change closure ((S.domRestrict W).graph : Set (H × H)) = (S.graph : Set (H × H))
  rw [he',← P.isOpenMap.preimage_closure_eq_closure_preimage P.continuous,hcl]
  exact (Set.ext he).symm

abbrev physicalFiniteSectorCore : Submodule ℂ Physical :=
  (finiteSectorDomain ElectronSector).comap electronBosonUnitary.symm.toLinearMap

lemma generalizedCreation_core (F : BosonKernel ElectronL2) :
    (generalizedCreation F).HasCore physicalFiniteSectorCore :=
  transportedGraph_hasCore electronBosonUnitary.symm _ _
    (maximalSectorCreation_core (generalizedCreationSector F))
    (maximalSectorCreation_closed (generalizedCreationSector F))

lemma generalizedAnnihilation_core (F : BosonKernel ElectronL2) :
    (generalizedAnnihilation F).HasCore physicalFiniteSectorCore :=
  transportedGraph_hasCore electronBosonUnitary.symm _ _
    (maximalSectorAnnihilation_core (generalizedAnnihilationSector F))
    (maximalSectorAnnihilation_closed (generalizedAnnihilationSector F))

lemma ordinaryCreation_closed (f : OneBoson) : (ordinaryCreation f).IsClosed :=
  maximalSectorCreation_closed (sectorCreation ordinarySectorKernel (ordinaryKernel f))

lemma ordinaryAnnihilation_closed (f : OneBoson) : (ordinaryAnnihilation f).IsClosed :=
  maximalSectorAnnihilation_closed (sectorAnnihilation ordinarySectorKernel (ordinaryKernel f))

lemma ordinaryCreation_core (f : OneBoson) : (ordinaryCreation f).HasCore (finiteSectorDomain Sector) :=
  maximalSectorCreation_core (sectorCreation ordinarySectorKernel (ordinaryKernel f))

lemma ordinaryAnnihilation_core (f : OneBoson) : (ordinaryAnnihilation f).HasCore (finiteSectorDomain Sector) :=
  maximalSectorAnnihilation_core (sectorAnnihilation ordinarySectorKernel (ordinaryKernel f))

end GW.Fock
