module
public import GW.Spaces.WeightedL2
public import GW.Analysis.RealMultiplier
public import GW.Analysis.SeriesDomination
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ENNReal
namespace GW.Spaces
section Lifts
variable {A B C W V Z : Type*}
  [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedAddCommGroup B] [NormedSpace ℂ B]
  [NormedAddCommGroup C] [NormedSpace ℂ C] [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup Z] [NormedSpace ℂ Z]

def CarrierIntertwines (J : W →L[ℂ] A) (K : V →L[ℂ] B) (T : A →ₗ[ℂ] B)
    (L : W →L[ℂ] V) : Prop := ∀ w, K (L w) = T (J w)

lemma carrierLift_unique {J : W →L[ℂ] A} {K : V →L[ℂ] B} (hK : Function.Injective K)
    {T : A →ₗ[ℂ] B} {L M : W →L[ℂ] V}
    (hL : CarrierIntertwines J K T L) (hM : CarrierIntertwines J K T M) : L = M := by
  apply ContinuousLinearMap.ext
  intro w
  exact hK ((hL w).trans (hM w).symm)

lemma carrierLift_exists {J : W →L[ℂ] A} {K : V →L[ℂ] B} (hK : Function.Injective K)
    {T : A →ₗ[ℂ] B} {c : ℝ} (hc : 0 ≤ c)
    (hex : ∀ w, ∃ v, K v = T (J w) ∧ ‖v‖ ≤ c*‖w‖) :
    ∃ L : W →L[ℂ] V, ‖L‖ ≤ c ∧ CarrierIntertwines J K T L := by
  classical
  choose f hf hb using hex
  let l : W →ₗ[ℂ] V :=
    { toFun := f
      map_add' := by intro w z; apply hK; simp only [map_add,hf]
      map_smul' := by intro r w; apply hK; simp only [map_smul,RingHom.id_apply,hf] }
  let L := l.mkContinuous c hb
  refine ⟨L,?_,hf⟩
  exact ContinuousLinearMap.opNorm_le_bound L hc hb

lemma carrierLift_iff {J : W →L[ℂ] A} {K : V →L[ℂ] B} (hK : Function.Injective K)
    {T : A →ₗ[ℂ] B} {c : ℝ} (hc : 0 ≤ c) :
    (∀ w, ∃ v, K v = T (J w) ∧ ‖v‖ ≤ c*‖w‖) ↔
      ∃! L : W →L[ℂ] V, ‖L‖ ≤ c ∧ CarrierIntertwines J K T L := by
  constructor
  · intro h
    obtain ⟨L,hLc,hL⟩ := carrierLift_exists hK hc h
    exact ⟨L,⟨hLc,hL⟩,fun M hM => carrierLift_unique hK hM.2 hL⟩
  · rintro ⟨L,⟨hLc,hL⟩,_⟩ w
    exact ⟨L w,hL w,(L.le_opNorm w).trans (mul_le_mul_of_nonneg_right hLc (norm_nonneg _))⟩

lemma carrierLift_identity (J : W →L[ℂ] A) :
    CarrierIntertwines J J LinearMap.id (ContinuousLinearMap.id ℂ W) := fun _ => rfl

lemma carrierLift_comp {J : W →L[ℂ] A} {K : V →L[ℂ] B} {P : Z →L[ℂ] C}
    {T : A →ₗ[ℂ] B} {U : B →ₗ[ℂ] C} {L : W →L[ℂ] V} {M : V →L[ℂ] Z}
    (hL : CarrierIntertwines J K T L) (hM : CarrierIntertwines K P U M) :
    CarrierIntertwines J P (U.comp T) (M.comp L) := by
  intro w
  exact (hM (L w)).trans (congrArg U (hL w))

lemma carrierLift_inverse {J : W →L[ℂ] A} {K : V →L[ℂ] B}
    (hJ : Function.Injective J) (hK : Function.Injective K)
    {T : A →ₗ[ℂ] B} {U : B →ₗ[ℂ] A} {L : W →L[ℂ] V} {M : V →L[ℂ] W}
    (hL : CarrierIntertwines J K T L) (hM : CarrierIntertwines K J U M)
    (hUT : U.comp T = LinearMap.id) (hTU : T.comp U = LinearMap.id) :
    M.comp L = ContinuousLinearMap.id ℂ W ∧ L.comp M = ContinuousLinearMap.id ℂ V := by
  constructor
  · apply carrierLift_unique hJ
      (J := J) (T := LinearMap.id) (M := ContinuousLinearMap.id ℂ W)
    · simpa only [hUT] using carrierLift_comp hL hM
    · exact carrierLift_identity J
  · apply carrierLift_unique hK
      (J := K) (T := LinearMap.id) (M := ContinuousLinearMap.id ℂ V)
    · simpa only [hTU] using carrierLift_comp hM hL
    · exact carrierLift_identity K
end Lifts
section GraphInterfaces
variable {A B W V : Type*}
  [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedAddCommGroup B] [NormedSpace ℂ B]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- An interface of proved reciprocal-weight identities, instantiated below on actual carriers. -/
structure WeightedGraph (A W : Type*) [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup W] [NormedSpace ℂ W] where
  domain : Submodule ℂ A
  embedding : W →L[ℂ] A
  embedding_injective : Function.Injective embedding
  embedding_norm_le : ‖embedding‖ ≤ 1
  embedding_dense : DenseRange embedding
  product : domain →ₗ[ℂ] W
  embedding_mem : ∀ w, embedding w ∈ domain
  product_embedding : ∀ w, product ⟨embedding w,embedding_mem w⟩ = w
  embedding_product : ∀ u : domain, embedding (product u) = (u : A)

variable (G : WeightedGraph A W) (K : WeightedGraph B V)

def weightedBoundOnDomain (T : A →ₗ[ℂ] B) (c : ℝ) : Prop :=
  ∀ u : G.domain, ∃ hmem : T (u : A) ∈ K.domain,
    ‖K.product ⟨T (u : A),hmem⟩‖ ≤ c*‖G.product u‖

lemma weightedGraph_lift_iff (T : A →ₗ[ℂ] B) {c : ℝ} (hc : 0 ≤ c) :
    weightedBoundOnDomain G K T c ↔ ∃! L : W →L[ℂ] V,
      ‖L‖ ≤ c ∧ CarrierIntertwines G.embedding K.embedding T L := by
  rw [← carrierLift_iff K.embedding_injective hc]
  constructor
  · intro hb f
    obtain ⟨hmem,hbound⟩ := hb ⟨G.embedding f,G.embedding_mem f⟩
    refine ⟨K.product ⟨T (G.embedding f),hmem⟩,K.embedding_product _,?_⟩
    simpa only [G.product_embedding] using hbound
  · intro hex u
    obtain ⟨v,hv,hbound⟩ := hex (G.product u)
    rw [G.embedding_product] at hv
    have hmem : T (u : A) ∈ K.domain := hv ▸ K.embedding_mem v
    refine ⟨hmem,?_⟩
    have hprod : K.product ⟨T (u : A),hmem⟩ = v := by
      apply K.embedding_injective
      rw [K.embedding_product,hv]
    rw [hprod]
    exact hbound

lemma weightedGraph_lift_formula (T : A →ₗ[ℂ] B) (L : W →L[ℂ] V)
    (hL : CarrierIntertwines G.embedding K.embedding T L) (w : W) :
    ∃ hmem : T (G.embedding w) ∈ K.domain,
      L w = K.product ⟨T (G.embedding w),hmem⟩ := by
  have hmem : T (G.embedding w) ∈ K.domain := (hL w) ▸ K.embedding_mem (L w)
  refine ⟨hmem,?_⟩
  apply K.embedding_injective
  rw [hL w,K.embedding_product]
end GraphInterfaces


section WeightedDomainNorm
variable {A W : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W]

/-- A separate mathematical weighted domain; no new norm is put on the ambient subtype. -/
def WeightedDomain (G : WeightedGraph A W) : Type _ := G.domain

instance weightedDomainAddCommGroup (G : WeightedGraph A W) : AddCommGroup (WeightedDomain G) :=
  inferInstanceAs (AddCommGroup G.domain)
instance weightedDomainModule (G : WeightedGraph A W) : Module ℂ (WeightedDomain G) :=
  inferInstanceAs (Module ℂ G.domain)

lemma weightedGraph_product_injective (G : WeightedGraph A W) : Function.Injective G.product := by
  intro u v he
  apply Subtype.ext
  simpa only [G.embedding_product] using congrArg G.embedding he

lemma weightedGraph_product_surjective (G : WeightedGraph A W) : Function.Surjective G.product :=
  fun w => ⟨⟨G.embedding w,G.embedding_mem w⟩,G.product_embedding w⟩

def weightedDomainCoordinates (G : WeightedGraph A W) : WeightedDomain G ≃ₗ[ℂ] W :=
  LinearEquiv.ofBijective G.product ⟨weightedGraph_product_injective G,weightedGraph_product_surjective G⟩

instance weightedDomainNormedAddCommGroup (G : WeightedGraph A W) : NormedAddCommGroup (WeightedDomain G) :=
  NormedAddCommGroup.induced _ _ (weightedDomainCoordinates G) (weightedDomainCoordinates G).injective

instance weightedDomainInnerProductSpace (G : WeightedGraph A W) : InnerProductSpace ℂ (WeightedDomain G) :=
  InnerProductSpace.induced (weightedDomainCoordinates G).toLinearMap

def weightedDomainIsometry (G : WeightedGraph A W) : WeightedDomain G ≃ₗᵢ[ℂ] W where
  toLinearEquiv := weightedDomainCoordinates G
  norm_map' _ := rfl

instance weightedDomainCompleteSpace (G : WeightedGraph A W) [CompleteSpace W] : CompleteSpace (WeightedDomain G) := by
  let i := weightedDomainIsometry G
  let e : WeightedDomain G ≃ᵤ W :=
    { toEquiv := i.toLinearEquiv.toEquiv
      uniformContinuous_toFun := i.isometry.uniformContinuous
      uniformContinuous_invFun := i.symm.isometry.uniformContinuous }
  exact e.completeSpace_iff.mpr inferInstance

lemma weightedDomain_norm (G : WeightedGraph A W) (u : WeightedDomain G) :
    ‖u‖ = ‖G.product (u : G.domain)‖ := rfl

lemma weightedDomain_inner (G : WeightedGraph A W) (u v : WeightedDomain G) :
    ⟪u,v⟫_ℂ = ⟪G.product (u : G.domain),G.product (v : G.domain)⟫_ℂ := rfl

lemma weightedDomain_embedding (G : WeightedGraph A W) (u : WeightedDomain G) :
    G.embedding (weightedDomainIsometry G u) = G.domain.subtype (show G.domain from u) :=
  G.embedding_product (show G.domain from u)
end WeightedDomainNorm

variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] {μ : Measure X} {w : X → ℝ}

def reciprocalMap (hw : Measurable w) (hw1 : ∀ x, 1 ≤ w x) : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  GW.Analysis.boundedMultiplier (fun x => (((w x)⁻¹ : ℝ) : ℂ))
    (Complex.continuous_ofReal.measurable.comp hw.inv) (WeightedL2.reciprocal_bound hw1)

lemma reciprocalMap_apply (hw : Measurable w) (hw1 : ∀ x, 1 ≤ w x) (f : Lp H 2 μ) :
    reciprocalMap hw hw1 f = WeightedL2.embed hw hw1
      ((WeightedL2.coordinates (H := H) (w := w) (μ := μ)).symm f) := by
  change reciprocalMap hw hw1 f = reciprocalMap hw hw1
    (WeightedL2.coordinates ((WeightedL2.coordinates (H := H) (w := w) (μ := μ)).symm f))
  rw [LinearIsometryEquiv.apply_symm_apply]

lemma reciprocalMap_norm_le (hw : Measurable w) (hw1 : ∀ x, 1 ≤ w x) (f : Lp H 2 μ) :
    ‖reciprocalMap hw hw1 f‖ ≤ ‖f‖ := by
  rw [reciprocalMap_apply]
  exact (WeightedL2.embed_norm_le hw hw1 _).trans_eq (LinearIsometryEquiv.norm_map _ _)

lemma reciprocalMap_injective (hw : Measurable w) (hw1 : ∀ x, 1 ≤ w x) :
    Function.Injective (reciprocalMap (H := H) (μ := μ) hw hw1) := by
  intro f g h
  rw [reciprocalMap_apply,reciprocalMap_apply] at h
  exact (WeightedL2.coordinates (H := H) (w := w) (μ := μ)).symm.injective
    (WeightedL2.embed_injective hw hw1 h)

lemma reciprocalMap_mem_domain (hw : Measurable w) (hw1 : ∀ x, 1 ≤ w x) (f : Lp H 2 μ) :
    reciprocalMap hw hw1 f ∈ (GW.Analysis.realMultiplier (H := H) w μ).domain := by
  rw [reciprocalMap_apply]
  exact WeightedL2.embed_mem_domain hw hw1 _

lemma reciprocalMap_product (hw : Measurable w) (hw1 : ∀ x, 1 ≤ w x) (f : Lp H 2 μ) :
    GW.Analysis.realMultiplier w μ ⟨reciprocalMap hw hw1 f,reciprocalMap_mem_domain hw hw1 f⟩ = f := by
  have h := WeightedL2.weighted_embed_ae hw hw1
    ((WeightedL2.coordinates (H := H) (w := w) (μ := μ)).symm f)
  rw [← reciprocalMap_apply hw hw1 f,LinearIsometryEquiv.apply_symm_apply] at h
  apply Lp.ext
  exact (GW.Analysis.realMultiplier_ae w _).symm.trans h

lemma reciprocalMap_inverse (hw : Measurable w) (hw1 : ∀ x, 1 ≤ w x)
    (u : (GW.Analysis.realMultiplier (H := H) w μ).domain) :
    reciprocalMap hw hw1 (GW.Analysis.realMultiplier w μ u) = (u : Lp H 2 μ) := by
  have hu : (u : Lp H 2 μ) ∈ Set.range (WeightedL2.embed (H := H) hw hw1) := by
    rw [WeightedL2.embed_range]
    exact u.property
  obtain ⟨f,hf⟩ := hu
  have ha := WeightedL2.weighted_embed_ae hw hw1 f
  rw [hf] at ha
  have he : GW.Analysis.realMultiplier w μ u = WeightedL2.coordinates f := by
    apply Lp.ext
    exact (GW.Analysis.realMultiplier_ae w u).symm.trans ha
  rw [he,reciprocalMap_apply,LinearIsometryEquiv.symm_apply_apply]
  exact hf

omit [MeasurableSpace X] in
lemma positive_realCutoffSet (hw1 : ∀ x, 1 ≤ w x) (n : ℕ) :
    GW.Analysis.realCutoffSet w n = {x | w x ≤ (n : ℝ)} := by
  ext x
  change |w x| ≤ (n : ℝ) ↔ w x ≤ (n : ℝ)
  rw [abs_of_nonneg (zero_le_one.trans (hw1 x))]

/-- Exactly the source's three bounded-multiplier invariances on the closed subspace. -/
structure WeightInvariant (S : ClosedSubmodule ℂ (Lp H 2 μ)) (hw : Measurable w)
    (hw1 : ∀ x, 1 ≤ w x) : Prop where
  reciprocal : ∀ u : S, reciprocalMap hw hw1 (u : Lp H 2 μ) ∈ S
  cutoff : ∀ n : ℕ, 1 ≤ n → ∀ u : S, GW.Analysis.realCutoff hw n (u : Lp H 2 μ) ∈ S
  truncated : ∀ n : ℕ, 1 ≤ n → ∀ u : S, GW.Analysis.truncatedReal hw n (u : Lp H 2 μ) ∈ S

lemma invariant_product_mem {S : ClosedSubmodule ℂ (Lp H 2 μ)} {hw : Measurable w}
    {hw1 : ∀ x, 1 ≤ w x} (h : WeightInvariant S hw hw1)
    (u : (GW.Analysis.realMultiplier (H := H) w μ).domain) (hu : (u : Lp H 2 μ) ∈ S) :
    GW.Analysis.realMultiplier w μ u ∈ S := by
  have hs (n : ℕ) : GW.Analysis.realCutoff hw (n+1) (GW.Analysis.realMultiplier w μ u) ∈ S := by
    rw [GW.Analysis.realCutoff_action]
    exact h.truncated (n+1) (Nat.succ_le_succ (Nat.zero_le n)) ⟨u,hu⟩
  have ht := (GW.Analysis.realCutoff_tendsto hw (GW.Analysis.realMultiplier w μ u)).comp
    (Filter.tendsto_add_atTop_nat 1)
  exact S.isClosed.mem_of_tendsto ht (Filter.Eventually.of_forall hs)

def restrictedWeightDomain (S : ClosedSubmodule ℂ (Lp H 2 μ)) (w : X → ℝ) : Submodule ℂ S :=
  (GW.Analysis.realMultiplier (H := H) w μ).domain.comap S.toSubmodule.subtype

def restrictedWeightInput (S : ClosedSubmodule ℂ (Lp H 2 μ)) (w : X → ℝ) :
    restrictedWeightDomain S w →ₗ[ℂ] (GW.Analysis.realMultiplier (H := H) w μ).domain where
  toFun u := ⟨(u : S),u.property⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

def restrictedWeightProduct {S : ClosedSubmodule ℂ (Lp H 2 μ)} {hw : Measurable w}
    {hw1 : ∀ x, 1 ≤ w x} (h : WeightInvariant S hw hw1) : restrictedWeightDomain S w →ₗ[ℂ] S :=
  ((GW.Analysis.realMultiplier (H := H) w μ).toFun.comp (restrictedWeightInput S w)).codRestrict
    S.toSubmodule (fun u => invariant_product_mem h (restrictedWeightInput S w u) (u : S).property)

/-- The chosen complete carrier is the original Hilbert space S, with its original norm. -/
def RestrictedWeightedCarrier (S : ClosedSubmodule ℂ (Lp H 2 μ)) (_w : X → ℝ) : Type _ := S

instance restrictedCarrierNormedAddCommGroup (S : ClosedSubmodule ℂ (Lp H 2 μ)) :
    NormedAddCommGroup (RestrictedWeightedCarrier S w) := inferInstanceAs (NormedAddCommGroup S)
instance restrictedCarrierNormedSpace (S : ClosedSubmodule ℂ (Lp H 2 μ)) :
    NormedSpace ℂ (RestrictedWeightedCarrier S w) := inferInstanceAs (NormedSpace ℂ S)
instance restrictedCarrierInnerProductSpace (S : ClosedSubmodule ℂ (Lp H 2 μ)) :
    InnerProductSpace ℂ (RestrictedWeightedCarrier S w) := inferInstanceAs (InnerProductSpace ℂ S)
instance restrictedCarrierCompleteSpace (S : ClosedSubmodule ℂ (Lp H 2 μ)) [CompleteSpace H] :
    CompleteSpace (RestrictedWeightedCarrier S w) := inferInstanceAs (CompleteSpace S)

def restrictedCoordinates (S : ClosedSubmodule ℂ (Lp H 2 μ)) (w : X → ℝ) :
    RestrictedWeightedCarrier S w ≃ₗᵢ[ℂ] S := LinearIsometryEquiv.refl ℂ S

def restrictedReciprocal {S : ClosedSubmodule ℂ (Lp H 2 μ)} {hw : Measurable w}
    {hw1 : ∀ x, 1 ≤ w x} (h : WeightInvariant S hw hw1) : S →L[ℂ] S :=
  ((reciprocalMap hw hw1).comp S.toSubmodule.subtypeL).codRestrict S.toSubmodule h.reciprocal

def restrictedWeightEmbedding {S : ClosedSubmodule ℂ (Lp H 2 μ)} {hw : Measurable w}
    {hw1 : ∀ x, 1 ≤ w x} (h : WeightInvariant S hw hw1) : RestrictedWeightedCarrier S w →L[ℂ] S :=
  (restrictedReciprocal h).comp (restrictedCoordinates S w).toLinearIsometry.toContinuousLinearMap

lemma restrictedWeightEmbedding_norm {S : ClosedSubmodule ℂ (Lp H 2 μ)} {hw : Measurable w}
    {hw1 : ∀ x, 1 ≤ w x} (h : WeightInvariant S hw hw1) : ‖restrictedWeightEmbedding h‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖reciprocalMap hw hw1 ((restrictedCoordinates S w f : S) : Lp H 2 μ)‖ ≤ 1*‖f‖
  rw [one_mul]
  exact (reciprocalMap_norm_le hw hw1 _).trans_eq ((restrictedCoordinates S w).norm_map f)

lemma restrictedWeightEmbedding_injective {S : ClosedSubmodule ℂ (Lp H 2 μ)} {hw : Measurable w}
    {hw1 : ∀ x, 1 ≤ w x} (h : WeightInvariant S hw hw1) : Function.Injective (restrictedWeightEmbedding h) := by
  intro f g he
  apply (restrictedCoordinates S w).injective
  apply Subtype.ext
  apply reciprocalMap_injective hw hw1
  exact congrArg (fun u : S => (u : Lp H 2 μ)) he

lemma restrictedWeightEmbedding_mem {S : ClosedSubmodule ℂ (Lp H 2 μ)} {hw : Measurable w}
    {hw1 : ∀ x, 1 ≤ w x} (h : WeightInvariant S hw hw1) (f : RestrictedWeightedCarrier S w) :
    restrictedWeightEmbedding h f ∈ restrictedWeightDomain S w :=
  reciprocalMap_mem_domain hw hw1 _

def restrictedCarrierProduct {S : ClosedSubmodule ℂ (Lp H 2 μ)} {hw : Measurable w}
    {hw1 : ∀ x, 1 ≤ w x} (h : WeightInvariant S hw hw1) :
    restrictedWeightDomain S w →ₗ[ℂ] RestrictedWeightedCarrier S w :=
  (restrictedCoordinates S w).symm.toLinearMap.comp (restrictedWeightProduct h)

lemma restricted_product_embedding {S : ClosedSubmodule ℂ (Lp H 2 μ)} {hw : Measurable w}
    {hw1 : ∀ x, 1 ≤ w x} (h : WeightInvariant S hw hw1) (f : RestrictedWeightedCarrier S w) :
    restrictedCarrierProduct h ⟨restrictedWeightEmbedding h f,restrictedWeightEmbedding_mem h f⟩ = f := by
  apply (restrictedCoordinates S w).injective
  apply Subtype.ext
  change GW.Analysis.realMultiplier (H := H) w μ
    ⟨reciprocalMap hw hw1 ((restrictedCoordinates S w f : S) : Lp H 2 μ),_⟩ =
      ((restrictedCoordinates S w f : S) : Lp H 2 μ)
  exact reciprocalMap_product hw hw1 _

lemma restricted_embedding_product {S : ClosedSubmodule ℂ (Lp H 2 μ)} {hw : Measurable w}
    {hw1 : ∀ x, 1 ≤ w x} (h : WeightInvariant S hw hw1) (u : restrictedWeightDomain S w) :
    restrictedWeightEmbedding h (restrictedCarrierProduct h u) = (u : S) := by
  apply Subtype.ext
  change reciprocalMap hw hw1 (GW.Analysis.realMultiplier (H := H) w μ (restrictedWeightInput S w u)) =
    ((u : S) : Lp H 2 μ)
  exact reciprocalMap_inverse hw hw1 _

lemma restrictedWeightEmbedding_range {S : ClosedSubmodule ℂ (Lp H 2 μ)} {hw : Measurable w}
    {hw1 : ∀ x, 1 ≤ w x} (h : WeightInvariant S hw hw1) :
    Set.range (restrictedWeightEmbedding h) = (restrictedWeightDomain S w : Set S) := by
  ext u
  constructor
  · rintro ⟨f,rfl⟩
    exact restrictedWeightEmbedding_mem h f
  · intro hu
    exact ⟨restrictedCarrierProduct h ⟨u,hu⟩,restricted_embedding_product h ⟨u,hu⟩⟩

lemma restrictedWeightEmbedding_dense {S : ClosedSubmodule ℂ (Lp H 2 μ)} {hw : Measurable w}
    {hw1 : ∀ x, 1 ≤ w x} (h : WeightInvariant S hw hw1) : DenseRange (restrictedWeightEmbedding h) := by
  intro u
  let v : ℕ → S := fun n => ⟨GW.Analysis.realCutoff hw (n+1) (u : Lp H 2 μ),
    h.cutoff (n+1) (Nat.succ_le_succ (Nat.zero_le n)) u⟩
  have ht : Tendsto v atTop (𝓝 u) := by
    apply tendsto_subtype_rng.mpr
    exact (GW.Analysis.realCutoff_tendsto hw (u : Lp H 2 μ)).comp (tendsto_add_atTop_nat 1)
  apply mem_closure_of_tendsto ht
  apply Eventually.of_forall
  intro n
  rw [restrictedWeightEmbedding_range]
  exact GW.Analysis.realCutoff_mem_domain hw (n+1) (u : Lp H 2 μ)

def weightCutoffInput (hw : Measurable w) (n : ℕ)
    (u : (GW.Analysis.realMultiplier (H := H) w μ).domain) :
    (GW.Analysis.realMultiplier (H := H) w μ).domain :=
  ⟨GW.Analysis.realCutoff hw n (u : Lp H 2 μ),
    GW.Analysis.realCutoff_mem_domain hw n (u : Lp H 2 μ)⟩

lemma realCutoff_weighted_product (hw : Measurable w) (n : ℕ)
    (u : (GW.Analysis.realMultiplier (H := H) w μ).domain) :
    GW.Analysis.realMultiplier (H := H) w μ (weightCutoffInput hw n u) =
        GW.Analysis.realCutoff hw n (GW.Analysis.realMultiplier (H := H) w μ u) := by
  rw [GW.Analysis.realCutoff_action]
  apply Lp.ext
  filter_upwards [GW.Analysis.realMultiplier_ae w (weightCutoffInput hw n u),
    GW.Analysis.realCutoff_ae hw n (u : Lp H 2 μ),
    GW.Analysis.truncatedReal_ae hw n (u : Lp H 2 μ)] with x hm hc ht
  rw [← hm]
  change (w x : ℂ) • (GW.Analysis.realCutoff hw n (u : Lp H 2 μ)) x = _
  rw [← hc,← ht]
  by_cases hx : x ∈ GW.Analysis.realCutoffSet w n <;> simp [hx]

def restrictedDomainCutoff {S : ClosedSubmodule ℂ (Lp H 2 μ)} {hw : Measurable w}
    {hw1 : ∀ x, 1 ≤ w x} (h : WeightInvariant S hw hw1) (n : ℕ)
    (u : restrictedWeightDomain S w) : restrictedWeightDomain S w :=
  ⟨⟨GW.Analysis.realCutoff hw (n+1) ((u : S) : Lp H 2 μ),
    h.cutoff (n+1) (Nat.succ_le_succ (Nat.zero_le n)) (u : S)⟩,
    GW.Analysis.realCutoff_mem_domain hw (n+1) ((u : S) : Lp H 2 μ)⟩

def restrictedAmbientCoordinates (S : ClosedSubmodule ℂ (Lp H 2 μ)) (w : X → ℝ) :
    RestrictedWeightedCarrier S w →ₗᵢ[ℂ] Lp H 2 μ :=
  S.toSubmodule.subtypeₗᵢ.comp (restrictedCoordinates S w).toLinearIsometry

lemma restricted_weighted_cutoff_tendsto {S : ClosedSubmodule ℂ (Lp H 2 μ)} {hw : Measurable w}
    {hw1 : ∀ x, 1 ≤ w x} (h : WeightInvariant S hw hw1) (u : restrictedWeightDomain S w) :
    Tendsto (fun n => restrictedCarrierProduct h (restrictedDomainCutoff h n u)) atTop
      (𝓝 (restrictedCarrierProduct h u)) := by
  apply (restrictedAmbientCoordinates S w).isometry.tendsto_nhds_iff.mpr
  have he (n : ℕ) : restrictedAmbientCoordinates S w
      (restrictedCarrierProduct h (restrictedDomainCutoff h n u)) =
      GW.Analysis.realCutoff hw (n+1)
        (GW.Analysis.realMultiplier (H := H) w μ (restrictedWeightInput S w u)) := by
    change GW.Analysis.realMultiplier (H := H) w μ
      (weightCutoffInput hw (n+1) (restrictedWeightInput S w u)) = _
    exact realCutoff_weighted_product hw (n+1) (restrictedWeightInput S w u)
  have ht := (GW.Analysis.realCutoff_tendsto hw
    (GW.Analysis.realMultiplier (H := H) w μ (restrictedWeightInput S w u))).comp (tendsto_add_atTop_nat 1)
  have hlim : restrictedAmbientCoordinates S w (restrictedCarrierProduct h u) =
      GW.Analysis.realMultiplier (H := H) w μ (restrictedWeightInput S w u) := rfl
  simpa only [Function.comp_def,he,hlim] using ht

def restrictedWeightedGraph {S : ClosedSubmodule ℂ (Lp H 2 μ)} {hw : Measurable w}
    {hw1 : ∀ x, 1 ≤ w x} (h : WeightInvariant S hw hw1) :
    WeightedGraph S (RestrictedWeightedCarrier S w) where
  domain := restrictedWeightDomain S w
  embedding := restrictedWeightEmbedding h
  embedding_injective := restrictedWeightEmbedding_injective h
  embedding_norm_le := restrictedWeightEmbedding_norm h
  embedding_dense := restrictedWeightEmbedding_dense h
  product := restrictedCarrierProduct h
  embedding_mem := restrictedWeightEmbedding_mem h
  product_embedding := restricted_product_embedding h
  embedding_product := restricted_embedding_product h

lemma reciprocalMap_opNorm (hw : Measurable w) (hw1 : ∀ x, 1 ≤ w x) :
    ‖reciprocalMap (H := H) (μ := μ) hw hw1‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa only [one_mul] using reciprocalMap_norm_le hw hw1 u

lemma weightCutoff_norm (hw : Measurable w) (n : ℕ) (u : Lp H 2 μ) :
    ‖GW.Analysis.realCutoff hw n u‖ ≤ ‖u‖ := by
  have hb : ‖GW.Analysis.realCutoff hw n u‖ ≤ 1*‖u‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [GW.Analysis.realCutoff_ae hw n u] with x hx
    rw [← hx,one_mul]
    exact norm_indicator_le_norm_self _ _
  simpa only [one_mul] using hb

lemma weightCutoff_opNorm (hw : Measurable w) (n : ℕ) :
    ‖GW.Analysis.realCutoff (H := H) (μ := μ) hw n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa only [one_mul] using weightCutoff_norm hw n u

lemma weightTruncated_opNorm (hw : Measurable w) (n : ℕ) :
    ‖GW.Analysis.truncatedReal (H := H) (μ := μ) hw n‖ ≤ (n : ℝ) :=
  GW.Analysis.boundedMultiplier_opNorm_le _ _ (Nat.cast_nonneg n) _

lemma weightCutoff_product_ae (hw : Measurable w) (n : ℕ) (u : Lp H 2 μ) :
    (fun x => (w x : ℂ) • GW.Analysis.realCutoff hw n u x) =ᵐ[μ] GW.Analysis.truncatedReal hw n u := by
  filter_upwards [GW.Analysis.realCutoff_ae hw n u,GW.Analysis.truncatedReal_ae hw n u] with x hc hb
  rw [← hc,← hb]
  by_cases hx : x ∈ GW.Analysis.realCutoffSet w n <;> simp [hx]

lemma reciprocalMap_weighted_ae (hw : Measurable w) (hw1 : ∀ x, 1 ≤ w x) (u : Lp H 2 μ) :
    (fun x => (w x : ℂ) • reciprocalMap hw hw1 u x) =ᵐ[μ] u := by
  have h := WeightedL2.weighted_embed_ae hw hw1
    ((WeightedL2.coordinates (H := H) (w := w) (μ := μ)).symm u)
  rw [← reciprocalMap_apply hw hw1 u,LinearIsometryEquiv.apply_symm_apply] at h
  exact h

section Diagonal
variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℂ (E n)]

lemma diagonal_mem (T : ∀ n, E n →L[ℂ] E n) {c : ℝ} (hT : ∀ n, ‖T n‖ ≤ c) (u : lp E 2) :
    Memℓp (fun n => T n (u n)) 2 := by
  have hu := (GW.Analysis.memℓp_two_iff_sq _).mp u.property
  have hb : Summable (fun n => (c*‖u n‖) ^ 2) := by
    simpa only [mul_pow] using hu.mul_left (c ^ 2)
  apply GW.Analysis.dominated_memℓp hb
  intro n
  exact ((T n).le_opNorm (u n)).trans (mul_le_mul_of_nonneg_right (hT n) (norm_nonneg _))

def diagonalLinear (T : ∀ n, E n →L[ℂ] E n) {c : ℝ} (hT : ∀ n, ‖T n‖ ≤ c) :
    lp E 2 →ₗ[ℂ] lp E 2 where
  toFun u := ⟨(fun n => T n (u n)),diagonal_mem T hT u⟩
  map_add' u v := by apply lp.ext; funext n; exact (T n).map_add (u n) (v n)
  map_smul' r u := by apply lp.ext; funext n; exact (T n).map_smul r (u n)

lemma diagonal_norm_bound (T : ∀ n, E n →L[ℂ] E n) {c : ℝ} (hc : 0 ≤ c)
    (hT : ∀ n, ‖T n‖ ≤ c) (u : lp E 2) : ‖diagonalLinear T hT u‖ ≤ c*‖u‖ := by
  have hb : ∀ n, ‖diagonalLinear T hT u n‖ ≤ ‖((c : ℂ) • u) n‖ := by
    intro n
    change ‖T n (u n)‖ ≤ ‖(c : ℂ) • u n‖
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc]
    exact ((T n).le_opNorm (u n)).trans (mul_le_mul_of_nonneg_right (hT n) (norm_nonneg _))
  calc
    _ ≤ ‖(c : ℂ) • u‖ := lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0) hb
    _ = _ := by rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc]

/-- The diagonal map never coerces different fibers to a single value space. -/
def diagonalMap (T : ∀ n, E n →L[ℂ] E n) {c : ℝ} (hc : 0 ≤ c) (hT : ∀ n, ‖T n‖ ≤ c) :
    lp E 2 →L[ℂ] lp E 2 := (diagonalLinear T hT).mkContinuous c (diagonal_norm_bound T hc hT)

lemma diagonalMap_apply (T : ∀ n, E n →L[ℂ] E n) {c : ℝ} (hc : 0 ≤ c)
    (hT : ∀ n, ‖T n‖ ≤ c) (u : lp E 2) (n : ℕ) : diagonalMap T hc hT u n = T n (u n) := rfl

lemma diagonalMap_opNorm (T : ∀ n, E n →L[ℂ] E n) {c : ℝ} (hc : 0 ≤ c)
    (hT : ∀ n, ‖T n‖ ≤ c) : ‖diagonalMap T hc hT‖ ≤ c :=
  ContinuousLinearMap.opNorm_le_bound _ hc (diagonal_norm_bound T hc hT)

lemma diagonalMap_tendsto (T : ℕ → ∀ n, E n →L[ℂ] E n) (hT : ∀ R n, ‖T R n‖ ≤ 1)
    (ht : ∀ n (u : E n), Tendsto (fun R => T R n u) atTop (𝓝 u)) (u : lp E 2) :
    Tendsto (fun R => diagonalMap (T R) zero_le_one (hT R) u) atTop (𝓝 u) := by
  apply GW.Analysis.dominated_lp_tendsto ((GW.Analysis.memℓp_two_iff_sq _).mp u.property)
  · intro R n
    change ‖T R n (u n)‖ ≤ ‖u n‖
    have hn := mul_le_mul_of_nonneg_right (hT R n) (norm_nonneg (u n))
    exact ((T R n).le_opNorm (u n)).trans (by simpa only [one_mul] using hn)
  · intro n
    exact ht n (u n)
end Diagonal

section CountableWeights
variable {Y F : ℕ → Type*} [∀ n, MeasurableSpace (Y n)]
  [∀ n, NormedAddCommGroup (F n)] [∀ n, InnerProductSpace ℂ (F n)]
  (μ : ∀ n, Measure (Y n)) {w : ∀ n, Y n → ℝ}

abbrev WeightFiber (n : ℕ) : Type _ := Lp (F n) 2 (μ n)
abbrev WeightSum : Type _ := lp (WeightFiber (F := F) μ) 2

def sumReciprocal (hw : ∀ n, Measurable (w n)) (hw1 : ∀ n x, 1 ≤ w n x) :
    WeightSum (F := F) μ →L[ℂ] WeightSum (F := F) μ :=
  diagonalMap (fun n => reciprocalMap (H := F n) (μ := μ n) (hw n) (hw1 n)) zero_le_one
    (fun n => reciprocalMap_opNorm (hw n) (hw1 n))

def sumCutoff (hw : ∀ n, Measurable (w n)) (R : ℕ) :
    WeightSum (F := F) μ →L[ℂ] WeightSum (F := F) μ :=
  diagonalMap (fun n => GW.Analysis.realCutoff (H := F n) (μ := μ n) (hw n) R) zero_le_one
    (fun n => weightCutoff_opNorm (hw n) R)

def sumTruncated (hw : ∀ n, Measurable (w n)) (R : ℕ) :
    WeightSum (F := F) μ →L[ℂ] WeightSum (F := F) μ :=
  diagonalMap (fun n => GW.Analysis.truncatedReal (H := F n) (μ := μ n) (hw n) R)
    (Nat.cast_nonneg R) (fun n => weightTruncated_opNorm (hw n) R)

lemma sumReciprocal_norm (hw : ∀ n, Measurable (w n)) (hw1 : ∀ n x, 1 ≤ w n x) :
    ‖sumReciprocal (F := F) μ hw hw1‖ ≤ 1 := diagonalMap_opNorm _ _ _

lemma sumReciprocal_injective (hw : ∀ n, Measurable (w n)) (hw1 : ∀ n x, 1 ≤ w n x) :
    Function.Injective (sumReciprocal (F := F) μ hw hw1) := by
  intro u v he
  apply lp.ext
  funext n
  apply reciprocalMap_injective (hw n) (hw1 n)
  exact congrArg (fun z : WeightSum (F := F) μ => z n) he

lemma sumCutoff_tendsto (hw : ∀ n, Measurable (w n)) (u : WeightSum (F := F) μ) :
    Tendsto (fun R => sumCutoff (F := F) μ hw R u) atTop (𝓝 u) :=
  diagonalMap_tendsto
    (fun R n => GW.Analysis.realCutoff (H := F n) (μ := μ n) (hw n) R)
    (fun R n => weightCutoff_opNorm (H := F n) (μ := μ n) (hw n) R)
    (fun n v => GW.Analysis.realCutoff_tendsto (hw n) v) u

/-- The actual joint product domain: a square-summable output with every component's a.e. formula. -/
def sumWeightDomain (w : ∀ n, Y n → ℝ) : Submodule ℂ (WeightSum (F := F) μ) where
  carrier := {u | ∃ v : WeightSum (F := F) μ,
    ∀ n, (fun x => (w n x : ℂ) • u n x) =ᵐ[μ n] v n}
  zero_mem' := by
    refine ⟨0,fun n => ?_⟩
    filter_upwards [Lp.coeFn_zero (E := F n) (p := 2) (μ := μ n)] with x hx
    change (w n x : ℂ) • (0 : Lp (F n) 2 (μ n)) x = (0 : Lp (F n) 2 (μ n)) x
    rw [hx]
    simp
  add_mem' := by
    rintro u v ⟨u',hu⟩ ⟨v',hv⟩
    refine ⟨u'+v',fun n => ?_⟩
    filter_upwards [Lp.coeFn_add (u n) (v n),Lp.coeFn_add (u' n) (v' n),hu n,hv n] with x hin hout hu hv
    change (w n x : ℂ) • (u n+v n) x = (u' n+v' n) x
    simp only [Pi.add_apply] at hin hout
    rw [hin,smul_add,hu,hv,hout]
  smul_mem' := by
    rintro c u ⟨v,hv⟩
    refine ⟨c • v,fun n => ?_⟩
    filter_upwards [Lp.coeFn_smul c (u n),Lp.coeFn_smul c (v n),hv n] with x hin hout hv
    change (w n x : ℂ) • (c • u n) x = (c • v n) x
    simp only [Pi.smul_apply] at hin hout
    rw [hin,smul_comm,hv,hout]

def sumWeightValue (u : sumWeightDomain (F := F) μ w) : WeightSum (F := F) μ := Classical.choose u.property

lemma sumWeightValue_ae (u : sumWeightDomain (F := F) μ w) (n : ℕ) :
    (fun x => (w n x : ℂ) • (u : WeightSum (F := F) μ) n x) =ᵐ[μ n] sumWeightValue (F := F) μ u n :=
  Classical.choose_spec u.property n

lemma sumReciprocal_mem (hw : ∀ n, Measurable (w n)) (hw1 : ∀ n x, 1 ≤ w n x)
    (f : WeightSum (F := F) μ) : sumReciprocal (F := F) μ hw hw1 f ∈ sumWeightDomain (F := F) μ w :=
  ⟨f,fun n => reciprocalMap_weighted_ae (hw n) (hw1 n) (f n)⟩

lemma sumReciprocal_value (hw : ∀ n, Measurable (w n)) (hw1 : ∀ n x, 1 ≤ w n x)
    (u : sumWeightDomain (F := F) μ w) : sumReciprocal (F := F) μ hw hw1 (sumWeightValue (F := F) μ u) = (u : WeightSum (F := F) μ) := by
  apply lp.ext
  funext n
  let x : (GW.Analysis.realMultiplier (H := F n) (w n) (μ n)).domain :=
    ⟨(u : WeightSum (F := F) μ) n,⟨sumWeightValue (F := F) μ u n,sumWeightValue_ae (F := F) μ u n⟩⟩
  have he : GW.Analysis.realMultiplier (H := F n) (w n) (μ n) x = sumWeightValue (F := F) μ u n := by
    apply Lp.ext
    exact (GW.Analysis.realMultiplier_ae (w n) x).symm.trans (sumWeightValue_ae (F := F) μ u n)
  change reciprocalMap (hw n) (hw1 n) (sumWeightValue (F := F) μ u n) = (x : Lp (F n) 2 (μ n))
  rw [← he]
  exact reciprocalMap_inverse (hw n) (hw1 n) x

def sumWeightProduct (hw : ∀ n, Measurable (w n)) (hw1 : ∀ n x, 1 ≤ w n x) :
    sumWeightDomain (F := F) μ w →ₗ[ℂ] WeightSum (F := F) μ where
  toFun := sumWeightValue (F := F) μ
  map_add' u v := by
    apply sumReciprocal_injective (F := F) μ hw hw1
    simp only [sumReciprocal_value,map_add]
    rfl
  map_smul' c u := by
    apply sumReciprocal_injective (F := F) μ hw hw1
    simp only [sumReciprocal_value,map_smul,RingHom.id_apply]
    rfl

lemma sumProduct_reciprocal (hw : ∀ n, Measurable (w n)) (hw1 : ∀ n x, 1 ≤ w n x)
    (f : WeightSum (F := F) μ) :
    sumWeightProduct (F := F) μ hw hw1 ⟨sumReciprocal (F := F) μ hw hw1 f,sumReciprocal_mem (F := F) μ hw hw1 f⟩ = f := by
  apply sumReciprocal_injective (F := F) μ hw hw1
  exact sumReciprocal_value (F := F) μ hw hw1 _

lemma sumReciprocal_range (hw : ∀ n, Measurable (w n)) (hw1 : ∀ n x, 1 ≤ w n x) :
    Set.range (sumReciprocal (F := F) μ hw hw1) = (sumWeightDomain (F := F) μ w : Set (WeightSum (F := F) μ)) := by
  ext u
  constructor
  · rintro ⟨f,rfl⟩
    exact sumReciprocal_mem (F := F) μ hw hw1 f
  · intro hu
    exact ⟨sumWeightValue (F := F) μ ⟨u,hu⟩,sumReciprocal_value (F := F) μ hw hw1 ⟨u,hu⟩⟩

lemma sumCutoff_mem (hw : ∀ n, Measurable (w n)) (R : ℕ) (u : WeightSum (F := F) μ) :
    sumCutoff (F := F) μ hw R u ∈ sumWeightDomain (F := F) μ w :=
  ⟨sumTruncated (F := F) μ hw R u,fun n => weightCutoff_product_ae (hw n) R (u n)⟩

lemma sumCutoff_product (hw : ∀ n, Measurable (w n)) (hw1 : ∀ n x, 1 ≤ w n x)
    (R : ℕ) (u : sumWeightDomain (F := F) μ w) :
    sumWeightProduct (F := F) μ hw hw1 ⟨sumCutoff (F := F) μ hw R (u : WeightSum (F := F) μ),sumCutoff_mem (F := F) μ hw R u⟩ =
      sumCutoff (F := F) μ hw R (sumWeightProduct (F := F) μ hw hw1 u) := by
  apply lp.ext
  funext n
  apply Lp.ext
  filter_upwards [sumWeightValue_ae (F := F) μ ⟨sumCutoff (F := F) μ hw R u,sumCutoff_mem (F := F) μ hw R u⟩ n,
    GW.Analysis.realCutoff_ae (hw n) R ((u : WeightSum (F := F) μ) n),sumWeightValue_ae (F := F) μ u n,
    GW.Analysis.realCutoff_ae (hw n) R (sumWeightValue (F := F) μ u n)] with x hv hc hu hp
  change sumWeightValue (F := F) μ ⟨sumCutoff (F := F) μ hw R u,sumCutoff_mem (F := F) μ hw R u⟩ n x =
    GW.Analysis.realCutoff (hw n) R (sumWeightValue (F := F) μ u n) x
  rw [← hv]
  change (w n x : ℂ) • GW.Analysis.realCutoff (hw n) R ((u : WeightSum (F := F) μ) n) x = _
  rw [← hc,← hp]
  by_cases hx : x ∈ GW.Analysis.realCutoffSet (w n) R
  · simpa only [Set.indicator_of_mem hx] using hu
  · simp only [Set.indicator_of_notMem hx,smul_zero]
end CountableWeights

section CountableSubspaces
variable {Y F : ℕ → Type*} [∀ n, MeasurableSpace (Y n)]
  [∀ n, NormedAddCommGroup (F n)] [∀ n, InnerProductSpace ℂ (F n)]
  (μ : ∀ n, Measure (Y n)) {w : ∀ n, Y n → ℝ}

lemma sumCutoff_value_truncated (hw : ∀ n, Measurable (w n)) (R : ℕ) (u : WeightSum (F := F) μ) :
    sumWeightValue (F := F) μ ⟨sumCutoff (F := F) μ hw R u,sumCutoff_mem (F := F) μ hw R u⟩ = sumTruncated (F := F) μ hw R u := by
  apply lp.ext
  funext n
  apply Lp.ext
  exact (sumWeightValue_ae (F := F) μ ⟨sumCutoff (F := F) μ hw R u,sumCutoff_mem (F := F) μ hw R u⟩ n).symm.trans
    (weightCutoff_product_ae (hw n) R (u n))

structure SumWeightInvariant (S : ClosedSubmodule ℂ (WeightSum (F := F) μ))
    (hw : ∀ n, Measurable (w n)) (hw1 : ∀ n x, 1 ≤ w n x) : Prop where
  reciprocal : ∀ u : S, sumReciprocal (F := F) μ hw hw1 (u : WeightSum (F := F) μ) ∈ S
  cutoff : ∀ R : ℕ, 1 ≤ R → ∀ u : S, sumCutoff (F := F) μ hw R (u : WeightSum (F := F) μ) ∈ S
  truncated : ∀ R : ℕ, 1 ≤ R → ∀ u : S, sumTruncated (F := F) μ hw R (u : WeightSum (F := F) μ) ∈ S

lemma sum_invariant_product_mem {S : ClosedSubmodule ℂ (WeightSum (F := F) μ)}
    {hw : ∀ n, Measurable (w n)} {hw1 : ∀ n x, 1 ≤ w n x} (h : SumWeightInvariant (F := F) μ S hw hw1)
    (u : sumWeightDomain (F := F) μ w) (hu : (u : WeightSum (F := F) μ) ∈ S) : sumWeightValue (F := F) μ u ∈ S := by
  have hs (R : ℕ) : sumCutoff (F := F) μ hw (R+1) (sumWeightValue (F := F) μ u) ∈ S := by
    have he : sumCutoff (F := F) μ hw (R+1) (sumWeightValue (F := F) μ u) = sumTruncated (F := F) μ hw (R+1) (u : WeightSum (F := F) μ) :=
      (sumCutoff_product (F := F) μ hw hw1 (R+1) u).symm.trans
        (sumCutoff_value_truncated (F := F) μ hw (R+1) (u : WeightSum (F := F) μ))
    rw [he]
    exact h.truncated (R+1) (Nat.succ_le_succ (Nat.zero_le R)) ⟨u,hu⟩
  exact S.isClosed.mem_of_tendsto
    ((sumCutoff_tendsto (F := F) μ hw (sumWeightValue (F := F) μ u)).comp (tendsto_add_atTop_nat 1))
    (Eventually.of_forall hs)

def sumRestrictedDomain (S : ClosedSubmodule ℂ (WeightSum (F := F) μ)) (w : ∀ n, Y n → ℝ) : Submodule ℂ S :=
  (sumWeightDomain (F := F) μ w).comap S.toSubmodule.subtype

def sumRestrictedInput (S : ClosedSubmodule ℂ (WeightSum (F := F) μ)) (w : ∀ n, Y n → ℝ) :
    sumRestrictedDomain (F := F) μ S w →ₗ[ℂ] sumWeightDomain (F := F) μ w where
  toFun u := ⟨(u : S),u.property⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

def sumRestrictedProduct {S : ClosedSubmodule ℂ (WeightSum (F := F) μ)}
    {hw : ∀ n, Measurable (w n)} {hw1 : ∀ n x, 1 ≤ w n x} (h : SumWeightInvariant (F := F) μ S hw hw1) :
    sumRestrictedDomain (F := F) μ S w →ₗ[ℂ] S :=
  ((sumWeightProduct (F := F) μ hw hw1).comp (sumRestrictedInput (F := F) μ S w)).codRestrict S.toSubmodule
    (fun u => sum_invariant_product_mem (F := F) μ h (sumRestrictedInput (F := F) μ S w u) (u : S).property)

def SumWeightedCarrier (S : ClosedSubmodule ℂ (WeightSum (F := F) μ)) (_w : ∀ n, Y n → ℝ) : Type _ := S

instance sumCarrierNormedAddCommGroup (S : ClosedSubmodule ℂ (WeightSum (F := F) μ)) :
    NormedAddCommGroup (SumWeightedCarrier (F := F) μ S w) := inferInstanceAs (NormedAddCommGroup S)
instance sumCarrierNormedSpace (S : ClosedSubmodule ℂ (WeightSum (F := F) μ)) :
    NormedSpace ℂ (SumWeightedCarrier (F := F) μ S w) := inferInstanceAs (NormedSpace ℂ S)
instance sumCarrierInnerProductSpace (S : ClosedSubmodule ℂ (WeightSum (F := F) μ)) :
    InnerProductSpace ℂ (SumWeightedCarrier (F := F) μ S w) := inferInstanceAs (InnerProductSpace ℂ S)
instance sumCarrierCompleteSpace (S : ClosedSubmodule ℂ (WeightSum (F := F) μ)) [∀ n, CompleteSpace (F n)] :
    CompleteSpace (SumWeightedCarrier (F := F) μ S w) := inferInstanceAs (CompleteSpace S)

def sumRestrictedCoordinates (S : ClosedSubmodule ℂ (WeightSum (F := F) μ)) (w : ∀ n, Y n → ℝ) :
    SumWeightedCarrier (F := F) μ S w ≃ₗᵢ[ℂ] S := LinearIsometryEquiv.refl ℂ S

def sumRestrictedReciprocal {S : ClosedSubmodule ℂ (WeightSum (F := F) μ)}
    {hw : ∀ n, Measurable (w n)} {hw1 : ∀ n x, 1 ≤ w n x} (h : SumWeightInvariant (F := F) μ S hw hw1) : S →L[ℂ] S :=
  ((sumReciprocal (F := F) μ hw hw1).comp S.toSubmodule.subtypeL).codRestrict S.toSubmodule h.reciprocal

def sumRestrictedEmbedding {S : ClosedSubmodule ℂ (WeightSum (F := F) μ)}
    {hw : ∀ n, Measurable (w n)} {hw1 : ∀ n x, 1 ≤ w n x} (h : SumWeightInvariant (F := F) μ S hw hw1) :
    SumWeightedCarrier (F := F) μ S w →L[ℂ] S :=
  (sumRestrictedReciprocal (F := F) μ h).comp (sumRestrictedCoordinates (F := F) μ S w).toLinearIsometry.toContinuousLinearMap

lemma sumRestrictedEmbedding_norm {S : ClosedSubmodule ℂ (WeightSum (F := F) μ)}
    {hw : ∀ n, Measurable (w n)} {hw1 : ∀ n x, 1 ≤ w n x} (h : SumWeightInvariant (F := F) μ S hw hw1) :
    ‖sumRestrictedEmbedding (F := F) μ h‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖sumReciprocal (F := F) μ hw hw1 ((sumRestrictedCoordinates (F := F) μ S w f : S) : WeightSum (F := F) μ)‖ ≤ 1*‖f‖
  rw [one_mul]
  calc
    _ ≤ ‖sumReciprocal (F := F) μ hw hw1‖*‖((sumRestrictedCoordinates (F := F) μ S w f : S) : WeightSum (F := F) μ)‖ :=
      (sumReciprocal (F := F) μ hw hw1).le_opNorm _
    _ ≤ 1*‖((sumRestrictedCoordinates (F := F) μ S w f : S) : WeightSum (F := F) μ)‖ :=
      mul_le_mul_of_nonneg_right (sumReciprocal_norm (F := F) μ hw hw1) (norm_nonneg _)
    _ = _ := by rw [one_mul]; exact (sumRestrictedCoordinates (F := F) μ S w).norm_map f

lemma sumRestrictedEmbedding_injective {S : ClosedSubmodule ℂ (WeightSum (F := F) μ)}
    {hw : ∀ n, Measurable (w n)} {hw1 : ∀ n x, 1 ≤ w n x} (h : SumWeightInvariant (F := F) μ S hw hw1) :
    Function.Injective (sumRestrictedEmbedding (F := F) μ h) := by
  intro f g he
  apply (sumRestrictedCoordinates (F := F) μ S w).injective
  apply Subtype.ext
  apply sumReciprocal_injective (F := F) μ hw hw1
  exact congrArg (fun u : S => (u : WeightSum (F := F) μ)) he

lemma sumRestrictedEmbedding_mem {S : ClosedSubmodule ℂ (WeightSum (F := F) μ)}
    {hw : ∀ n, Measurable (w n)} {hw1 : ∀ n x, 1 ≤ w n x} (h : SumWeightInvariant (F := F) μ S hw hw1)
    (f : SumWeightedCarrier (F := F) μ S w) : sumRestrictedEmbedding (F := F) μ h f ∈ sumRestrictedDomain (F := F) μ S w :=
  sumReciprocal_mem (F := F) μ hw hw1 _

def sumRestrictedCarrierProduct {S : ClosedSubmodule ℂ (WeightSum (F := F) μ)}
    {hw : ∀ n, Measurable (w n)} {hw1 : ∀ n x, 1 ≤ w n x} (h : SumWeightInvariant (F := F) μ S hw hw1) :
    sumRestrictedDomain (F := F) μ S w →ₗ[ℂ] SumWeightedCarrier (F := F) μ S w :=
  (sumRestrictedCoordinates (F := F) μ S w).symm.toLinearMap.comp (sumRestrictedProduct (F := F) μ h)

lemma sum_restricted_product_embedding {S : ClosedSubmodule ℂ (WeightSum (F := F) μ)}
    {hw : ∀ n, Measurable (w n)} {hw1 : ∀ n x, 1 ≤ w n x} (h : SumWeightInvariant (F := F) μ S hw hw1)
    (f : SumWeightedCarrier (F := F) μ S w) : sumRestrictedCarrierProduct (F := F) μ h
      ⟨sumRestrictedEmbedding (F := F) μ h f,sumRestrictedEmbedding_mem (F := F) μ h f⟩ = f := by
  apply (sumRestrictedCoordinates (F := F) μ S w).injective
  apply Subtype.ext
  change sumWeightProduct (F := F) μ hw hw1
    ⟨sumReciprocal (F := F) μ hw hw1 ((sumRestrictedCoordinates (F := F) μ S w f : S) : WeightSum (F := F) μ),_⟩ =
      ((sumRestrictedCoordinates (F := F) μ S w f : S) : WeightSum (F := F) μ)
  exact sumProduct_reciprocal (F := F) μ hw hw1 _

lemma sum_restricted_embedding_product {S : ClosedSubmodule ℂ (WeightSum (F := F) μ)}
    {hw : ∀ n, Measurable (w n)} {hw1 : ∀ n x, 1 ≤ w n x} (h : SumWeightInvariant (F := F) μ S hw hw1)
    (u : sumRestrictedDomain (F := F) μ S w) : sumRestrictedEmbedding (F := F) μ h (sumRestrictedCarrierProduct (F := F) μ h u) = (u : S) := by
  apply Subtype.ext
  change sumReciprocal (F := F) μ hw hw1 (sumWeightProduct (F := F) μ hw hw1 (sumRestrictedInput (F := F) μ S w u)) =
    ((u : S) : WeightSum (F := F) μ)
  exact sumReciprocal_value (F := F) μ hw hw1 _

lemma sumRestrictedEmbedding_range {S : ClosedSubmodule ℂ (WeightSum (F := F) μ)}
    {hw : ∀ n, Measurable (w n)} {hw1 : ∀ n x, 1 ≤ w n x} (h : SumWeightInvariant (F := F) μ S hw hw1) :
    Set.range (sumRestrictedEmbedding (F := F) μ h) = (sumRestrictedDomain (F := F) μ S w : Set S) := by
  ext u
  constructor
  · rintro ⟨f,rfl⟩
    exact sumRestrictedEmbedding_mem (F := F) μ h f
  · intro hu
    exact ⟨sumRestrictedCarrierProduct (F := F) μ h ⟨u,hu⟩,sum_restricted_embedding_product (F := F) μ h ⟨u,hu⟩⟩

lemma sumRestrictedEmbedding_dense {S : ClosedSubmodule ℂ (WeightSum (F := F) μ)}
    {hw : ∀ n, Measurable (w n)} {hw1 : ∀ n x, 1 ≤ w n x} (h : SumWeightInvariant (F := F) μ S hw hw1) :
    DenseRange (sumRestrictedEmbedding (F := F) μ h) := by
  intro u
  let v : ℕ → S := fun R => ⟨sumCutoff (F := F) μ hw (R+1) (u : WeightSum (F := F) μ),
    h.cutoff (R+1) (Nat.succ_le_succ (Nat.zero_le R)) u⟩
  have ht : Tendsto v atTop (𝓝 u) := by
    apply tendsto_subtype_rng.mpr
    exact (sumCutoff_tendsto (F := F) μ hw (u : WeightSum (F := F) μ)).comp (tendsto_add_atTop_nat 1)
  apply mem_closure_of_tendsto ht
  apply Eventually.of_forall
  intro R
  rw [sumRestrictedEmbedding_range]
  exact sumCutoff_mem (F := F) μ hw (R+1) (u : WeightSum (F := F) μ)

def sumRestrictedDomainCutoff {S : ClosedSubmodule ℂ (WeightSum (F := F) μ)}
    {hw : ∀ n, Measurable (w n)} {hw1 : ∀ n x, 1 ≤ w n x} (h : SumWeightInvariant (F := F) μ S hw hw1)
    (R : ℕ) (u : sumRestrictedDomain (F := F) μ S w) : sumRestrictedDomain (F := F) μ S w :=
  ⟨⟨sumCutoff (F := F) μ hw (R+1) ((u : S) : WeightSum (F := F) μ),
    h.cutoff (R+1) (Nat.succ_le_succ (Nat.zero_le R)) (u : S)⟩,
    sumCutoff_mem (F := F) μ hw (R+1) ((u : S) : WeightSum (F := F) μ)⟩

def sumRestrictedAmbientCoordinates (S : ClosedSubmodule ℂ (WeightSum (F := F) μ)) (w : ∀ n, Y n → ℝ) :
    SumWeightedCarrier (F := F) μ S w →ₗᵢ[ℂ] WeightSum (F := F) μ :=
  S.toSubmodule.subtypeₗᵢ.comp (sumRestrictedCoordinates (F := F) μ S w).toLinearIsometry

lemma sum_restricted_weighted_cutoff_tendsto {S : ClosedSubmodule ℂ (WeightSum (F := F) μ)}
    {hw : ∀ n, Measurable (w n)} {hw1 : ∀ n x, 1 ≤ w n x} (h : SumWeightInvariant (F := F) μ S hw hw1)
    (u : sumRestrictedDomain (F := F) μ S w) :
    Tendsto (fun R => sumRestrictedCarrierProduct (F := F) μ h (sumRestrictedDomainCutoff (F := F) μ h R u)) atTop
      (𝓝 (sumRestrictedCarrierProduct (F := F) μ h u)) := by
  apply (sumRestrictedAmbientCoordinates (F := F) μ S w).isometry.tendsto_nhds_iff.mpr
  have he (R : ℕ) : sumRestrictedAmbientCoordinates (F := F) μ S w
      (sumRestrictedCarrierProduct (F := F) μ h (sumRestrictedDomainCutoff (F := F) μ h R u)) =
      sumCutoff (F := F) μ hw (R+1) (sumWeightValue (F := F) μ (sumRestrictedInput (F := F) μ S w u)) := by
    exact sumCutoff_product (F := F) μ hw hw1 (R+1) (sumRestrictedInput (F := F) μ S w u)
  have hlim : sumRestrictedAmbientCoordinates (F := F) μ S w (sumRestrictedCarrierProduct (F := F) μ h u) =
      sumWeightValue (F := F) μ (sumRestrictedInput (F := F) μ S w u) := rfl
  have ht := (sumCutoff_tendsto (F := F) μ hw (sumWeightValue (F := F) μ (sumRestrictedInput (F := F) μ S w u))).comp (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def,he,hlim] using ht

def sumRestrictedWeightedGraph {S : ClosedSubmodule ℂ (WeightSum (F := F) μ)}
    {hw : ∀ n, Measurable (w n)} {hw1 : ∀ n x, 1 ≤ w n x} (h : SumWeightInvariant (F := F) μ S hw hw1) :
    WeightedGraph S (SumWeightedCarrier (F := F) μ S w) where
  domain := sumRestrictedDomain (F := F) μ S w
  embedding := sumRestrictedEmbedding (F := F) μ h
  embedding_injective := sumRestrictedEmbedding_injective (F := F) μ h
  embedding_norm_le := sumRestrictedEmbedding_norm (F := F) μ h
  embedding_dense := sumRestrictedEmbedding_dense (F := F) μ h
  product := sumRestrictedCarrierProduct (F := F) μ h
  embedding_mem := sumRestrictedEmbedding_mem (F := F) μ h
  product_embedding := sum_restricted_product_embedding (F := F) μ h
  embedding_product := sum_restricted_embedding_product (F := F) μ h
end CountableSubspaces

def reciprocalWeightFunction (t : ℝ) : ℂ := (((max 1 t)⁻¹ : ℝ) : ℂ)
def cutoffWeightFunction (n : ℕ) : ℝ → ℂ := {t | t ≤ (n : ℝ)}.indicator (fun _ => 1)
def truncatedWeightFunction (n : ℕ) : ℝ → ℂ :=
  {t | 1 ≤ t ∧ t ≤ (n : ℝ)}.indicator (fun t => (t : ℂ))

lemma reciprocalWeightFunction_measurable : Measurable reciprocalWeightFunction :=
  Complex.continuous_ofReal.measurable.comp ((measurable_const.max measurable_id).inv)

lemma cutoffWeightFunction_measurable (n : ℕ) : Measurable (cutoffWeightFunction n) :=
  measurable_const.indicator (measurableSet_le measurable_id measurable_const)

lemma truncatedWeightFunction_measurable (n : ℕ) : Measurable (truncatedWeightFunction n) :=
  Complex.continuous_ofReal.measurable.indicator
    ((measurableSet_le measurable_const measurable_id).inter (measurableSet_le measurable_id measurable_const))

lemma reciprocalWeightFunction_bound (t : ℝ) : ‖reciprocalWeightFunction t‖ ≤ 1 := by
  have ht : 1 ≤ max 1 t := le_max_left _ _
  rw [reciprocalWeightFunction,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (zero_le_one.trans ht))]
  exact inv_le_one_of_one_le₀ ht

lemma cutoffWeightFunction_bound (n : ℕ) (t : ℝ) : ‖cutoffWeightFunction n t‖ ≤ 1 := by
  by_cases ht : t ≤ (n : ℝ) <;> simp [cutoffWeightFunction,ht]

lemma truncatedWeightFunction_bound (n : ℕ) (t : ℝ) : ‖truncatedWeightFunction n t‖ ≤ (n : ℝ) := by
  by_cases ht : 1 ≤ t ∧ t ≤ (n : ℝ)
  · have hm : t ∈ {t : ℝ | 1 ≤ t ∧ t ≤ (n : ℝ)} := ht
    simpa only [truncatedWeightFunction,Set.indicator_of_mem hm,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (zero_le_one.trans ht.1)] using ht.2
  · have hm : t ∉ {t : ℝ | 1 ≤ t ∧ t ≤ (n : ℝ)} := ht
    simp only [truncatedWeightFunction,Set.indicator_of_notMem hm,norm_zero]
    exact Nat.cast_nonneg n

section FunctionalInvariance
variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {μ : Measure X} {w : X → ℝ}

lemma boundedMultiplier_coeff_congr {a b : X → ℂ} {ha : Measurable a} {hb : Measurable b}
    {c d : ℝ} {hca : ∀ᵐ x ∂μ, ‖a x‖ ≤ c} {hcb : ∀ᵐ x ∂μ, ‖b x‖ ≤ d}
    (he : a =ᵐ[μ] b) (u : Lp H 2 μ) :
    GW.Analysis.boundedMultiplier a ha hca u = GW.Analysis.boundedMultiplier b hb hcb u := by
  apply Lp.ext
  filter_upwards [GW.Analysis.boundedMultiplier_ae a ha hca u,
    GW.Analysis.boundedMultiplier_ae b hb hcb u,he] with x ha hb he
  rw [← ha,← hb,he]

/-- Invariance under every bounded Borel function of the given weight. -/
def FunctionalWeightInvariant (S : ClosedSubmodule ℂ (Lp H 2 μ)) (hw : Measurable w) : Prop :=
  ∀ (a : ℝ → ℂ) (ha : Measurable a) {c : ℝ} (hc : ∀ t, ‖a t‖ ≤ c) (u : S),
    GW.Analysis.boundedMultiplier (a ∘ w) (ha.comp hw)
      (Eventually.of_forall (fun x => hc (w x))) (u : Lp H 2 μ) ∈ S

lemma weightInvariant_of_functional {S : ClosedSubmodule ℂ (Lp H 2 μ)} {hw : Measurable w}
    (hw1 : ∀ x, 1 ≤ w x) (h : FunctionalWeightInvariant S hw) : WeightInvariant S hw hw1 := by
  constructor
  · intro u
    have hs := h reciprocalWeightFunction reciprocalWeightFunction_measurable reciprocalWeightFunction_bound u
    have he : reciprocalMap hw hw1 (u : Lp H 2 μ) =
        GW.Analysis.boundedMultiplier (reciprocalWeightFunction ∘ w)
          (reciprocalWeightFunction_measurable.comp hw)
          (Eventually.of_forall (fun x => reciprocalWeightFunction_bound (w x))) (u : Lp H 2 μ) := by
      apply boundedMultiplier_coeff_congr
      exact Eventually.of_forall (fun x => by simp [reciprocalWeightFunction,max_eq_right (hw1 x)])
    rw [he]
    exact hs
  · intro n _hn u
    have hs := h (cutoffWeightFunction n) (cutoffWeightFunction_measurable n) (cutoffWeightFunction_bound n) u
    have he : GW.Analysis.realCutoff hw n (u : Lp H 2 μ) =
        GW.Analysis.boundedMultiplier (cutoffWeightFunction n ∘ w)
          ((cutoffWeightFunction_measurable n).comp hw)
          (Eventually.of_forall (fun x => cutoffWeightFunction_bound n (w x))) (u : Lp H 2 μ) := by
      apply boundedMultiplier_coeff_congr
      exact Eventually.of_forall (fun x => by
        simp [GW.Analysis.realCutoffSet,cutoffWeightFunction,Set.indicator,
          abs_of_nonneg (zero_le_one.trans (hw1 x))])
    rw [he]
    exact hs
  · intro n _hn u
    have hs := h (truncatedWeightFunction n) (truncatedWeightFunction_measurable n) (truncatedWeightFunction_bound n) u
    have he : GW.Analysis.truncatedReal hw n (u : Lp H 2 μ) =
        GW.Analysis.boundedMultiplier (truncatedWeightFunction n ∘ w)
          ((truncatedWeightFunction_measurable n).comp hw)
          (Eventually.of_forall (fun x => truncatedWeightFunction_bound n (w x))) (u : Lp H 2 μ) := by
      apply boundedMultiplier_coeff_congr
      exact Eventually.of_forall (fun x => by
        simp [GW.Analysis.realCutoffSet,truncatedWeightFunction,Set.indicator,hw1 x,
          abs_of_nonneg (zero_le_one.trans (hw1 x))])
    rw [he]
    exact hs
end FunctionalInvariance

section FunctionalSumInvariance
variable {Y F : ℕ → Type*} [∀ n, MeasurableSpace (Y n)]
  [∀ n, NormedAddCommGroup (F n)] [∀ n, InnerProductSpace ℂ (F n)]
  (μ : ∀ n, Measure (Y n)) {w : ∀ n, Y n → ℝ}

def sumFunctionalMap (hw : ∀ n, Measurable (w n)) (a : ℝ → ℂ) (ha : Measurable a)
    {c : ℝ} (hc : ∀ t, ‖a t‖ ≤ c) : WeightSum (F := F) μ →L[ℂ] WeightSum (F := F) μ :=
  diagonalMap (fun n => GW.Analysis.boundedMultiplier (E := F n) (μ := μ n) (a ∘ w n) (ha.comp (hw n))
    (Eventually.of_forall (fun x => hc (w n x)))) ((norm_nonneg (a 0)).trans (hc 0))
    (fun _ => GW.Analysis.boundedMultiplier_opNorm_le _ _ ((norm_nonneg (a 0)).trans (hc 0)) _)

def FunctionalSumWeightInvariant (S : ClosedSubmodule ℂ (WeightSum (F := F) μ))
    (hw : ∀ n, Measurable (w n)) : Prop :=
  ∀ (a : ℝ → ℂ) (ha : Measurable a) {c : ℝ} (hc : ∀ t, ‖a t‖ ≤ c) (u : S),
    sumFunctionalMap (F := F) μ hw a ha hc (u : WeightSum (F := F) μ) ∈ S

lemma sumWeightInvariant_of_functional {S : ClosedSubmodule ℂ (WeightSum (F := F) μ)}
    {hw : ∀ n, Measurable (w n)} (hw1 : ∀ n x, 1 ≤ w n x)
    (h : FunctionalSumWeightInvariant (F := F) μ S hw) : SumWeightInvariant (F := F) μ S hw hw1 := by
  constructor
  · intro u
    have hs := h reciprocalWeightFunction reciprocalWeightFunction_measurable reciprocalWeightFunction_bound u
    have he : sumReciprocal (F := F) μ hw hw1 (u : WeightSum (F := F) μ) =
        sumFunctionalMap (F := F) μ hw reciprocalWeightFunction reciprocalWeightFunction_measurable reciprocalWeightFunction_bound u := by
      apply lp.ext
      funext n
      apply boundedMultiplier_coeff_congr
      exact Eventually.of_forall (fun x => by simp [reciprocalWeightFunction,max_eq_right (hw1 n x)])
    rw [he]
    exact hs
  · intro R _hR u
    have hs := h (cutoffWeightFunction R) (cutoffWeightFunction_measurable R) (cutoffWeightFunction_bound R) u
    have he : sumCutoff (F := F) μ hw R (u : WeightSum (F := F) μ) =
        sumFunctionalMap (F := F) μ hw (cutoffWeightFunction R) (cutoffWeightFunction_measurable R) (cutoffWeightFunction_bound R) u := by
      apply lp.ext
      funext n
      apply boundedMultiplier_coeff_congr
      exact Eventually.of_forall (fun x => by
        simp [GW.Analysis.realCutoffSet,cutoffWeightFunction,Set.indicator,
          abs_of_nonneg (zero_le_one.trans (hw1 n x))])
    rw [he]
    exact hs
  · intro R _hR u
    have hs := h (truncatedWeightFunction R) (truncatedWeightFunction_measurable R) (truncatedWeightFunction_bound R) u
    have he : sumTruncated (F := F) μ hw R (u : WeightSum (F := F) μ) =
        sumFunctionalMap (F := F) μ hw (truncatedWeightFunction R) (truncatedWeightFunction_measurable R) (truncatedWeightFunction_bound R) u := by
      apply lp.ext
      funext n
      apply boundedMultiplier_coeff_congr
      exact Eventually.of_forall (fun x => by
        simp [GW.Analysis.realCutoffSet,truncatedWeightFunction,Set.indicator,hw1 n x,
          abs_of_nonneg (zero_le_one.trans (hw1 n x))])
    rw [he]
    exact hs

lemma sumWeightDomain_mem_iff (u : WeightSum (F := F) μ) :
    u ∈ sumWeightDomain (F := F) μ w ↔ ∃ hmem : ∀ n, u n ∈ (GW.Analysis.realMultiplier (H := F n) (w n) (μ n)).domain,
      Summable (fun n => ‖GW.Analysis.realMultiplier (H := F n) (w n) (μ n) ⟨u n,hmem n⟩‖ ^ 2) := by
  constructor
  · rintro ⟨v,hv⟩
    let hm : ∀ n, u n ∈ (GW.Analysis.realMultiplier (H := F n) (w n) (μ n)).domain := fun n => ⟨v n,hv n⟩
    have he (n : ℕ) : GW.Analysis.realMultiplier (H := F n) (w n) (μ n) ⟨u n,hm n⟩ = v n := by
      apply Lp.ext
      exact (GW.Analysis.realMultiplier_ae (w n) ⟨u n,hm n⟩).symm.trans (hv n)
    refine ⟨hm,?_⟩
    simpa only [he] using (GW.Analysis.memℓp_two_iff_sq _).mp v.property
  · rintro ⟨hm,hs⟩
    let v : WeightSum (F := F) μ := GW.Analysis.squareSumVector
      (fun n => GW.Analysis.realMultiplier (H := F n) (w n) (μ n) ⟨u n,hm n⟩) hs
    exact ⟨v,fun n => GW.Analysis.realMultiplier_ae (w n) ⟨u n,hm n⟩⟩

lemma sumWeightProduct_norm_sq (hw : ∀ n, Measurable (w n)) (hw1 : ∀ n x, 1 ≤ w n x)
    (u : sumWeightDomain (F := F) μ w) :
    ‖sumWeightProduct (F := F) μ hw hw1 u‖ ^ 2 = ∑' n, ‖sumWeightValue (F := F) μ u n‖ ^ 2 := GW.Analysis.lp_norm_sq _

end FunctionalSumInvariance

section RealWeightCutoffs
variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {μ : Measure X} {w : X → ℝ}

def realWeightCutoff (hw : Measurable w) (R : ℝ) : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  (WeightedL2.coordinates (H := H) (w := w) (μ := μ)).toLinearIsometry.toContinuousLinearMap.comp
    ((WeightedL2.cutoff {x | w x ≤ R} (measurableSet_le hw measurable_const)).comp
      (WeightedL2.coordinates (H := H) (w := w) (μ := μ)).symm.toLinearIsometry.toContinuousLinearMap)

lemma realWeightCutoff_apply (hw : Measurable w) (R : ℝ) (u : Lp H 2 μ) :
    realWeightCutoff hw R u = WeightedL2.coordinates
      (WeightedL2.cutoff {x | w x ≤ R} (measurableSet_le hw measurable_const)
        ((WeightedL2.coordinates (H := H) (w := w) (μ := μ)).symm u)) := rfl

lemma realWeightCutoff_ae (hw : Measurable w) (R : ℝ) (u : Lp H 2 μ) :
    {x | w x ≤ R}.indicator (u : X → H) =ᵐ[μ] realWeightCutoff hw R u := by
  have h := WeightedL2.cutoff_ae {x | w x ≤ R} (measurableSet_le hw measurable_const)
    ((WeightedL2.coordinates (H := H) (w := w) (μ := μ)).symm u)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h

lemma realWeightCutoff_norm (hw : Measurable w) (R : ℝ) :
    ‖realWeightCutoff (H := H) (μ := μ) hw R‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [realWeightCutoff_ae hw R u] with x hx
  rw [← hx,one_mul]
  exact norm_indicator_le_norm_self _ _

lemma realWeightCutoff_tendsto (hw : Measurable w) (u : Lp H 2 μ) :
    Tendsto (fun R : ℝ => realWeightCutoff hw R u) atTop (𝓝 u) := by
  have ht := WeightedL2.weight_cutoff_tendsto_real hw
    ((WeightedL2.coordinates (H := H) (w := w) (μ := μ)).symm u)
  have hc := ((WeightedL2.coordinates (H := H) (w := w) (μ := μ)).continuous.tendsto _).comp ht
  simpa only [Function.comp_def,realWeightCutoff_apply,LinearIsometryEquiv.apply_symm_apply] using hc

lemma realWeightCutoff_nat (hw : Measurable w) (hw1 : ∀ x, 1 ≤ w x) (R : ℕ) :
    realWeightCutoff (H := H) (μ := μ) hw (R : ℝ) = GW.Analysis.realCutoff hw R := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  apply (realWeightCutoff_ae hw (R : ℝ) u).symm.trans
  simpa only [positive_realCutoffSet hw1 R] using GW.Analysis.realCutoff_ae hw R u
end RealWeightCutoffs

section DiagonalFilters
variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℂ (E n)]
  {ι : Type*} {l : Filter ι}

lemma diagonalMap_tendsto_filter (T : ι → ∀ n, E n →L[ℂ] E n) (hT : ∀ i n, ‖T i n‖ ≤ 1)
    (ht : ∀ n (u : E n), Tendsto (fun i => T i n u) l (𝓝 u)) (u : lp E 2) :
    Tendsto (fun i => diagonalMap (T i) zero_le_one (hT i) u) l (𝓝 u) := by
  have hu := (GW.Analysis.memℓp_two_iff_sq _).mp u.property
  have hb : ∀ i n, ‖T i n (u n)-u n‖ ^ 2 ≤ 4*‖u n‖ ^ 2 := by
    intro i n
    have h1 := ((T i n).le_opNorm (u n)).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (hT i n) (norm_nonneg (u n)))
    have h2 := norm_sub_le (T i n (u n)) (u n)
    nlinarith [norm_nonneg (T i n (u n)-u n),norm_nonneg (u n)]
  have hs := tendsto_tsum_of_dominated_convergence
    (f := fun i n => ‖T i n (u n)-u n‖ ^ 2) (g := fun _ => (0 : ℝ)) (hu.mul_left 4)
    (fun n => by
      have hc : Tendsto (fun _ : ι => u n) l (𝓝 (u n)) := tendsto_const_nhds
      simpa using ((ht n (u n)).sub hc).norm.pow 2)
    (Eventually.of_forall (fun i n => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (‖T i n (u n)-u n‖))] using hb i n))
  have hsq : Tendsto (fun i => ‖diagonalMap (T i) zero_le_one (hT i) u-u‖ ^ 2) l (𝓝 0) := by
    simpa only [GW.Analysis.lp_norm_sq,lp.coeFn_sub,Pi.sub_apply,diagonalMap_apply,tsum_zero] using hs
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using
    Real.continuous_sqrt.continuousAt.tendsto.comp hsq
end DiagonalFilters

section SumRealCutoffs
variable {Y F : ℕ → Type*} [∀ n, MeasurableSpace (Y n)]
  [∀ n, NormedAddCommGroup (F n)] [∀ n, InnerProductSpace ℂ (F n)]
  (μ : ∀ n, Measure (Y n)) {w : ∀ n, Y n → ℝ}

def sumRealCutoff (hw : ∀ n, Measurable (w n)) (R : ℝ) : WeightSum (F := F) μ →L[ℂ] WeightSum (F := F) μ :=
  diagonalMap (fun n => realWeightCutoff (H := F n) (μ := μ n) (hw n) R) zero_le_one
    (fun n => realWeightCutoff_norm (hw n) R)

lemma sumRealCutoff_tendsto (hw : ∀ n, Measurable (w n)) (u : WeightSum (F := F) μ) :
    Tendsto (fun R : ℝ => sumRealCutoff (F := F) μ hw R u) atTop (𝓝 u) :=
  diagonalMap_tendsto_filter (fun R n => realWeightCutoff (H := F n) (μ := μ n) (hw n) R)
    (fun R n => realWeightCutoff_norm (H := F n) (μ := μ n) (hw n) R)
    (fun n v => realWeightCutoff_tendsto (hw n) v) u

lemma sumWeightValue_unique (u : sumWeightDomain (F := F) μ w) (v : WeightSum (F := F) μ)
    (hv : ∀ n, (fun x => (w n x : ℂ) • (u : WeightSum (F := F) μ) n x) =ᵐ[μ n] v n) : sumWeightValue (F := F) μ u = v := by
  apply lp.ext
  funext n
  apply Lp.ext
  exact (sumWeightValue_ae (F := F) μ u n).symm.trans (hv n)

lemma sumRealCutoff_weighted_ae (hw : ∀ n, Measurable (w n)) (R : ℝ) (u : sumWeightDomain (F := F) μ w) (n : ℕ) :
    (fun x => (w n x : ℂ) • sumRealCutoff (F := F) μ hw R (u : WeightSum (F := F) μ) n x) =ᵐ[μ n]
      sumRealCutoff (F := F) μ hw R (sumWeightValue (F := F) μ u) n := by
  filter_upwards [realWeightCutoff_ae (hw n) R ((u : WeightSum (F := F) μ) n),sumWeightValue_ae (F := F) μ u n,
    realWeightCutoff_ae (hw n) R (sumWeightValue (F := F) μ u n)] with x hc hu hp
  change (w n x : ℂ) • realWeightCutoff (hw n) R ((u : WeightSum (F := F) μ) n) x =
    realWeightCutoff (hw n) R (sumWeightValue (F := F) μ u n) x
  rw [← hc,← hp]
  by_cases hx : w n x ≤ R
  · have hm : x ∈ {x | w n x ≤ R} := hx
    simpa only [Set.indicator_of_mem hm] using hu
  · have hm : x ∉ {x | w n x ≤ R} := hx
    simp only [Set.indicator_of_notMem hm,smul_zero]

def sumRealCutoffInput (hw : ∀ n, Measurable (w n)) (R : ℝ) (u : sumWeightDomain (F := F) μ w) : sumWeightDomain (F := F) μ w :=
  ⟨sumRealCutoff (F := F) μ hw R (u : WeightSum (F := F) μ),
    ⟨sumRealCutoff (F := F) μ hw R (sumWeightValue (F := F) μ u),sumRealCutoff_weighted_ae (F := F) μ hw R u⟩⟩

lemma sumRealCutoff_product (hw : ∀ n, Measurable (w n)) (hw1 : ∀ n x, 1 ≤ w n x)
    (R : ℝ) (u : sumWeightDomain (F := F) μ w) :
    sumWeightProduct (F := F) μ hw hw1 (sumRealCutoffInput (F := F) μ hw R u) = sumRealCutoff (F := F) μ hw R (sumWeightProduct (F := F) μ hw hw1 u) :=
  sumWeightValue_unique (F := F) μ _ _ (sumRealCutoff_weighted_ae (F := F) μ hw R u)

lemma sumReal_weighted_cutoff_tendsto (hw : ∀ n, Measurable (w n)) (hw1 : ∀ n x, 1 ≤ w n x)
    (u : sumWeightDomain (F := F) μ w) :
    Tendsto (fun R : ℝ => sumWeightProduct (F := F) μ hw hw1 (sumRealCutoffInput (F := F) μ hw R u)) atTop
      (𝓝 (sumWeightProduct (F := F) μ hw hw1 u)) := by
  have he : sumWeightProduct (F := F) μ hw hw1 u = sumWeightValue (F := F) μ u := rfl
  simpa only [sumRealCutoff_product,he] using sumRealCutoff_tendsto (F := F) μ hw (sumWeightValue (F := F) μ u)
end SumRealCutoffs

section GraphNorms
variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {μ : Measure X}

def multiplierGraphWeight (m : X → ℝ) (x : X) : ℝ := Real.sqrt (1+m x ^ 2)
def multiplierEnergyWeight (m : X → ℝ) (x : X) : ℝ := Real.sqrt (1+m x)

lemma multiplierGraphWeight_measurable {m : X → ℝ} (hm : Measurable m) : Measurable (multiplierGraphWeight m) :=
  (measurable_const.add (hm.pow_const 2)).sqrt
lemma multiplierEnergyWeight_measurable {m : X → ℝ} (hm : Measurable m) : Measurable (multiplierEnergyWeight m) :=
  (measurable_const.add hm).sqrt

omit [MeasurableSpace X] in
lemma multiplierGraphWeight_lower (m : X → ℝ) (x : X) : 1 ≤ multiplierGraphWeight m x := by
  have hs := Real.sq_sqrt (show 0 ≤ 1+m x ^ 2 by nlinarith [sq_nonneg (m x)])
  have hp := Real.sqrt_nonneg (1+m x ^ 2)
  change 1 ≤ Real.sqrt (1+m x ^ 2)
  nlinarith [sq_nonneg (m x)]

omit [MeasurableSpace X] in
lemma multiplierEnergyWeight_lower {m : X → ℝ} (hm0 : ∀ x, 0 ≤ m x) (x : X) :
    1 ≤ multiplierEnergyWeight m x := by
  have hs := Real.sq_sqrt (show 0 ≤ 1+m x by linarith [hm0 x])
  have hp := Real.sqrt_nonneg (1+m x)
  change 1 ≤ Real.sqrt (1+m x)
  nlinarith [hm0 x]

lemma graphWeight_pointwise (m : ℝ) (u : H) :
    ‖(Real.sqrt (1+m ^ 2) : ℂ) • u‖ ^ 2 = ‖u‖ ^ 2+‖(m : ℂ) • u‖ ^ 2 := by
  simp only [norm_smul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    Real.sq_sqrt (show 0 ≤ 1+m ^ 2 by nlinarith [sq_nonneg m])]
  ring

lemma multiplierGraphWeight_mem {m : X → ℝ} (hm : Measurable m)
    (u : (GW.Analysis.realMultiplier (H := H) m μ).domain) :
    (u : Lp H 2 μ) ∈ (GW.Analysis.realMultiplier (H := H) (multiplierGraphWeight m) μ).domain := by
  apply (GW.Analysis.realMultiplier_domain _ _).mpr
  have hmu := (GW.Analysis.realMultiplier_domain m (u : Lp H 2 μ)).mp u.property
  have hiu := (Lp.memLp (u : Lp H 2 μ)).integrable_norm_pow (p := 2) (by norm_num)
  have him := hmu.integrable_norm_pow (p := 2) (by norm_num)
  have he : (fun x => ‖(multiplierGraphWeight m x : ℂ) • (u : Lp H 2 μ) x‖ ^ 2) =ᵐ[μ]
      (fun x => ‖(u : Lp H 2 μ) x‖ ^ 2+‖(m x : ℂ) • (u : Lp H 2 μ) x‖ ^ 2) :=
    Eventually.of_forall (fun x => graphWeight_pointwise (m x) ((u : Lp H 2 μ) x))
  apply (memLp_two_iff_integrable_sq_norm
    ((Complex.continuous_ofReal.measurable.comp (multiplierGraphWeight_measurable hm)).aestronglyMeasurable.smul
      (Lp.memLp (u : Lp H 2 μ)).aestronglyMeasurable)).mpr
  exact (hiu.add him).congr he.symm

lemma multiplierGraphWeight_domain {m : X → ℝ} (hm : Measurable m) :
    (GW.Analysis.realMultiplier (H := H) (multiplierGraphWeight m) μ).domain =
      (GW.Analysis.realMultiplier (H := H) m μ).domain := by
  ext u
  constructor
  · intro hu
    apply (GW.Analysis.realMultiplier_domain _ _).mpr
    have hf := (GW.Analysis.realMultiplier_domain (multiplierGraphWeight m) u).mp hu
    apply hf.of_le_mul (c := 1)
      ((Complex.continuous_ofReal.measurable.comp hm).aestronglyMeasurable.smul (Lp.memLp u).aestronglyMeasurable)
    apply Eventually.of_forall
    intro x
    rw [one_mul]
    apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
    have he : ‖(multiplierGraphWeight m x : ℂ) • u x‖ ^ 2 =
        ‖u x‖ ^ 2+‖(m x : ℂ) • u x‖ ^ 2 := graphWeight_pointwise (m x) (u x)
    change ‖(m x : ℂ) • u x‖*‖(m x : ℂ) • u x‖ ≤
      ‖(multiplierGraphWeight m x : ℂ) • u x‖*‖(multiplierGraphWeight m x : ℂ) • u x‖
    nlinarith [sq_nonneg ‖u x‖]
  · intro hu
    exact multiplierGraphWeight_mem hm ⟨u,hu⟩

def multiplierGraphInput {m : X → ℝ} (hm : Measurable m)
    (u : (GW.Analysis.realMultiplier (H := H) m μ).domain) :
    (GW.Analysis.realMultiplier (H := H) (multiplierGraphWeight m) μ).domain :=
  ⟨u,multiplierGraphWeight_mem hm u⟩

lemma multiplierGraphWeight_norm_sq {m : X → ℝ} (hm : Measurable m)
    (u : (GW.Analysis.realMultiplier (H := H) m μ).domain) :
    ‖GW.Analysis.realMultiplier (multiplierGraphWeight m) μ (multiplierGraphInput hm u)‖ ^ 2 =
      ‖(u : Lp H 2 μ)‖ ^ 2+‖GW.Analysis.realMultiplier m μ u‖ ^ 2 := by
  have hiu := (Lp.memLp (u : Lp H 2 μ)).integrable_norm_pow (p := 2) (by norm_num)
  have him := (Lp.memLp (GW.Analysis.realMultiplier m μ u)).integrable_norm_pow (p := 2) (by norm_num)
  have he : (fun x => ‖GW.Analysis.realMultiplier (multiplierGraphWeight m) μ (multiplierGraphInput hm u) x‖ ^ 2) =ᵐ[μ]
      (fun x => ‖(u : Lp H 2 μ) x‖ ^ 2+‖GW.Analysis.realMultiplier m μ u x‖ ^ 2) := by
    filter_upwards [GW.Analysis.realMultiplier_ae (multiplierGraphWeight m) (multiplierGraphInput hm u),
      GW.Analysis.realMultiplier_ae m u] with x hw hm
    rw [← hw,← hm]
    exact graphWeight_pointwise (m x) ((u : Lp H 2 μ) x)
  calc
    _ = ∫ x, ‖GW.Analysis.realMultiplier (multiplierGraphWeight m) μ (multiplierGraphInput hm u) x‖ ^ 2 ∂μ :=
      GW.Analysis.l2_norm_sq (𝕜 := ℂ) _
    _ = ∫ x, ‖(u : Lp H 2 μ) x‖ ^ 2+‖GW.Analysis.realMultiplier m μ u x‖ ^ 2 ∂μ := integral_congr_ae he
    _ = (∫ x, ‖(u : Lp H 2 μ) x‖ ^ 2 ∂μ)+(∫ x, ‖GW.Analysis.realMultiplier m μ u x‖ ^ 2 ∂μ) := integral_add hiu him
    _ = _ := by rw [← GW.Analysis.l2_norm_sq (𝕜 := ℂ),← GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
lemma energyWeight_pointwise (m : ℝ) (hm0 : 0 ≤ m) (u : H) :
    ‖(Real.sqrt (1+m) : ℂ) • u‖ ^ 2 = ‖u‖ ^ 2+(⟪u,(m : ℂ) • u⟫_ℂ).re := by
  have hi : (⟪u,u⟫_ℂ).re = ‖u‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) u).symm
  simp only [norm_smul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    Real.sq_sqrt (show 0 ≤ 1+m by linarith),inner_smul_right,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,hi]
  ring

lemma multiplierEnergyWeight_mem {m : X → ℝ} (hm : Measurable m) (hm0 : ∀ x, 0 ≤ m x)
    (u : (GW.Analysis.realMultiplier (H := H) m μ).domain) :
    (u : Lp H 2 μ) ∈ (GW.Analysis.realMultiplier (H := H) (multiplierEnergyWeight m) μ).domain := by
  have hiu := (Lp.memLp (u : Lp H 2 μ)).integrable_norm_pow (p := 2) (by norm_num)
  have hip : Integrable (fun x => (⟪(u : Lp H 2 μ) x,GW.Analysis.realMultiplier m μ u x⟫_ℂ).re) μ :=
    (L2.integrable_inner (𝕜 := ℂ) (u : Lp H 2 μ) (GW.Analysis.realMultiplier m μ u)).re
  have he : (fun x => ‖(multiplierEnergyWeight m x : ℂ) • (u : Lp H 2 μ) x‖ ^ 2) =ᵐ[μ]
      (fun x => ‖(u : Lp H 2 μ) x‖ ^ 2+(⟪(u : Lp H 2 μ) x,GW.Analysis.realMultiplier m μ u x⟫_ℂ).re) := by
    filter_upwards [GW.Analysis.realMultiplier_ae m u] with x hm
    rw [← hm]
    exact energyWeight_pointwise (m x) (hm0 x) ((u : Lp H 2 μ) x)
  apply (GW.Analysis.realMultiplier_domain _ _).mpr
  apply (memLp_two_iff_integrable_sq_norm
    ((Complex.continuous_ofReal.measurable.comp (multiplierEnergyWeight_measurable hm)).aestronglyMeasurable.smul
      (Lp.memLp (u : Lp H 2 μ)).aestronglyMeasurable)).mpr
  exact (hiu.add hip).congr he.symm

def multiplierEnergyInput {m : X → ℝ} (hm : Measurable m) (hm0 : ∀ x, 0 ≤ m x)
    (u : (GW.Analysis.realMultiplier (H := H) m μ).domain) :
    (GW.Analysis.realMultiplier (H := H) (multiplierEnergyWeight m) μ).domain :=
  ⟨u,multiplierEnergyWeight_mem hm hm0 u⟩

lemma multiplierEnergyWeight_norm_sq {m : X → ℝ} (hm : Measurable m) (hm0 : ∀ x, 0 ≤ m x)
    (u : (GW.Analysis.realMultiplier (H := H) m μ).domain) :
    ‖GW.Analysis.realMultiplier (multiplierEnergyWeight m) μ (multiplierEnergyInput hm hm0 u)‖ ^ 2 =
      ‖(u : Lp H 2 μ)‖ ^ 2+(⟪(u : Lp H 2 μ),GW.Analysis.realMultiplier m μ u⟫_ℂ).re := by
  have hiu := (Lp.memLp (u : Lp H 2 μ)).integrable_norm_pow (p := 2) (by norm_num)
  have hip : Integrable (fun x => (⟪(u : Lp H 2 μ) x,GW.Analysis.realMultiplier m μ u x⟫_ℂ).re) μ :=
    (L2.integrable_inner (𝕜 := ℂ) (u : Lp H 2 μ) (GW.Analysis.realMultiplier m μ u)).re
  have he : (fun x => ‖GW.Analysis.realMultiplier (multiplierEnergyWeight m) μ (multiplierEnergyInput hm hm0 u) x‖ ^ 2) =ᵐ[μ]
      (fun x => ‖(u : Lp H 2 μ) x‖ ^ 2+(⟪(u : Lp H 2 μ) x,GW.Analysis.realMultiplier m μ u x⟫_ℂ).re) := by
    filter_upwards [GW.Analysis.realMultiplier_ae (multiplierEnergyWeight m) (multiplierEnergyInput hm hm0 u),
      GW.Analysis.realMultiplier_ae m u] with x hw hm
    rw [← hw,← hm]
    exact energyWeight_pointwise (m x) (hm0 x) ((u : Lp H 2 μ) x)
  calc
    _ = ∫ x, ‖GW.Analysis.realMultiplier (multiplierEnergyWeight m) μ (multiplierEnergyInput hm hm0 u) x‖ ^ 2 ∂μ :=
      GW.Analysis.l2_norm_sq (𝕜 := ℂ) _
    _ = ∫ x, ‖(u : Lp H 2 μ) x‖ ^ 2+(⟪(u : Lp H 2 μ) x,GW.Analysis.realMultiplier m μ u x⟫_ℂ).re ∂μ := integral_congr_ae he
    _ = (∫ x, ‖(u : Lp H 2 μ) x‖ ^ 2 ∂μ)+
        (∫ x, (⟪(u : Lp H 2 μ) x,GW.Analysis.realMultiplier m μ u x⟫_ℂ).re ∂μ) := integral_add hiu hip
    _ = _ := by
      rw [← GW.Analysis.l2_norm_sq (𝕜 := ℂ),L2.inner_def]
      exact congrArg (fun r : ℝ => ‖(u : Lp H 2 μ)‖ ^ 2+r)
        (integral_re (L2.integrable_inner (𝕜 := ℂ) (u : Lp H 2 μ) (GW.Analysis.realMultiplier m μ u)))


end GraphNorms

section SumGraphWeights
variable {Y F : ℕ → Type*} [∀ n, MeasurableSpace (Y n)]
  [∀ n, NormedAddCommGroup (F n)] [∀ n, InnerProductSpace ℂ (F n)]
  (μ : ∀ n, Measure (Y n)) {w : ∀ n, Y n → ℝ}

def sumComponentInput (u : sumWeightDomain (F := F) μ w) (n : ℕ) :
    (GW.Analysis.realMultiplier (H := F n) (w n) (μ n)).domain :=
  ⟨(u : WeightSum (F := F) μ) n,⟨sumWeightValue (F := F) μ u n,sumWeightValue_ae (F := F) μ u n⟩⟩

lemma sumComponent_action (u : sumWeightDomain (F := F) μ w) (n : ℕ) :
    GW.Analysis.realMultiplier (H := F n) (w n) (μ n) (sumComponentInput (F := F) μ u n) = sumWeightValue (F := F) μ u n := by
  apply Lp.ext
  exact (GW.Analysis.realMultiplier_ae (w n) (sumComponentInput (F := F) μ u n)).symm.trans (sumWeightValue_ae (F := F) μ u n)

lemma sumGraphWeight_domain (hw : ∀ n, Measurable (w n)) :
    sumWeightDomain (F := F) μ (fun n => multiplierGraphWeight (w n)) = sumWeightDomain (F := F) μ w := by
  ext u
  rw [sumWeightDomain_mem_iff,sumWeightDomain_mem_iff]
  constructor
  · rintro ⟨hg,hs⟩
    have hm (n : ℕ) : u n ∈ (GW.Analysis.realMultiplier (H := F n) (w n) (μ n)).domain := by
      rw [← multiplierGraphWeight_domain (hw n)]
      exact hg n
    refine ⟨hm,Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun n => ?_) hs⟩
    have he : multiplierGraphInput (hw n) ⟨u n,hm n⟩ = ⟨u n,hg n⟩ := Subtype.ext rfl
    have h := multiplierGraphWeight_norm_sq (hw n) ⟨u n,hm n⟩
    rw [he] at h
    nlinarith [sq_nonneg ‖u n‖]
  · rintro ⟨hm,hs⟩
    let hg (n : ℕ) : u n ∈ (GW.Analysis.realMultiplier (H := F n) (multiplierGraphWeight (w n)) (μ n)).domain :=
      multiplierGraphWeight_mem (hw n) ⟨u n,hm n⟩
    have he (n : ℕ) :
        ‖GW.Analysis.realMultiplier (H := F n) (multiplierGraphWeight (w n)) (μ n) ⟨u n,hg n⟩‖ ^ 2 =
          ‖u n‖ ^ 2+‖GW.Analysis.realMultiplier (H := F n) (w n) (μ n) ⟨u n,hm n⟩‖ ^ 2 :=
      multiplierGraphWeight_norm_sq (hw n) ⟨u n,hm n⟩
    refine ⟨hg,?_⟩
    simpa only [he] using ((GW.Analysis.memℓp_two_iff_sq _).mp u.property).add hs

def sumGraphInput (hw : ∀ n, Measurable (w n)) (u : sumWeightDomain (F := F) μ w) :
    sumWeightDomain (F := F) μ (fun n => multiplierGraphWeight (w n)) :=
  ⟨u,by rw [sumGraphWeight_domain (F := F) μ hw]; exact u.property⟩

lemma sumGraphWeight_norm_sq (hw : ∀ n, Measurable (w n)) (u : sumWeightDomain (F := F) μ w) :
    ‖sumWeightValue (F := F) μ (sumGraphInput (F := F) μ hw u)‖ ^ 2 =
      ‖(u : WeightSum (F := F) μ)‖ ^ 2+‖sumWeightValue (F := F) μ u‖ ^ 2 := by
  have he (n : ℕ) : ‖sumWeightValue (F := F) μ (sumGraphInput (F := F) μ hw u) n‖ ^ 2 =
      ‖(u : WeightSum (F := F) μ) n‖ ^ 2+‖sumWeightValue (F := F) μ u n‖ ^ 2 := by
    have hi : sumComponentInput (F := F) μ (sumGraphInput (F := F) μ hw u) n =
        multiplierGraphInput (hw n) (sumComponentInput (F := F) μ u n) := Subtype.ext rfl
    rw [← sumComponent_action,hi,multiplierGraphWeight_norm_sq,sumComponent_action]
    rfl
  have hu := (GW.Analysis.memℓp_two_iff_sq _).mp (u : WeightSum (F := F) μ).property
  have hv := (GW.Analysis.memℓp_two_iff_sq _).mp (sumWeightValue (F := F) μ u).property
  calc
    _ = ∑' n, ‖sumWeightValue (F := F) μ (sumGraphInput (F := F) μ hw u) n‖ ^ 2 := GW.Analysis.lp_norm_sq _
    _ = ∑' n, (‖(u : WeightSum (F := F) μ) n‖ ^ 2+‖sumWeightValue (F := F) μ u n‖ ^ 2) := tsum_congr he
    _ = (∑' n, ‖(u : WeightSum (F := F) μ) n‖ ^ 2)+(∑' n, ‖sumWeightValue (F := F) μ u n‖ ^ 2) := hu.tsum_add hv
    _ = _ := by rw [← GW.Analysis.lp_norm_sq,← GW.Analysis.lp_norm_sq]

lemma sumEnergyWeight_mem (hw : ∀ n, Measurable (w n)) (hw0 : ∀ n x, 0 ≤ w n x)
    (u : sumWeightDomain (F := F) μ w) :
    (u : WeightSum (F := F) μ) ∈ sumWeightDomain (F := F) μ (fun n => multiplierEnergyWeight (w n)) := by
  apply (sumWeightDomain_mem_iff (F := F) μ (u : WeightSum (F := F) μ)).mpr
  let he (n : ℕ) : (u : WeightSum (F := F) μ) n ∈
      (GW.Analysis.realMultiplier (H := F n) (multiplierEnergyWeight (w n)) (μ n)).domain :=
    multiplierEnergyWeight_mem (hw n) (hw0 n) (sumComponentInput (F := F) μ u n)
  have hn (n : ℕ) :
      ‖GW.Analysis.realMultiplier (H := F n) (multiplierEnergyWeight (w n)) (μ n) ⟨(u : WeightSum (F := F) μ) n,he n⟩‖ ^ 2 =
        ‖(u : WeightSum (F := F) μ) n‖ ^ 2+(⟪(u : WeightSum (F := F) μ) n,sumWeightValue (F := F) μ u n⟫_ℂ).re := by
    have h := multiplierEnergyWeight_norm_sq (hw n) (hw0 n) (sumComponentInput (F := F) μ u n)
    rw [sumComponent_action] at h
    exact h
  have hu := (GW.Analysis.memℓp_two_iff_sq _).mp (u : WeightSum (F := F) μ).property
  have hip := (Complex.hasSum_re (lp.summable_inner (𝕜 := ℂ) (u : WeightSum (F := F) μ) (sumWeightValue (F := F) μ u)).hasSum).summable
  refine ⟨he,?_⟩
  simpa only [hn] using hu.add hip

def sumEnergyInput (hw : ∀ n, Measurable (w n)) (hw0 : ∀ n x, 0 ≤ w n x)
    (u : sumWeightDomain (F := F) μ w) : sumWeightDomain (F := F) μ (fun n => multiplierEnergyWeight (w n)) :=
  ⟨u,sumEnergyWeight_mem (F := F) μ hw hw0 u⟩

lemma sumEnergyWeight_norm_sq (hw : ∀ n, Measurable (w n)) (hw0 : ∀ n x, 0 ≤ w n x)
    (u : sumWeightDomain (F := F) μ w) :
    ‖sumWeightValue (F := F) μ (sumEnergyInput (F := F) μ hw hw0 u)‖ ^ 2 =
      ‖(u : WeightSum (F := F) μ)‖ ^ 2+(⟪(u : WeightSum (F := F) μ),sumWeightValue (F := F) μ u⟫_ℂ).re := by
  have he (n : ℕ) : ‖sumWeightValue (F := F) μ (sumEnergyInput (F := F) μ hw hw0 u) n‖ ^ 2 =
      ‖(u : WeightSum (F := F) μ) n‖ ^ 2+(⟪(u : WeightSum (F := F) μ) n,sumWeightValue (F := F) μ u n⟫_ℂ).re := by
    have hi : sumComponentInput (F := F) μ (sumEnergyInput (F := F) μ hw hw0 u) n =
        multiplierEnergyInput (hw n) (hw0 n) (sumComponentInput (F := F) μ u n) := Subtype.ext rfl
    rw [← sumComponent_action,hi,multiplierEnergyWeight_norm_sq,sumComponent_action]
    rfl
  have hu := (GW.Analysis.memℓp_two_iff_sq _).mp (u : WeightSum (F := F) μ).property
  have hpair := lp.summable_inner (𝕜 := ℂ) (u : WeightSum (F := F) μ) (sumWeightValue (F := F) μ u)
  have hip := (Complex.hasSum_re hpair.hasSum).summable
  calc
    _ = ∑' n, ‖sumWeightValue (F := F) μ (sumEnergyInput (F := F) μ hw hw0 u) n‖ ^ 2 := GW.Analysis.lp_norm_sq _
    _ = ∑' n, (‖(u : WeightSum (F := F) μ) n‖ ^ 2+(⟪(u : WeightSum (F := F) μ) n,sumWeightValue (F := F) μ u n⟫_ℂ).re) := tsum_congr he
    _ = (∑' n, ‖(u : WeightSum (F := F) μ) n‖ ^ 2)+(∑' n, (⟪(u : WeightSum (F := F) μ) n,sumWeightValue (F := F) μ u n⟫_ℂ).re) := hu.tsum_add hip
    _ = _ := by rw [← GW.Analysis.lp_norm_sq,← Complex.re_tsum hpair,← lp.inner_eq_tsum]
end SumGraphWeights

section AppliedSingleCarrier
variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {μ : Measure X} {w : X → ℝ} {S : ClosedSubmodule ℂ (Lp H 2 μ)}
  {hw : Measurable w} {hw1 : ∀ x, 1 ≤ w x}

lemma restricted_weighted_domain_complete [CompleteSpace H] (h : WeightInvariant S hw hw1) :
    CompleteSpace (WeightedDomain (restrictedWeightedGraph h)) := inferInstance

lemma restricted_weighted_domain_norm (h : WeightInvariant S hw hw1)
    (u : WeightedDomain (restrictedWeightedGraph h)) :
    ‖u‖ = ‖GW.Analysis.realMultiplier (H := H) w μ
      (restrictedWeightInput S w (show restrictedWeightDomain S w from u))‖ := rfl

lemma restricted_weighted_domain_inner (h : WeightInvariant S hw hw1)
    (u v : WeightedDomain (restrictedWeightedGraph h)) : ⟪u,v⟫_ℂ =
    ⟪GW.Analysis.realMultiplier (H := H) w μ (restrictedWeightInput S w (show restrictedWeightDomain S w from u)),
      GW.Analysis.realMultiplier (H := H) w μ (restrictedWeightInput S w (show restrictedWeightDomain S w from v))⟫_ℂ := rfl

lemma restrictedWeightDomain_mem_iff (u : S) : u ∈ restrictedWeightDomain S w ↔
    MemLp (fun x => (w x : ℂ) • (u : Lp H 2 μ) x) 2 μ := GW.Analysis.realMultiplier_domain _ _
end AppliedSingleCarrier

section AppliedSumCarrier
variable {Y F : ℕ → Type*} [∀ n, MeasurableSpace (Y n)]
  [∀ n, NormedAddCommGroup (F n)] [∀ n, InnerProductSpace ℂ (F n)]
  (μ : ∀ n, Measure (Y n)) {w : ∀ n, Y n → ℝ}
  {S : ClosedSubmodule ℂ (WeightSum (F := F) μ)}
  {hw : ∀ n, Measurable (w n)} {hw1 : ∀ n x, 1 ≤ w n x}

lemma sum_restricted_weighted_domain_complete [∀ n, CompleteSpace (F n)] (h : SumWeightInvariant (F := F) μ S hw hw1) :
    CompleteSpace (WeightedDomain (sumRestrictedWeightedGraph (F := F) μ h)) := inferInstance

lemma sum_restricted_weighted_domain_norm_sq (h : SumWeightInvariant (F := F) μ S hw hw1)
    (u : WeightedDomain (sumRestrictedWeightedGraph (F := F) μ h)) :
    ‖u‖ ^ 2 = ∑' n, ‖sumWeightValue (F := F) μ
      (sumRestrictedInput (F := F) μ S w (show sumRestrictedDomain (F := F) μ S w from u)) n‖ ^ 2 := GW.Analysis.lp_norm_sq _

lemma sum_restricted_weighted_domain_inner (h : SumWeightInvariant (F := F) μ S hw hw1)
    (u v : WeightedDomain (sumRestrictedWeightedGraph (F := F) μ h)) : ⟪u,v⟫_ℂ =
      ∑' n, ⟪sumWeightValue (F := F) μ (sumRestrictedInput (F := F) μ S w (show sumRestrictedDomain (F := F) μ S w from u)) n,
        sumWeightValue (F := F) μ (sumRestrictedInput (F := F) μ S w (show sumRestrictedDomain (F := F) μ S w from v)) n⟫_ℂ := lp.inner_eq_tsum _ _
end AppliedSumCarrier

end GW.Spaces
