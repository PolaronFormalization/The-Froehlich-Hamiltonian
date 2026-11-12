module
public import GW.Operators.SelfadjointCriterion
/-! Source basic:resolvent. Full-domain inverse identities justify every product.
Unitary transport uses actual preimage domains and Hilbert graph isometries. -/
@[expose] public section
noncomputable section
open scoped Topology InnerProductSpace
namespace GW.Operators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Exact bounded inverse obligations; this also covers separately constructed real inverses. -/
structure IsResolvent (T : H →ₗ.[ℂ] H) (z : ℂ) (R : H →L[ℂ] H) : Prop where
  mem_domain : ∀ f, R f ∈ T.domain
  left_inv : ∀ f, complexShift T z ⟨R f, mem_domain f⟩ = f
  right_inv : ∀ u : T.domain, R (complexShift T z u) = (u : H)

namespace IsResolvent
variable {T : H →ₗ.[ℂ] H} {z : ℂ} {R : H →L[ℂ] H}

def input (hR : IsResolvent T z R) (f : H) : T.domain := ⟨R f, hR.mem_domain f⟩
lemma input_coe (hR : IsResolvent T z R) (f : H) : (hR.input f : H) = R f := rfl
lemma input_action (hR : IsResolvent T z R) (f : H) : complexShift T z (hR.input f) = f := hR.left_inv f
end IsResolvent

section Complete
variable [CompleteSpace H]
lemma resolvent_isResolvent (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjointOperator T) (z : ℂ) (hz : z.im ≠ 0) :
    IsResolvent T z (resolvent T hT z hz) where
  mem_domain := resolvent_mem_domain T hT z hz
  left_inv := resolventInput_action T hT z hz
  right_inv := resolvent_right_inverse T hT z hz

end Complete

lemma isResolvent_unique {T : H →ₗ.[ℂ] H} {z : ℂ} {R S : H →L[ℂ] H}
    (hR : IsResolvent T z R) (hS : IsResolvent T z S) : R = S := by
  ext f
  have h := hR.right_inv (hS.input f)
  rw [hS.input_action] at h
  exact h

lemma resolvent_difference {T : H →ₗ.[ℂ] H} {z w : ℂ} {Rz Rw : H →L[ℂ] H}
    (hz : IsResolvent T z Rz) (hw : IsResolvent T w Rw) :
    Rz - Rw = (z-w) • (Rz.comp Rw) := by
  ext f
  have hA : complexShift T z (hw.input f) = f + (w-z) • Rw f := by
    have he := hw.input_action f
    change T (hw.input f)-w • Rw f = f at he
    change T (hw.input f)-z • Rw f = f + (w-z) • Rw f
    calc
      T (hw.input f)-z • Rw f = (T (hw.input f)-w • Rw f)+(w-z) • Rw f := by module
      _ = f+(w-z) • Rw f := congrArg (fun v : H => v+(w-z) • Rw f) he
  have he := (hz.right_inv (hw.input f)).symm.trans (congrArg Rz hA)
  rw [map_add, map_smul] at he
  change Rz f - Rw f = (z-w) • Rz (Rw f)
  change Rw f = Rz f+(w-z) • Rz (Rw f) at he
  conv_lhs => rw [he]
  module

lemma resolvent_commute {T : H →ₗ.[ℂ] H} {z w : ℂ} {Rz Rw : H →L[ℂ] H}
    (hz : IsResolvent T z Rz) (hw : IsResolvent T w Rw) : Rz.comp Rw = Rw.comp Rz := by
  by_cases hzw : z = w
  · have he : Rz = Rw := isResolvent_unique (hzw ▸ hz) hw
    rw [he]
  · ext f
    change Rz (Rw f) = Rw (Rz f)
    have h1 := congrArg (fun L : H →L[ℂ] H => L f) (resolvent_difference hz hw)
    have h2 := congrArg (fun L : H →L[ℂ] H => L f) (resolvent_difference hw hz)
    change Rz f-Rw f = (z-w) • Rz (Rw f) at h1
    change Rw f-Rz f = (w-z) • Rw (Rz f) at h2
    have he : (z-w) • Rz (Rw f) = (z-w) • Rw (Rz f) := by
      calc
        (z-w) • Rz (Rw f) = Rz f-Rw f := h1.symm
        _ = -(Rw f-Rz f) := by abel
        _ = -((w-z) • Rw (Rz f)) := congrArg Neg.neg h2
        _ = (z-w) • Rw (Rz f) := by module
    have hh := congrArg (fun v : H => (z-w)⁻¹ • v) he
    simpa only [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hzw), one_smul] using hh

section Adjoint
variable [CompleteSpace H]
lemma resolvent_adjoint {T : H →ₗ.[ℂ] H} (hs : T.IsFormalAdjoint T) {z : ℂ}
    {Rz Rc : H →L[ℂ] H} (hz : IsResolvent T z Rz) (hc : IsResolvent T ((starRingEnd ℂ) z) Rc) :
    Rz.adjoint = Rc := by
  apply Eq.symm
  apply (ContinuousLinearMap.eq_adjoint_iff Rc Rz).mpr
  intro f g
  have hx := hc.input_action f
  have hy := hz.input_action g
  have hsym := hs (hc.input f) (hz.input g)
  change ⟪T (hc.input f), Rz g⟫_ℂ = ⟪Rc f, T (hz.input g)⟫_ℂ at hsym
  change T (hc.input f)-(starRingEnd ℂ) z • Rc f = f at hx
  change T (hz.input g)-z • Rz g = g at hy
  change ⟪Rc f, g⟫_ℂ = ⟪f,Rz g⟫_ℂ
  calc
    ⟪Rc f, g⟫_ℂ = ⟪Rc f, T (hz.input g)-z • Rz g⟫_ℂ :=
      congrArg (fun v : H => ⟪Rc f,v⟫_ℂ) hy.symm
    _ = ⟪T (hc.input f)-(starRingEnd ℂ) z • Rc f,Rz g⟫_ℂ := by
      simp only [inner_sub_right, inner_smul_right, inner_sub_left, inner_smul_left,
        starRingEnd_apply, star_star]
      exact congrArg (fun a : ℂ => a-z * ⟪Rc f,Rz g⟫_ℂ) hsym.symm
    _ = ⟪f,Rz g⟫_ℂ := congrArg (fun v : H => ⟪v,Rz g⟫_ℂ) hx

end Adjoint

/-- An equal-domain input is transported before applying the second operator. -/
def sameDomainInput {S T : H →ₗ.[ℂ] H} (hd : S.domain = T.domain) (u : T.domain) : S.domain :=
  ⟨u, by rw [hd]; exact u.property⟩

lemma second_resolvent_difference {S T : H →ₗ.[ℂ] H} (hd : S.domain = T.domain) {z : ℂ}
    {RS RT : H →L[ℂ] H} (hS : IsResolvent S z RS) (hT : IsResolvent T z RT)
    (D : H →L[ℂ] H)
    (hD : ∀ f, D f = S (sameDomainInput hd (hT.input f))-T (hT.input f)) :
    RS-RT = -(RS.comp D) := by
  ext f
  have hA : complexShift S z (sameDomainInput hd (hT.input f)) = f+D f := by
    have he := hT.input_action f
    change T (hT.input f)-z • RT f = f at he
    change S (sameDomainInput hd (hT.input f))-z • RT f = f+D f
    calc
      S (sameDomainInput hd (hT.input f))-z • RT f =
        (T (hT.input f)-z • RT f)+(S (sameDomainInput hd (hT.input f))-T (hT.input f)) := by module
      _ = f+D f := congrArg₂ (fun a b : H => a+b) he (hD f).symm
  have he := (hS.right_inv (sameDomainInput hd (hT.input f))).symm.trans (congrArg RS hA)
  rw [map_add] at he
  change RT f = RS f+RS (D f) at he
  change RS f-RT f = -RS (D f)
  conv_lhs => rw [he]
  abel
/-- Restrict the unitary to the exact transported domain before applying T. -/
def unitaryDomainMap (U : H ≃ₗᵢ[ℂ] H) (T : H →ₗ.[ℂ] H) :
    T.domain.comap U.toLinearMap →ₗ[ℂ] T.domain where
  toFun u := ⟨U (u : H), u.property⟩
  map_add' u v := Subtype.ext (U.map_add (u : H) (v : H))
  map_smul' c u := Subtype.ext (U.map_smul c (u : H))

/-- Unitary transport on the actual preimage domain, with inverse unitary action. -/
def unitaryTransport (U : H ≃ₗᵢ[ℂ] H) (T : H →ₗ.[ℂ] H) : H →ₗ.[ℂ] H where
  domain := T.domain.comap U.toLinearMap
  toFun := U.symm.toLinearMap.comp (T.toFun.comp (unitaryDomainMap U T))

lemma unitaryTransport_apply (U : H ≃ₗᵢ[ℂ] H) (T : H →ₗ.[ℂ] H) (u : (unitaryTransport U T).domain) :
    unitaryTransport U T u = U.symm (T (unitaryDomainMap U T u)) := rfl

lemma unitaryTransport_domain (U : H ≃ₗᵢ[ℂ] H) (T : H →ₗ.[ℂ] H) :
    (unitaryTransport U T).domain = T.domain.map U.symm.toLinearMap := by
  ext x
  constructor
  · intro hx
    exact ⟨U x, hx, U.symm_apply_apply x⟩
  · rintro ⟨y,hy,hx⟩
    change U x ∈ T.domain
    rw [← hx]
    change U (U.symm y) ∈ T.domain
    rw [U.apply_symm_apply]
    exact hy

lemma unitaryDomainMap_bijective (U : H ≃ₗᵢ[ℂ] H) (T : H →ₗ.[ℂ] H) :
    Function.Bijective (unitaryDomainMap U T) := by
  constructor
  · intro u v he
    apply Subtype.ext
    exact U.injective (congrArg Subtype.val he)
  · intro v
    let u : T.domain.comap U.toLinearMap := ⟨U.symm (v : H), by
      change U (U.symm (v : H)) ∈ T.domain
      rw [U.apply_symm_apply]
      exact v.property⟩
    exact ⟨u, Subtype.ext (U.apply_symm_apply (v : H))⟩

def unitaryDomainEquiv (U : H ≃ₗᵢ[ℂ] H) (T : H →ₗ.[ℂ] H) :
    (unitaryTransport U T).domain ≃ₗ[ℂ] T.domain :=
  LinearEquiv.ofBijective (unitaryDomainMap U T) (unitaryDomainMap_bijective U T)

lemma unitaryTransport_graph_iff (U : H ≃ₗᵢ[ℂ] H) (T : H →ₗ.[ℂ] H) (p : H × H) :
    p ∈ (unitaryTransport U T).graph ↔ (U p.1,U p.2) ∈ T.graph := by
  constructor
  · intro hp
    obtain ⟨u,hu,hval⟩ := (unitaryTransport U T).mem_graph_iff.mp hp
    refine T.mem_graph_iff.mpr ⟨unitaryDomainMap U T u, congrArg U hu, ?_⟩
    have he := congrArg U hval
    change U (U.symm (T (unitaryDomainMap U T u))) = U p.2 at he
    rwa [U.apply_symm_apply] at he
  · intro hp
    obtain ⟨v,hv,hval⟩ := T.mem_graph_iff.mp hp
    change (v : H) = U p.1 at hv
    change T v = U p.2 at hval
    let u : (unitaryTransport U T).domain := ⟨p.1, by
      change U p.1 ∈ T.domain
      rw [← hv]
      exact v.property⟩
    refine (unitaryTransport U T).mem_graph_iff.mpr ⟨u,rfl,?_⟩
    have he : unitaryDomainMap U T u = v := Subtype.ext hv.symm
    change U.symm (T (unitaryDomainMap U T u)) = p.2
    rw [he,hval,U.symm_apply_apply]

lemma unitaryTransport_closed (U : H ≃ₗᵢ[ℂ] H) (T : H →ₗ.[ℂ] H) (hT : T.IsClosed) :
    (unitaryTransport U T).IsClosed := by
  have he : ((unitaryTransport U T).graph : Set (H × H)) =
      (fun p : H × H => (U p.1,U p.2)) ⁻¹' (T.graph : Set (H × H)) :=
    Set.ext (unitaryTransport_graph_iff U T)
  change IsClosed ((unitaryTransport U T).graph : Set (H × H))
  rw [he]
  exact hT.preimage ((U.continuous.comp continuous_fst).prodMk (U.continuous.comp continuous_snd))

lemma unitaryTransport_dense (U : H ≃ₗᵢ[ℂ] H) (T : H →ₗ.[ℂ] H) (hd : Dense (T.domain : Set H)) :
    Dense ((unitaryTransport U T).domain : Set H) := by
  change Dense (U ⁻¹' (T.domain : Set H))
  exact hd.preimage U.toHomeomorph.isOpenMap

lemma unitary_inner_symm (U : H ≃ₗᵢ[ℂ] H) (a b : H) :
    ⟪U.symm a,b⟫_ℂ = ⟪a,U b⟫_ℂ := by
  simpa only [LinearIsometryEquiv.symm_symm] using U.symm.inner_map_eq_flip a b

lemma unitaryTransport_witness_iff (U : H ≃ₗᵢ[ℂ] H) (T : H →ₗ.[ℂ] H) (y h : H) :
    (∀ u : (unitaryTransport U T).domain, ⟪unitaryTransport U T u,y⟫_ℂ = ⟪(u : H),h⟫_ℂ) ↔
    (∀ v : T.domain, ⟪T v,U y⟫_ℂ = ⟪(v : H),U h⟫_ℂ) := by
  constructor
  · intro hw v
    let u := (unitaryDomainEquiv U T).symm v
    have he := hw u
    change ⟪U.symm (T (unitaryDomainMap U T u)),y⟫_ℂ = ⟪(u : H),h⟫_ℂ at he
    rw [unitary_inner_symm, ← U.inner_map_map (u : H) h] at he
    change ⟪T (unitaryDomainMap U T u),U y⟫_ℂ = ⟪(unitaryDomainMap U T u : H),U h⟫_ℂ at he
    have hu : unitaryDomainMap U T u = v := (unitaryDomainEquiv U T).apply_symm_apply v
    rwa [hu] at he
  · intro hw u
    have he := hw (unitaryDomainMap U T u)
    change ⟪T (unitaryDomainMap U T u),U y⟫_ℂ = ⟪U (u : H),U h⟫_ℂ at he
    rw [U.inner_map_map] at he
    change ⟪U.symm (T (unitaryDomainMap U T u)),y⟫_ℂ = ⟪(u : H),h⟫_ℂ
    rw [unitary_inner_symm]
    exact he

section UnitaryAdjoint
variable [CompleteSpace H]

lemma unitaryTransport_adjoint (U : H ≃ₗᵢ[ℂ] H) (T : H →ₗ.[ℂ] H) (hd : Dense (T.domain : Set H)) :
    (unitaryTransport U T).adjoint = unitaryTransport U T.adjoint := by
  apply LinearPMap.eq_of_eq_graph
  ext p
  rw [adjoint_graph_iff (unitaryTransport U T) (unitaryTransport_dense U T hd),
    unitaryTransport_graph_iff, adjoint_graph_iff T hd]
  exact unitaryTransport_witness_iff U T p.1 p.2

lemma unitaryTransport_selfadjoint (U : H ≃ₗᵢ[ℂ] H) (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjointOperator T) :
    IsSelfAdjointOperator (unitaryTransport U T) := by
  refine ⟨unitaryTransport_dense U T hT.1, ?_⟩
  rw [unitaryTransport_adjoint U T hT.1,hT.2]
end UnitaryAdjoint

def unitaryBounded (U : H ≃ₗᵢ[ℂ] H) : H →L[ℂ] H := U.toLinearIsometry.toContinuousLinearMap

def unitaryConjugate (U : H ≃ₗᵢ[ℂ] H) (R : H →L[ℂ] H) : H →L[ℂ] H :=
  (unitaryBounded U.symm).comp (R.comp (unitaryBounded U))

lemma unitaryConjugate_apply (U : H ≃ₗᵢ[ℂ] H) (R : H →L[ℂ] H) (f : H) :
    unitaryConjugate U R f = U.symm (R (U f)) := rfl

lemma unitaryConjugate_isResolvent (U : H ≃ₗᵢ[ℂ] H) {T : H →ₗ.[ℂ] H} {z : ℂ} {R : H →L[ℂ] H}
    (hR : IsResolvent T z R) : IsResolvent (unitaryTransport U T) z (unitaryConjugate U R) := by
  have hmem (f : H) : unitaryConjugate U R f ∈ (unitaryTransport U T).domain := by
    change U (U.symm (R (U f))) ∈ T.domain
    rw [U.apply_symm_apply]
    exact hR.mem_domain (U f)
  refine ⟨hmem, ?_, ?_⟩
  · intro f
    let u : (unitaryTransport U T).domain := ⟨unitaryConjugate U R f,hmem f⟩
    have hu : unitaryDomainMap U T u = hR.input (U f) := Subtype.ext (U.apply_symm_apply (R (U f)))
    have he := hR.input_action (U f)
    change T (hR.input (U f))-z • R (U f) = U f at he
    change U.symm (T (unitaryDomainMap U T u))-z • U.symm (R (U f)) = f
    rw [hu]
    calc
      U.symm (T (hR.input (U f)))-z • U.symm (R (U f)) =
          U.symm (T (hR.input (U f))-z • R (U f)) := by rw [map_sub,map_smul]
      _ = U.symm (U f) := congrArg U.symm he
      _ = f := U.symm_apply_apply f
  · intro u
    have he : U (complexShift (unitaryTransport U T) z u) = complexShift T z (unitaryDomainMap U T u) := by
      change U (U.symm (T (unitaryDomainMap U T u))-z • (u : H)) =
        T (unitaryDomainMap U T u)-z • U (u : H)
      rw [map_sub,map_smul,U.apply_symm_apply]
    change U.symm (R (U (complexShift (unitaryTransport U T) z u))) = (u : H)
    rw [he,hR.right_inv]
    exact U.symm_apply_apply (u : H)

section CompleteUnitary
variable [CompleteSpace H]

lemma unitaryBounded_adjoint (U : H ≃ₗᵢ[ℂ] H) : (unitaryBounded U).adjoint = unitaryBounded U.symm := by
  apply Eq.symm
  apply (ContinuousLinearMap.eq_adjoint_iff (unitaryBounded U.symm) (unitaryBounded U)).mpr
  exact unitary_inner_symm U

lemma unitary_resolvent (U : H ≃ₗᵢ[ℂ] H) (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjointOperator T)
    (z : ℂ) (hz : z.im ≠ 0) :
    resolvent (unitaryTransport U T) (unitaryTransport_selfadjoint U T hT) z hz =
      unitaryConjugate U (resolvent T hT z hz) :=
  isResolvent_unique
    (resolvent_isResolvent (unitaryTransport U T) (unitaryTransport_selfadjoint U T hT) z hz)
    (unitaryConjugate_isResolvent U (resolvent_isResolvent T hT z hz))
end CompleteUnitary

/-- The source graph-norm isometry, using WithLp 2 on both actual graphs. -/
def unitaryGraphEquiv (U : H ≃ₗᵢ[ℂ] H) (T : H →ₗ.[ℂ] H) (hT : T.IsClosed) :
    GraphDomain (unitaryTransport U T) (unitaryTransport_closed U T hT) ≃ₗᵢ[ℂ] GraphDomain T hT where
  toLinearEquiv :=
    { toFun v := ⟨WithLp.toLp 2 (U (v : WithLp 2 (H × H)).fst,U (v : WithLp 2 (H × H)).snd),
        (unitaryTransport_graph_iff U T ((v : WithLp 2 (H × H)).fst,(v : WithLp 2 (H × H)).snd)).mp v.property⟩
      invFun w := ⟨WithLp.toLp 2 (U.symm (w : WithLp 2 (H × H)).fst,U.symm (w : WithLp 2 (H × H)).snd), by
        apply (unitaryTransport_graph_iff U T (U.symm (w : WithLp 2 (H × H)).fst,U.symm (w : WithLp 2 (H × H)).snd)).mpr
        change (U (U.symm (w : WithLp 2 (H × H)).fst),U (U.symm (w : WithLp 2 (H × H)).snd)) ∈ T.graph
        rw [U.apply_symm_apply,U.apply_symm_apply]
        exact w.property⟩
      left_inv v := by
        apply Subtype.ext
        apply (WithLp.equiv 2 (H × H)).injective
        exact Prod.ext (U.symm_apply_apply _) (U.symm_apply_apply _)
      right_inv w := by
        apply Subtype.ext
        apply (WithLp.equiv 2 (H × H)).injective
        exact Prod.ext (U.apply_symm_apply _) (U.apply_symm_apply _)
      map_add' v w := by
        apply Subtype.ext
        apply (WithLp.equiv 2 (H × H)).injective
        change (U ((v : WithLp 2 (H × H))+(w : WithLp 2 (H × H))).fst,
          U ((v : WithLp 2 (H × H))+(w : WithLp 2 (H × H))).snd) =
          (U (v : WithLp 2 (H × H)).fst+U (w : WithLp 2 (H × H)).fst,
          U (v : WithLp 2 (H × H)).snd+U (w : WithLp 2 (H × H)).snd)
        simp only [WithLp.add_fst,WithLp.add_snd,map_add]
      map_smul' c v := by
        apply Subtype.ext
        apply (WithLp.equiv 2 (H × H)).injective
        change (U (c • (v : WithLp 2 (H × H))).fst,U (c • (v : WithLp 2 (H × H))).snd) =
          (c • U (v : WithLp 2 (H × H)).fst,c • U (v : WithLp 2 (H × H)).snd)
        simp only [WithLp.smul_fst,WithLp.smul_snd,map_smul] }
  norm_map' v := by
    change ‖WithLp.toLp 2 (U (v : WithLp 2 (H × H)).fst,U (v : WithLp 2 (H × H)).snd)‖ =
      ‖(v : WithLp 2 (H × H))‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2,WithLp.prod_norm_sq_eq_of_L2]
    change ‖U (v : WithLp 2 (H × H)).fst‖ ^ 2+‖U (v : WithLp 2 (H × H)).snd‖ ^ 2 = _
    rw [U.norm_map,U.norm_map]

lemma unitaryGraphEquiv_inclusion (U : H ≃ₗᵢ[ℂ] H) (T : H →ₗ.[ℂ] H) (hT : T.IsClosed)
    (v : GraphDomain (unitaryTransport U T) (unitaryTransport_closed U T hT)) :
    graphInclusion T hT (unitaryGraphEquiv U T hT v) =
      U (graphInclusion (unitaryTransport U T) (unitaryTransport_closed U T hT) v) := rfl

lemma unitaryGraphEquiv_symm_inclusion (U : H ≃ₗᵢ[ℂ] H) (T : H →ₗ.[ℂ] H) (hT : T.IsClosed)
    (v : GraphDomain T hT) :
    graphInclusion (unitaryTransport U T) (unitaryTransport_closed U T hT)
      ((unitaryGraphEquiv U T hT).symm v) = U.symm (graphInclusion T hT v) := rfl

lemma unitary_image_mem (U : H ≃ₗᵢ[ℂ] H) (C : Submodule ℂ H) (x : H) :
    x ∈ C.map U.symm.toLinearMap ↔ U x ∈ C := by
  constructor
  · rintro ⟨y,hy,hx⟩
    have he : U.symm y = x := hx
    rw [← he,U.apply_symm_apply]
    exact hy
  · intro hx
    exact ⟨U x,hx,U.symm_apply_apply x⟩

lemma unitaryTransport_core_iff (U : H ≃ₗᵢ[ℂ] H) (T : H →ₗ.[ℂ] H) (hT : T.IsClosed)
    (C : Submodule ℂ H) (hC : C ≤ T.domain) :
    T.HasCore C ↔ (unitaryTransport U T).HasCore (C.map U.symm.toLinearMap) := by
  have hS := unitaryTransport_closed U T hT
  have hCS : C.map U.symm.toLinearMap ≤ (unitaryTransport U T).domain := by
    intro x hx
    change U x ∈ T.domain
    exact hC ((unitary_image_mem U C x).mp hx)
  rw [hasCore_iff_graph_dense T hT C hC,
    hasCore_iff_graph_dense (unitaryTransport U T) hS (C.map U.symm.toLinearMap) hCS]
  let W := unitaryGraphEquiv U T hT
  constructor
  · intro hd
    have hp := hd.preimage W.toHomeomorph.isOpenMap
    have heq : W ⁻¹' {v : GraphDomain T hT | graphInclusion T hT v ∈ C} =
        {v | graphInclusion (unitaryTransport U T) hS v ∈ C.map U.symm.toLinearMap} := by
      ext v
      change graphInclusion T hT (W v) ∈ C ↔ graphInclusion (unitaryTransport U T) hS v ∈ C.map U.symm.toLinearMap
      rw [unitaryGraphEquiv_inclusion,unitary_image_mem]
    change Dense (W ⁻¹' {v : GraphDomain T hT | graphInclusion T hT v ∈ C}) at hp
    rwa [heq] at hp
  · intro hd
    have hp := hd.preimage W.symm.toHomeomorph.isOpenMap
    have heq : W.symm ⁻¹' {v | graphInclusion (unitaryTransport U T) hS v ∈ C.map U.symm.toLinearMap} =
        {v : GraphDomain T hT | graphInclusion T hT v ∈ C} := by
      ext v
      change graphInclusion (unitaryTransport U T) hS (W.symm v) ∈ C.map U.symm.toLinearMap ↔
        graphInclusion T hT v ∈ C
      rw [unitary_image_mem,unitaryGraphEquiv_symm_inclusion,U.apply_symm_apply]
    change Dense (W.symm ⁻¹' {v | graphInclusion (unitaryTransport U T) hS v ∈ C.map U.symm.toLinearMap}) at hp
    rwa [heq] at hp

/-- The full core equivalence includes both domain-inclusion implications. -/
lemma unitaryTransport_hasCore_iff (U : H ≃ₗᵢ[ℂ] H) (T : H →ₗ.[ℂ] H) (hT : T.IsClosed)
    (C : Submodule ℂ H) :
    (unitaryTransport U T).HasCore (C.map U.symm.toLinearMap) ↔ T.HasCore C := by
  constructor
  · intro hc
    have hC : C ≤ T.domain := by
      intro x hx
      have hy : U.symm x ∈ C.map U.symm.toLinearMap := ⟨x,hx,rfl⟩
      have hm := hc.le_domain hy
      change U (U.symm x) ∈ T.domain at hm
      rwa [U.apply_symm_apply] at hm
    exact (unitaryTransport_core_iff U T hT C hC).mpr hc
  · intro hc
    exact (unitaryTransport_core_iff U T hT C hc.le_domain).mp hc

section ActualResolvents
variable [CompleteSpace H]

lemma conjugate_nonreal {z : ℂ} (hz : z.im ≠ 0) : ((starRingEnd ℂ) z).im ≠ 0 := by
  simpa only [Complex.conj_im,neg_ne_zero] using hz

lemma resolvent_adjoint_eq (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjointOperator T) (z : ℂ) (hz : z.im ≠ 0) :
    (resolvent T hT z hz).adjoint = resolvent T hT ((starRingEnd ℂ) z) (conjugate_nonreal hz) := by
  have hs : T.IsFormalAdjoint T := by simpa only [hT.2] using LinearPMap.adjoint_isFormalAdjoint hT.1
  exact resolvent_adjoint hs (resolvent_isResolvent T hT z hz)
    (resolvent_isResolvent T hT _ (conjugate_nonreal hz))

lemma resolvent_identity (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjointOperator T) (z w : ℂ)
    (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    resolvent T hT z hz-resolvent T hT w hw =
      (z-w) • ((resolvent T hT z hz).comp (resolvent T hT w hw)) :=
  resolvent_difference (resolvent_isResolvent T hT z hz) (resolvent_isResolvent T hT w hw)

lemma resolvents_commute (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjointOperator T) (z w : ℂ)
    (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    (resolvent T hT z hz).comp (resolvent T hT w hw) =
      (resolvent T hT w hw).comp (resolvent T hT z hz) :=
  resolvent_commute (resolvent_isResolvent T hT z hz) (resolvent_isResolvent T hT w hw)

lemma resolvent_second_identity (S T : H →ₗ.[ℂ] H) (hS : IsSelfAdjointOperator S)
    (hT : IsSelfAdjointOperator T) (hd : S.domain = T.domain) (z : ℂ) (hz : z.im ≠ 0)
    (D : H →L[ℂ] H)
    (hD : ∀ f, D f = S (sameDomainInput hd (resolventInput T hT z hz f))-T (resolventInput T hT z hz f)) :
    resolvent S hS z hz-resolvent T hT z hz = -((resolvent S hS z hz).comp D) :=
  second_resolvent_difference hd (resolvent_isResolvent S hS z hz) (resolvent_isResolvent T hT z hz) D hD
end ActualResolvents

/-- The inverse-operator construction supplies an actual real resolvent point. -/
lemma inverseOperator_isResolvent (R : H →L[ℂ] H) (hR : Function.Injective R) (c : ℝ) :
    IsResolvent (realShift (inverseOperator R hR) c) ((-c : ℝ) : ℂ) R := by
  refine ⟨fun f => LinearMap.mem_range_self R.toLinearMap f, ?_, ?_⟩
  · intro f
    change (inverseOperator R hR ⟨R f,_⟩-(c : ℂ) • R f)-((-c : ℝ) : ℂ) • R f = f
    rw [inverseOperator_left]
    simp only [Complex.ofReal_neg,neg_smul]
    module
  · intro u
    change R ((inverseOperator R hR u-(c : ℂ) • (u : H))-((-c : ℝ) : ℂ) • (u : H)) = (u : H)
    have he : (inverseOperator R hR u-(c : ℂ) • (u : H))-((-c : ℝ) : ℂ) • (u : H) = inverseOperator R hR u := by
      simp only [Complex.ofReal_neg,neg_smul]
      module
    rw [he]
    change R (inverseOperator R hR ⟨(u : H),u.property⟩) = (u : H)
    exact inverseOperator_right R hR ⟨(u : H),u.property⟩

end GW.Operators
