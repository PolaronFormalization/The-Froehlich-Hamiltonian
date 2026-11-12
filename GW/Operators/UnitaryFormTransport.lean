module
public import GW.Operators.FormRepresentation
public import GW.Operators.ResolventAlgebra
@[expose] public section
noncomputable section
open scoped Topology InnerProductSpace
namespace GW.Operators
variable {Q H : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Bounded restrictions of both actual ambient unitaries to the same embedded form space. -/
structure FormUnitaryData (d e : CoerciveFormData Q H) where
  unitary : H ≃ₗᵢ[ℂ] H
  common_embedding : e.embedding = d.embedding
  forward : Q →L[ℂ] Q
  backward : Q →L[ℂ] Q
  forward_embedding : ∀ v, d.embedding (forward v) = unitary (d.embedding v)
  backward_embedding : ∀ v, d.embedding (backward v) = unitary.symm (d.embedding v)
  form_identity : ∀ u v, e.form u v = d.form (backward u) (backward v)

variable {d e : CoerciveFormData Q H} (u : FormUnitaryData d e)

omit [CompleteSpace Q] [CompleteSpace H] in
lemma formUnitary_backward_forward (v : Q) : u.backward (u.forward v) = v := by
  apply d.embedding_injective
  rw [u.backward_embedding,u.forward_embedding,LinearIsometryEquiv.symm_apply_apply]
omit [CompleteSpace Q] [CompleteSpace H] in
lemma formUnitary_forward_backward (v : Q) : u.forward (u.backward v) = v := by
  apply d.embedding_injective
  rw [u.forward_embedding,u.backward_embedding,LinearIsometryEquiv.apply_symm_apply]

lemma formUnitary_forward_witness (w : (formOperator e).domain) :
    ∃ h : u.unitary.symm (w : H) ∈ (formOperator d).domain,
      formOperator d ⟨u.unitary.symm (w : H),h⟩ = u.unitary.symm (formOperator e w) := by
  let z := operatorFormCoordinate e w
  have hz : d.embedding (u.backward z) = u.unitary.symm (w : H) := by
    rw [u.backward_embedding,← u.common_embedding]
    exact congrArg u.unitary.symm (operatorFormCoordinate_embedding e w)
  have hq : ∀ v, d.form v (u.backward z) = ⟪d.embedding v,u.unitary.symm (formOperator e w)⟫_ℂ := by
    intro v
    calc
      _ = e.form (u.forward v) z := by rw [u.form_identity,formUnitary_backward_forward]
      _ = ⟪e.embedding (u.forward v),formOperator e w⟫_ℂ := formOperator_form_identity e w (u.forward v)
      _ = ⟪u.unitary (d.embedding v),formOperator e w⟫_ℂ := by rw [u.common_embedding,u.forward_embedding]
      _ = _ := by
        have h := u.unitary.inner_map_map (d.embedding v) (u.unitary.symm (formOperator e w))
        rw [LinearIsometryEquiv.apply_symm_apply] at h
        exact h
  obtain ⟨hm,hv⟩ := formOperator_domain_of_equation d (u.backward z) (u.unitary.symm (formOperator e w)) hq
  have hmem : u.unitary.symm (w : H) ∈ (formOperator d).domain := hz ▸ hm
  refine ⟨hmem,?_⟩
  have heq : (⟨u.unitary.symm (w : H),hmem⟩ : (formOperator d).domain) = ⟨d.embedding (u.backward z),hm⟩ :=
    Subtype.ext hz.symm
  rw [heq]
  exact hv

lemma formUnitary_reverse_witness (x : (formOperator d).domain) :
    ∃ h : u.unitary (x : H) ∈ (formOperator e).domain,
      formOperator e ⟨u.unitary (x : H),h⟩ = u.unitary (formOperator d x) := by
  let z := operatorFormCoordinate d x
  have hz : e.embedding (u.forward z) = u.unitary (x : H) := by
    rw [u.common_embedding,u.forward_embedding]
    exact congrArg u.unitary (operatorFormCoordinate_embedding d x)
  have hq : ∀ v, e.form v (u.forward z) = ⟪e.embedding v,u.unitary (formOperator d x)⟫_ℂ := by
    intro v
    rw [u.form_identity,formUnitary_backward_forward,formOperator_form_identity]
    rw [u.backward_embedding,u.common_embedding]
    have h := u.unitary.inner_map_map (u.unitary.symm (d.embedding v)) (formOperator d x)
    rw [LinearIsometryEquiv.apply_symm_apply] at h
    exact h.symm
  obtain ⟨hm,hv⟩ := formOperator_domain_of_equation e (u.forward z) (u.unitary (formOperator d x)) hq
  have hmem : u.unitary (x : H) ∈ (formOperator e).domain := hz ▸ hm
  refine ⟨hmem,?_⟩
  have heq : (⟨u.unitary (x : H),hmem⟩ : (formOperator e).domain) = ⟨e.embedding (u.forward z),hm⟩ :=
    Subtype.ext hz.symm
  rw [heq]
  exact hv

lemma formUnitary_domain : (formOperator d).domain =
    (formOperator e).domain.map u.unitary.symm.toLinearMap := by
  apply Submodule.ext
  intro x
  constructor
  · intro hx
    have hm := (formUnitary_reverse_witness u ⟨x,hx⟩).choose
    exact ⟨u.unitary x,hm,u.unitary.symm_apply_apply x⟩
  · rintro ⟨w,hw,hx⟩
    have hm := (formUnitary_forward_witness u ⟨w,hw⟩).choose
    exact hx ▸ hm

lemma formUnitary_operator : formOperator d = unitaryTransport u.unitary (formOperator e) := by
  apply LinearPMap.ext
  · rw [unitaryTransport_domain]
    exact formUnitary_domain u
  · intro x hx ht
    obtain ⟨hm,hv⟩ := formUnitary_reverse_witness u ⟨x,hx⟩
    change formOperator d ⟨x,hx⟩ = u.unitary.symm
      (formOperator e ⟨u.unitary x,(show u.unitary x ∈ (formOperator e).domain from ht)⟩)
    rw [hv,LinearIsometryEquiv.symm_apply_apply]

lemma formUnitary_domain_iff (x : H) :
    x ∈ (formOperator d).domain ↔ u.unitary x ∈ (formOperator e).domain := by
  constructor
  · intro hx
    exact (formUnitary_reverse_witness u ⟨x,hx⟩).choose
  · intro hx
    have h := (formUnitary_forward_witness u ⟨u.unitary x,hx⟩).choose
    simpa only [LinearIsometryEquiv.symm_apply_apply] using h

def formUnitaryForwardInput (w : (formOperator e).domain) : (formOperator d).domain :=
  ⟨u.unitary.symm (w : H),(formUnitary_forward_witness u w).choose⟩
lemma formUnitaryForwardInput_action (w : (formOperator e).domain) :
    formOperator d (formUnitaryForwardInput u w) = u.unitary.symm (formOperator e w) :=
  (formUnitary_forward_witness u w).choose_spec

def formUnitaryReverseInput (x : (formOperator d).domain) : (formOperator e).domain :=
  ⟨u.unitary (x : H),(formUnitary_reverse_witness u x).choose⟩
lemma formUnitaryReverseInput_action (x : (formOperator d).domain) :
    formOperator e (formUnitaryReverseInput u x) = u.unitary (formOperator d x) :=
  (formUnitary_reverse_witness u x).choose_spec

omit [CompleteSpace Q] [CompleteSpace H] in
lemma formUnitary_forward_range : u.unitary '' Set.range d.embedding = Set.range d.embedding := by
  ext x
  constructor
  · rintro ⟨y,⟨v,rfl⟩,rfl⟩
    exact ⟨u.forward v,u.forward_embedding v⟩
  · rintro ⟨v,rfl⟩
    refine ⟨d.embedding (u.backward v),⟨u.backward v,rfl⟩,?_⟩
    rw [u.backward_embedding,LinearIsometryEquiv.apply_symm_apply]

omit [CompleteSpace Q] [CompleteSpace H] in
lemma formUnitary_backward_range : u.unitary.symm '' Set.range d.embedding = Set.range d.embedding := by
  ext x
  constructor
  · rintro ⟨y,⟨v,rfl⟩,rfl⟩
    exact ⟨u.backward v,u.backward_embedding v⟩
  · rintro ⟨v,rfl⟩
    refine ⟨d.embedding (u.forward v),⟨u.forward v,rfl⟩,?_⟩
    rw [u.forward_embedding,LinearIsometryEquiv.symm_apply_apply]

lemma formUnitary_representatives (L L' : H →ₗ.[ℂ] H)
    (hL : IsSelfAdjointOperator L) (hL' : IsSelfAdjointOperator L')
    (hd : ∀ x : L.domain, ∃ v : Q, d.embedding v = (x : H) ∧
      ∀ z, d.form z v = ⟪d.embedding z,L x⟫_ℂ)
    (he : ∀ x : L'.domain, ∃ v : Q, e.embedding v = (x : H) ∧
      ∀ z, e.form z v = ⟪e.embedding z,L' x⟫_ℂ) :
    L = unitaryTransport u.unitary L' ∧ L.domain = L'.domain.map u.unitary.symm.toLinearMap := by
  have h₁ := formOperator_unique d L hL hd
  have h₂ := formOperator_unique e L' hL' he
  subst L
  subst L'
  exact ⟨formUnitary_operator u,formUnitary_domain u⟩

end GW.Operators
