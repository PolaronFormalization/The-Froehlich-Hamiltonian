module
public import GW.Fock.FockFieldSelfadjoint
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal
namespace GW.Fock

def fieldConjugationShift (f g : OneBoson) : ℂ := ⟪g,f⟫_ℂ+⟪f,g⟫_ℂ

set_option backward.isDefEq.respectTransparency.types false in
lemma fieldConjugationShift_real (f g : OneBoson) :
    fieldConjugationShift f g = ((2*(⟪f,g⟫_ℂ).re:ℝ):ℂ) := by
  have hc : ⟪g,f⟫_ℂ = (starRingEnd ℂ) ⟪f,g⟫_ℂ := by
    convert! (inner_conj_symm g f).symm using 1 <;> rfl
  change ⟪g,f⟫_ℂ+⟪f,g⟫_ℂ = _
  calc
    _ = (starRingEnd ℂ) ⟪f,g⟫_ℂ+⟪f,g⟫_ℂ := congrArg (fun z : ℂ => z+⟪f,g⟫_ℂ) hc
    _ = ⟪f,g⟫_ℂ+(starRingEnd ℂ) ⟪f,g⟫_ℂ := add_comm _ _
    _ = (2:ℂ)*((⟪f,g⟫_ℂ).re:ℂ) := by convert! RCLike.add_conj ⟪f,g⟫_ℂ using 1 <;> rfl
    _ = _ := by push_cast; rfl

set_option backward.isDefEq.respectTransparency.types false in
lemma fieldConjugation_coherent (f g h : OneBoson) :
    ordinaryField g (fieldWeylCoherentInput g f h) =
      weylUnitary f (ordinaryField g (coherentFieldInput g h)+fieldConjugationShift f g • exponentialVector h) := by
  have ha : ordinaryAnnihilationRootInput g (fieldWeylCoherentInput g f h) = weylCoherentAnnihilationInput f g h :=
    Subtype.ext (fieldWeylCoherentInput_value g f h)
  have hc : ordinaryCreationRootInput g (fieldWeylCoherentInput g f h) = weylCoherentCreationInput f g h :=
    Subtype.ext (fieldWeylCoherentInput_value g f h)
  rw [ordinaryField_action,ha,hc,weyl_annihilation_coherent_intertwine,weyl_creation_coherent_intertwine,
    ← map_add,coherentField_action]
  congr 1
  change _ = _+ (⟪g,f⟫_ℂ+⟪f,g⟫_ℂ) • exponentialVector h
  module

lemma fieldWeightedWeyl_coherent_input (f g h : OneBoson) :
    ordinaryFieldHalfInput g (weylWeightedMap (1/2) (by norm_num) (by norm_num) f
      (coherentExponentialWeighted (1/2) (by norm_num) h)) = fieldWeylCoherentInput g f h := by
  apply Subtype.ext
  change numberDomainEmbedding (1/2) (by norm_num) (weylWeightedInput (1/2) (by norm_num) (by norm_num) f
      (coherentExponentialWeighted (1/2) (by norm_num) h)) = _
  rw [weylWeightedInput_embedding,numberDomainEmbedding_apply,coherentExponentialWeighted_ambient,
    fieldWeylCoherentInput_value]

set_option backward.isDefEq.respectTransparency.types false in
lemma fieldConjugation_half (f g : OneBoson) (u : NumberWeightedDomain Sector (1/2) (by norm_num)) :
    ordinaryFieldHalfMap g (weylWeightedMap (1/2) (by norm_num) (by norm_num) f u) =
      weylUnitary f (ordinaryFieldHalfMap g u+fieldConjugationShift f g • numberDomainEmbedding (1/2) (by norm_num) u) := by
  let L := (ordinaryFieldHalfMap g).comp (weylWeightedMap (1/2) (by norm_num) (by norm_num) f)
  let R := (weylUnitary f : Carrier →L[ℂ] Carrier).comp
    (ordinaryFieldHalfMap g+fieldConjugationShift f g • numberDomainEmbedding (1/2) _)
  have hE (h : OneBoson) : L (coherentExponentialWeighted (1/2) (by norm_num) h) =
      R (coherentExponentialWeighted (1/2) (by norm_num) h) := by
    change ordinaryField g (ordinaryFieldHalfInput g
      (weylWeightedMap (1/2) (by norm_num) (by norm_num) f (coherentExponentialWeighted (1/2) (by norm_num) h))) = _
    rw [fieldWeightedWeyl_coherent_input,fieldConjugation_coherent]
    change _ = weylUnitary f (ordinaryFieldHalfMap g (coherentExponentialWeighted (1/2) (by norm_num) h)+
      fieldConjugationShift f g • numberDomainEmbedding (1/2) (by norm_num) (coherentExponentialWeighted (1/2) (by norm_num) h))
    rw [ordinaryFieldHalfMap_coherent,numberDomainEmbedding_apply,coherentExponentialWeighted_ambient]
  have he : Set.EqOn L R (numberHalfCore : Set (NumberWeightedDomain Sector (1/2) (by norm_num))) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h,rfl⟩ := hx
      exact hE h
    | zero => simp only [map_zero]
    | add x y hx hy ihx ihy => simp only [map_add,ihx,ihy]
    | smul a x hx ih => simp only [map_smul,ih]
  exact (he.closure L.continuous R.continuous) (numberHalfCore_dense u)

set_option backward.isDefEq.respectTransparency.types false in
lemma fieldConjugation_half_graph (f g : OneBoson) (u : NumberWeightedDomain Sector (1/2) (by norm_num)) :
    (weylUnitary f (numberDomainEmbedding (1/2) (by norm_num) u),
     weylUnitary f (ordinaryFieldHalfMap g u+fieldConjugationShift f g • numberDomainEmbedding (1/2) (by norm_num) u)) ∈
      (ordinaryFieldClosure g).graph := by
  have hg := (LinearPMap.le_graph_of_le (ordinaryFieldClosure_extends g))
    (ordinaryFieldHalfMap_graph g (weylWeightedMap (1/2) (by norm_num) (by norm_num) f u))
  change (numberDomainEmbedding (1/2) (by norm_num) (weylWeightedInput (1/2) (by norm_num) (by norm_num) f u),
    ordinaryFieldHalfMap g (weylWeightedMap (1/2) (by norm_num) (by norm_num) f u)) ∈ (ordinaryFieldClosure g).graph at hg
  rw [weylWeightedInput_embedding,fieldConjugation_half] at hg
  exact hg

set_option backward.isDefEq.respectTransparency.types false in
lemma fieldConjugation_graph (f g : OneBoson) (u : (ordinaryFieldClosure g).domain) :
    (weylUnitary f u.val,weylUnitary f (ordinaryFieldClosure g u+fieldConjugationShift f g • u.val)) ∈
      (ordinaryFieldClosure g).graph := by
  let U : Carrier →L[ℂ] Carrier := weylUnitary f
  let F : Carrier × Carrier →L[ℂ] Carrier := ContinuousLinearMap.fst ℂ Carrier Carrier
  let G : Carrier × Carrier →L[ℂ] Carrier := ContinuousLinearMap.snd ℂ Carrier Carrier
  let P := (U.comp F).prod (U.comp (G+fieldConjugationShift f g • F))
  let S : Set (Carrier × Carrier) := {p | (U p.1,U (p.2+fieldConjugationShift f g • p.1)) ∈ (ordinaryFieldClosure g).graph}
  have hclosed : IsClosed S := (ordinaryFieldClosure_closed g).preimage P.continuous
  have hsub : ((ordinaryField g).graph : Set (Carrier × Carrier)) ⊆ S := by
    intro p hp
    obtain ⟨w,hw⟩ := (ordinaryField g).mem_graph_iff'.mp hp
    rw [← hw]
    let v := numberHalfGraphInput w
    have heJ : numberDomainEmbedding (1/2) (by norm_num) v = w.val := numberHalfGraphInput_embedding w
    have heA : ordinaryFieldHalfMap g v = ordinaryField g w := by
      change ordinaryField g (ordinaryFieldHalfInput g v) = ordinaryField g w
      congr 1
      exact Subtype.ext heJ
    have hg := fieldConjugation_half_graph f g v
    rw [heJ,heA] at hg
    exact hg
  have hp : (u.val,ordinaryFieldClosure g u) ∈ closure ((ordinaryField g).graph : Set (Carrier × Carrier)) := by
    change (u.val,ordinaryFieldClosure g u) ∈ (ordinaryField g).graph.topologicalClosure
    rw [ordinaryFieldClosure_graph]
    exact (ordinaryFieldClosure g).mem_graph u
  exact closure_minimal hsub hclosed hp

def fieldConjugationInput (f g : OneBoson) (u : (ordinaryFieldClosure g).domain) : (ordinaryFieldClosure g).domain :=
  ⟨weylUnitary f u.val,fieldClosure_graph_domain g (fieldConjugation_graph f g u)⟩

lemma fieldConjugationInput_value (f g : OneBoson) (u : (ordinaryFieldClosure g).domain) :
    (fieldConjugationInput f g u).val = weylUnitary f u.val := rfl

lemma fieldConjugation_action (f g : OneBoson) (u : (ordinaryFieldClosure g).domain) :
    ordinaryFieldClosure g (fieldConjugationInput f g u) =
      weylUnitary f (ordinaryFieldClosure g u+fieldConjugationShift f g • u.val) :=
  (ordinaryFieldClosure g).mem_graph_snd_inj ((ordinaryFieldClosure g).mem_graph (fieldConjugationInput f g u))
    (fieldConjugation_graph f g u) rfl

lemma weyl_field_conjugation (f g : OneBoson) (u : (ordinaryFieldClosure g).domain) :
    (weylUnitary f).symm (ordinaryFieldClosure g (fieldConjugationInput f g u)) =
      ordinaryFieldClosure g u+((2*(⟪f,g⟫_ℂ).re:ℝ):ℂ) • u.val := by
  rw [fieldConjugation_action,LinearIsometryEquiv.symm_apply_apply,fieldConjugationShift_real]

lemma weyl_field_domain_iff (f g : OneBoson) (u : Carrier) :
    weylUnitary f u ∈ (ordinaryFieldClosure g).domain ↔ u ∈ (ordinaryFieldClosure g).domain := by
  constructor
  · intro hu
    have hh := (fieldConjugationInput (-f) g ⟨weylUnitary f u,hu⟩).property
    change weylUnitary (-f) (weylUnitary f u) ∈ (ordinaryFieldClosure g).domain at hh
    rw [← weylUnitary_symm,LinearIsometryEquiv.symm_apply_apply] at hh
    exact hh
  · intro hu
    exact (fieldConjugationInput f g ⟨u,hu⟩).property

lemma weyl_field_domain_image (f g : OneBoson) :
    (weylUnitary f) '' ((ordinaryFieldClosure g).domain : Set Carrier) = ((ordinaryFieldClosure g).domain : Set Carrier) := by
  ext u
  constructor
  · rintro ⟨v,hv,rfl⟩
    exact (weyl_field_domain_iff f g v).mpr hv
  · intro hu
    refine ⟨weylUnitary (-f) u,(weyl_field_domain_iff (-f) g u).mpr hu,?_⟩
    rw [← weylUnitary_symm,LinearIsometryEquiv.apply_symm_apply]

end GW.Fock
