module
public import GW.Fock.FockWeylLipschitz
public import GW.Fock.FockFiberFields
public import GW.Fock.FockFieldConjugation
public import GW.Operators.BasicFractionalFree
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal
namespace GW.Fock

lemma weylUnitary_joint_continuous : Continuous (fun p : OneBoson × Carrier => weylUnitary p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := Metric.continuousAt_iff.mp (weylUnitary_strong_continuous p₀.2).continuousAt
    (ε/2) (by linarith)
  refine ⟨min δ (ε/2),lt_min hδ (by linarith),?_⟩
  intro p hp
  rw [Prod.dist_eq,max_lt_iff] at hp
  have hf : dist p.1 p₀.1 < δ := lt_of_lt_of_le hp.1 (min_le_left _ _)
  have hu : dist p.2 p₀.2 < ε/2 := lt_of_lt_of_le hp.2 (min_le_right _ _)
  have hm := hd hf
  have ht := dist_triangle (weylUnitary p.1 p.2) (weylUnitary p.1 p₀.2) (weylUnitary p₀.1 p₀.2)
  rw [(weylUnitary p.1).isometry.dist_eq] at ht
  linarith

def fiberWeylRep (b : GW.Space → OneBoson) (U : Physical) (x : GW.Space) : Carrier := weylUnitary (b x) (U x)

set_option backward.isDefEq.respectTransparency.types false in
lemma fiberWeylRep_stronglyMeasurable (b : GW.Space → OneBoson) (hb : StronglyMeasurable b) (U : Physical) :
    StronglyMeasurable (fiberWeylRep b U) := by
  have hp : StronglyMeasurable (fun x : GW.Space => (b x,U x)) := hb.prodMk (Lp.stronglyMeasurable U)
  have hh := weylUnitary_joint_continuous.comp_stronglyMeasurable hp
  convert! hh using 1 <;> rfl

lemma fiberWeylRep_memLp (b : GW.Space → OneBoson) (hb : StronglyMeasurable b) (U : Physical) :
    MemLp (fiberWeylRep b U) 2 (volume : Measure GW.Space) := by
  apply (Lp.memLp U).of_le_mul (c := 1) (fiberWeylRep_stronglyMeasurable b hb U).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  change ‖weylUnitary (b x) (U x)‖ ≤ 1*‖U x‖
  simp only [LinearIsometryEquiv.norm_map,one_mul] <;> exact le_rfl

def fiberWeylClass (b : GW.Space → OneBoson) (hb : StronglyMeasurable b) (U : Physical) : Physical :=
  (fiberWeylRep_memLp b hb U).toLp (fiberWeylRep b U)

lemma fiberWeylClass_ae (b : GW.Space → OneBoson) (hb : StronglyMeasurable b) (U : Physical) :
    fiberWeylClass b hb U =ᵐ[(volume : Measure GW.Space)] fiberWeylRep b U := MemLp.coeFn_toLp _

lemma fiberWeylClass_norm (b : GW.Space → OneBoson) (hb : StronglyMeasurable b) (U : Physical) :
    ‖fiberWeylClass b hb U‖ = ‖U‖ := by
  apply le_antisymm
  · have h : ‖fiberWeylClass b hb U‖ ≤ 1*‖U‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [fiberWeylClass_ae b hb U] with x hx
      rw [hx]
      change ‖weylUnitary (b x) (U x)‖ ≤ 1*‖U x‖
      simp only [LinearIsometryEquiv.norm_map,one_mul] <;> exact le_rfl
    simpa only [one_mul] using h
  · have h : ‖U‖ ≤ 1*‖fiberWeylClass b hb U‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [fiberWeylClass_ae b hb U] with x hx
      rw [hx]
      change ‖U x‖ ≤ 1*‖weylUnitary (b x) (U x)‖
      simp only [LinearIsometryEquiv.norm_map,one_mul] <;> exact le_rfl
    simpa only [one_mul] using h

def fiberWeylLinear (b : GW.Space → OneBoson) (hb : StronglyMeasurable b) : Physical →ₗ[ℂ] Physical where
  toFun := fiberWeylClass b hb
  map_add' U V := by
    apply Lp.ext
    filter_upwards [fiberWeylClass_ae b hb (U+V),fiberWeylClass_ae b hb U,fiberWeylClass_ae b hb V,
      Lp.coeFn_add U V,Lp.coeFn_add (fiberWeylClass b hb U) (fiberWeylClass b hb V)] with x h₁ h₂ h₃ h₄ h₅
    change fiberWeylClass b hb (U+V) x = (fiberWeylClass b hb U+fiberWeylClass b hb V) x
    rw [h₁,h₅,Pi.add_apply,h₂,h₃]
    change weylUnitary (b x) ((U+V) x) = weylUnitary (b x) (U x)+weylUnitary (b x) (V x)
    rw [show (U+V) x = U x+V x from h₄,map_add]
  map_smul' c U := by
    apply Lp.ext
    filter_upwards [fiberWeylClass_ae b hb (c • U),fiberWeylClass_ae b hb U,
      Lp.coeFn_smul c U,Lp.coeFn_smul c (fiberWeylClass b hb U)] with x h₁ h₂ h₃ h₄
    change fiberWeylClass b hb (c • U) x = (c • fiberWeylClass b hb U) x
    rw [h₁,h₄,Pi.smul_apply,h₂]
    change weylUnitary (b x) ((c • U) x) = c • weylUnitary (b x) (U x)
    rw [show (c • U) x = c • U x from h₃,map_smul]

def fiberWeylIsometry (b : GW.Space → OneBoson) (hb : StronglyMeasurable b) : Physical →ₗᵢ[ℂ] Physical where
  toLinearMap := fiberWeylLinear b hb
  norm_map' := fiberWeylClass_norm b hb

lemma fiberWeylClass_inverse_left (b : GW.Space → OneBoson) (hb : StronglyMeasurable b) (U : Physical) :
    fiberWeylClass (fun x => -b x) (continuous_neg.comp_stronglyMeasurable hb) (fiberWeylClass b hb U) = U := by
  apply Lp.ext
  filter_upwards [fiberWeylClass_ae (fun x => -b x) (continuous_neg.comp_stronglyMeasurable hb) (fiberWeylClass b hb U),
    fiberWeylClass_ae b hb U] with x hx hy
  rw [hx]
  change weylUnitary (-(b x)) (fiberWeylClass b hb U x) = U x
  rw [hy]
  change weylUnitary (-(b x)) (weylUnitary (b x) (U x)) = U x
  rw [← weylUnitary_symm,LinearIsometryEquiv.symm_apply_apply]

lemma fiberWeylClass_inverse_right (b : GW.Space → OneBoson) (hb : StronglyMeasurable b) (U : Physical) :
    fiberWeylClass b hb (fiberWeylClass (fun x => -b x) (continuous_neg.comp_stronglyMeasurable hb) U) = U := by
  apply Lp.ext
  filter_upwards [fiberWeylClass_ae b hb (fiberWeylClass (fun x => -b x) (continuous_neg.comp_stronglyMeasurable hb) U),
    fiberWeylClass_ae (fun x => -b x) (continuous_neg.comp_stronglyMeasurable hb) U] with x hx hy
  rw [hx]
  change weylUnitary (b x) (fiberWeylClass (fun x => -b x) (continuous_neg.comp_stronglyMeasurable hb) U x) = U x
  rw [hy]
  change weylUnitary (b x) (weylUnitary (-(b x)) (U x)) = U x
  rw [← weylUnitary_symm,LinearIsometryEquiv.apply_symm_apply]

def fiberWeylUnitary (b : GW.Space → OneBoson) (hb : StronglyMeasurable b) : Physical ≃ₗᵢ[ℂ] Physical :=
  LinearIsometryEquiv.ofSurjective (fiberWeylIsometry b hb) (fun U =>
    ⟨fiberWeylClass (fun x => -b x) (continuous_neg.comp_stronglyMeasurable hb) U,fiberWeylClass_inverse_right b hb U⟩)

lemma fiberWeylUnitary_ae (b : GW.Space → OneBoson) (hb : StronglyMeasurable b) (U : Physical) :
    fiberWeylUnitary b hb U =ᵐ[(volume : Measure GW.Space)] fun x => weylUnitary (b x) (U x) :=
  fiberWeylClass_ae b hb U

lemma fiberWeylUnitary_symm_apply (b : GW.Space → OneBoson) (hb : StronglyMeasurable b) (U : Physical) :
    (fiberWeylUnitary b hb).symm U = fiberWeylUnitary (fun x => -b x) (continuous_neg.comp_stronglyMeasurable hb) U := by
  apply (fiberWeylUnitary b hb).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact (fiberWeylClass_inverse_right b hb U).symm


def fiberWeylEssBound (b : GW.Space → OneBoson) : ℝ :=
  (eLpNormEssSup b (volume : Measure GW.Space)).toReal

lemma fiberWeylEssBound_nonneg (b : GW.Space → OneBoson) : 0 ≤ fiberWeylEssBound b :=
  ENNReal.toReal_nonneg

set_option backward.isDefEq.respectTransparency.types false in
lemma fiberWeylEssBound_ae (b : GW.Space → OneBoson)
    (hfin : eLpNormEssSup b (volume : Measure GW.Space) < ⊤) :
    ∀ᵐ x ∂(volume : Measure GW.Space), ‖b x‖ ≤ fiberWeylEssBound b := by
  filter_upwards [ae_le_eLpNormEssSup (f := b) (μ := (volume : Measure GW.Space))] with x hx
  have h := ENNReal.toReal_mono hfin.ne hx
  simpa only [toReal_eNorm, fiberWeylEssBound] using h

def fiberWeylGraphRep (r : ℝ) (hr : 0 ≤ r) (hs : r ≤ 1)
    (b : GW.Space → OneBoson) (G : Lp (NumberWeightedDomain Sector r hr) 2 (volume : Measure GW.Space))
    (x : GW.Space) : NumberWeightedDomain Sector r hr := weylWeightedMap r hr hs (b x) (G x)

set_option backward.isDefEq.respectTransparency.types false in
lemma fiberWeylGraphRep_stronglyMeasurable (r : ℝ) (hr : 0 ≤ r) (hs : r ≤ 1)
    (b : GW.Space → OneBoson) (hb : StronglyMeasurable b)
    (G : Lp (NumberWeightedDomain Sector r hr) 2 (volume : Measure GW.Space)) :
    StronglyMeasurable (fiberWeylGraphRep r hr hs b G) := by
  have hp : StronglyMeasurable (fun x : GW.Space => (b x,G x)) := hb.prodMk (Lp.stronglyMeasurable G)
  have hh := (weylWeightedMap_joint_continuous r hr hs).comp_stronglyMeasurable hp
  convert! hh using 1 <;> rfl

lemma fiberWeylGraphRep_bound (r : ℝ) (hr : 0 ≤ r) (hs : r ≤ 1)
    (b : GW.Space → OneBoson) (M : ℝ)
    (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖b x‖ ≤ M)
    (G : Lp (NumberWeightedDomain Sector r hr) 2 (volume : Measure GW.Space)) :
    ∀ᵐ x ∂(volume : Measure GW.Space), ‖fiberWeylGraphRep r hr hs b G x‖ ≤ (1+M)^(2*r)*‖G x‖ := by
  filter_upwards [hM] with x hx
  exact (weylWeightedInput_norm r hr hs (b x) (G x)).trans
    (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (by positivity) (add_le_add le_rfl hx) (by positivity)) (norm_nonneg _))

lemma fiberWeylGraphRep_memLp (r : ℝ) (hr : 0 ≤ r) (hs : r ≤ 1)
    (b : GW.Space → OneBoson) (hb : StronglyMeasurable b) (M : ℝ)
    (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖b x‖ ≤ M)
    (G : Lp (NumberWeightedDomain Sector r hr) 2 (volume : Measure GW.Space)) :
    MemLp (fiberWeylGraphRep r hr hs b G) 2 (volume : Measure GW.Space) :=
  (Lp.memLp G).of_le_mul (fiberWeylGraphRep_stronglyMeasurable r hr hs b hb G).aestronglyMeasurable
    (fiberWeylGraphRep_bound r hr hs b M hM G)

def fiberWeylGraphClass (r : ℝ) (hr : 0 ≤ r) (hs : r ≤ 1)
    (b : GW.Space → OneBoson) (hb : StronglyMeasurable b) (M : ℝ)
    (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖b x‖ ≤ M)
    (G : Lp (NumberWeightedDomain Sector r hr) 2 (volume : Measure GW.Space)) :
    Lp (NumberWeightedDomain Sector r hr) 2 (volume : Measure GW.Space) :=
  (fiberWeylGraphRep_memLp r hr hs b hb M hM G).toLp (fiberWeylGraphRep r hr hs b G)

lemma fiberWeylGraphClass_ae (r : ℝ) (hr : 0 ≤ r) (hs : r ≤ 1)
    (b : GW.Space → OneBoson) (hb : StronglyMeasurable b) (M : ℝ)
    (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖b x‖ ≤ M)
    (G : Lp (NumberWeightedDomain Sector r hr) 2 (volume : Measure GW.Space)) :
    fiberWeylGraphClass r hr hs b hb M hM G =ᵐ[(volume : Measure GW.Space)]
      fiberWeylGraphRep r hr hs b G := MemLp.coeFn_toLp _

lemma fiberWeylGraphClass_bound (r : ℝ) (hr : 0 ≤ r) (hs : r ≤ 1)
    (b : GW.Space → OneBoson) (hb : StronglyMeasurable b) (M : ℝ)
    (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖b x‖ ≤ M)
    (G : Lp (NumberWeightedDomain Sector r hr) 2 (volume : Measure GW.Space)) :
    ‖fiberWeylGraphClass r hr hs b hb M hM G‖ ≤ (1+M)^(2*r)*‖G‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [fiberWeylGraphClass_ae r hr hs b hb M hM G,
    fiberWeylGraphRep_bound r hr hs b M hM G] with x hx hy
  rw [hx]
  exact hy


def fiberWeylGraphLinear (r : ℝ) (hr : 0 ≤ r) (hs : r ≤ 1)
    (b : GW.Space → OneBoson) (hb : StronglyMeasurable b) (M : ℝ)
    (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖b x‖ ≤ M) :
    Lp (NumberWeightedDomain Sector r hr) 2 (volume : Measure GW.Space) →ₗ[ℂ]
      Lp (NumberWeightedDomain Sector r hr) 2 (volume : Measure GW.Space) where
  toFun := fiberWeylGraphClass r hr hs b hb M hM
  map_add' U V := by
    apply Lp.ext
    filter_upwards [fiberWeylGraphClass_ae r hr hs b hb M hM (U+V),
      fiberWeylGraphClass_ae r hr hs b hb M hM U,fiberWeylGraphClass_ae r hr hs b hb M hM V,
      Lp.coeFn_add U V,Lp.coeFn_add (fiberWeylGraphClass r hr hs b hb M hM U)
        (fiberWeylGraphClass r hr hs b hb M hM V)] with x h₁ h₂ h₃ h₄ h₅
    change fiberWeylGraphClass r hr hs b hb M hM (U+V) x =
      (fiberWeylGraphClass r hr hs b hb M hM U+fiberWeylGraphClass r hr hs b hb M hM V) x
    rw [h₁,h₅,Pi.add_apply,h₂,h₃]
    change weylWeightedMap r hr hs (b x) ((U+V) x) =
      weylWeightedMap r hr hs (b x) (U x)+weylWeightedMap r hr hs (b x) (V x)
    rw [show (U+V) x = U x+V x from h₄,map_add]
  map_smul' c U := by
    apply Lp.ext
    filter_upwards [fiberWeylGraphClass_ae r hr hs b hb M hM (c • U),
      fiberWeylGraphClass_ae r hr hs b hb M hM U,Lp.coeFn_smul c U,
      Lp.coeFn_smul c (fiberWeylGraphClass r hr hs b hb M hM U)] with x h₁ h₂ h₃ h₄
    change fiberWeylGraphClass r hr hs b hb M hM (c • U) x =
      (c • fiberWeylGraphClass r hr hs b hb M hM U) x
    rw [h₁,h₄,Pi.smul_apply,h₂]
    change weylWeightedMap r hr hs (b x) ((c • U) x) = c • weylWeightedMap r hr hs (b x) (U x)
    rw [show (c • U) x = c • U x from h₃,map_smul]

def fiberWeylGraphMap (r : ℝ) (hr : 0 ≤ r) (hs : r ≤ 1)
    (b : GW.Space → OneBoson) (hb : StronglyMeasurable b) (M : ℝ)
    (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖b x‖ ≤ M) :
    Lp (NumberWeightedDomain Sector r hr) 2 (volume : Measure GW.Space) →L[ℂ]
      Lp (NumberWeightedDomain Sector r hr) 2 (volume : Measure GW.Space) :=
  (fiberWeylGraphLinear r hr hs b hb M hM).mkContinuous ((1+M)^(2*r))
    (fiberWeylGraphClass_bound r hr hs b hb M hM)

set_option backward.isDefEq.respectTransparency.types false in
lemma fiberWeylGraphMap_inclusion (r : ℝ) (hr : 0 ≤ r) (hs : r ≤ 1)
    (b : GW.Space → OneBoson) (hb : StronglyMeasurable b) (M : ℝ)
    (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖b x‖ ≤ M)
    (G : Lp (NumberWeightedDomain Sector r hr) 2 (volume : Measure GW.Space)) :
    numberGraphIncludeL2 (volume : Measure GW.Space) Sector r hr (fiberWeylGraphMap r hr hs b hb M hM G) =
      fiberWeylUnitary b hb (numberGraphIncludeL2 (volume : Measure GW.Space) Sector r hr G) := by
  apply Lp.ext
  filter_upwards [(numberDomainInclusion Sector r hr).coeFn_compLp
      (fiberWeylGraphMap r hr hs b hb M hM G),
    (numberDomainInclusion Sector r hr).coeFn_compLp G,
    fiberWeylGraphClass_ae r hr hs b hb M hM G,
    fiberWeylUnitary_ae b hb (numberGraphIncludeL2 (volume : Measure GW.Space) Sector r hr G)] with x h₁ h₂ h₃ h₄
  change numberGraphIncludeL2 (volume : Measure GW.Space) Sector r hr
    (fiberWeylGraphMap r hr hs b hb M hM G) x =
    fiberWeylUnitary b hb (numberGraphIncludeL2 (volume : Measure GW.Space) Sector r hr G) x
  rw [h₄]
  change numberGraphIncludeL2 (volume : Measure GW.Space) Sector r hr
    (fiberWeylGraphMap r hr hs b hb M hM G) x =
    weylUnitary (b x) (numberGraphIncludeL2 (volume : Measure GW.Space) Sector r hr G x)
  rw [show numberGraphIncludeL2 (volume : Measure GW.Space) Sector r hr
      (fiberWeylGraphMap r hr hs b hb M hM G) x =
      numberDomainInclusion Sector r hr (fiberWeylGraphClass r hr hs b hb M hM G x) from h₁,
    h₃]
  change numberDomainEmbedding r hr (weylWeightedInput r hr hs (b x) (G x)) = _
  rw [weylWeightedInput_embedding]
  congr 1
  exact h₂.symm


def fiberWeylPhysicalGraphMap (r : ℝ) (hr : 0 ≤ r) (hs : r ≤ 1)
    (b : GW.Space → OneBoson) (hb : StronglyMeasurable b) (M : ℝ)
    (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖b x‖ ≤ M) :
    PhysicalNumberDomain r hr →L[ℂ] PhysicalNumberDomain r hr :=
  (physicalNumberGraphBochnerUnitary r hr).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((fiberWeylGraphMap r hr hs b hb M hM).comp
      (physicalNumberGraphBochnerUnitary r hr).symm.toContinuousLinearEquiv.toContinuousLinearMap)

set_option backward.isDefEq.respectTransparency.types false in
lemma fiberWeylPhysicalGraphMap_inclusion (r : ℝ) (hr : 0 ≤ r) (hs : r ≤ 1)
    (b : GW.Space → OneBoson) (hb : StronglyMeasurable b) (M : ℝ)
    (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖b x‖ ≤ M)
    (U : PhysicalNumberDomain r hr) :
    (show Physical from (show (physicalShiftedNumberPower r).domain from
      fiberWeylPhysicalGraphMap r hr hs b hb M hM U)) =
      fiberWeylUnitary b hb (show Physical from (show (physicalShiftedNumberPower r).domain from U)) := by
  obtain ⟨G,rfl⟩ := (physicalNumberGraphBochnerUnitary r hr).surjective U
  change (show Physical from (show (physicalShiftedNumberPower r).domain from
    physicalNumberGraphBochnerUnitary r hr (fiberWeylGraphMap r hr hs b hb M hM
      ((physicalNumberGraphBochnerUnitary r hr).symm (physicalNumberGraphBochnerUnitary r hr G))))) = _
  rw [LinearIsometryEquiv.symm_apply_apply]
  rw [numberGraphBochnerUnitary_inclusion,numberGraphBochnerUnitary_inclusion]
  exact fiberWeylGraphMap_inclusion r hr hs b hb M hM G

lemma fiberWeylPhysicalGraphMap_bound (r : ℝ) (hr : 0 ≤ r) (hs : r ≤ 1)
    (b : GW.Space → OneBoson) (hb : StronglyMeasurable b) (M : ℝ)
    (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖b x‖ ≤ M)
    (U : PhysicalNumberDomain r hr) :
    ‖fiberWeylPhysicalGraphMap r hr hs b hb M hM U‖ ≤ (1+M)^(2*r)*‖U‖ := by
  change ‖physicalNumberGraphBochnerUnitary r hr
    (fiberWeylGraphMap r hr hs b hb M hM ((physicalNumberGraphBochnerUnitary r hr).symm U))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  have h := fiberWeylGraphClass_bound r hr hs b hb M hM ((physicalNumberGraphBochnerUnitary r hr).symm U)
  rw [LinearIsometryEquiv.norm_map] at h
  exact h

set_option backward.isDefEq.respectTransparency.types false in
lemma fiberWeyl_shifted_domain (r : ℝ) (hr : 0 ≤ r) (hs : r ≤ 1)
    (b : GW.Space → OneBoson) (hb : StronglyMeasurable b) (M : ℝ)
    (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖b x‖ ≤ M)
    (U : Physical) (hU : U ∈ (physicalShiftedNumberPower r).domain) :
    fiberWeylUnitary b hb U ∈ (physicalShiftedNumberPower r).domain := by
  let V : PhysicalNumberDomain r hr := show (physicalShiftedNumberPower r).domain from ⟨U,hU⟩
  have he := fiberWeylPhysicalGraphMap_inclusion r hr hs b hb M hM V
  exact he ▸ (show (physicalShiftedNumberPower r).domain from
    fiberWeylPhysicalGraphMap r hr hs b hb M hM V).property


lemma physicalNumberPower_domains_eq (r : ℝ) (hr : 0 < r) :
    (physicalNumberPower r).domain = (physicalShiftedNumberPower r).domain := by
  rw [physicalNumberPower_domain_map,physicalShiftedNumberPower_domain_map,
    numberPower_domain_eq (fun n => Lp (Sector n) 2 (volume : Measure GW.Space)) r hr]

lemma fiberWeyl_shifted_domain_iff (r : ℝ) (hr : 0 ≤ r) (hs : r ≤ 1)
    (b : GW.Space → OneBoson) (hb : StronglyMeasurable b) (M : ℝ)
    (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖b x‖ ≤ M) (U : Physical) :
    fiberWeylUnitary b hb U ∈ (physicalShiftedNumberPower r).domain ↔
      U ∈ (physicalShiftedNumberPower r).domain := by
  constructor
  · intro h
    have hn : ∀ᵐ x ∂(volume : Measure GW.Space), ‖-b x‖ ≤ M := by
      simpa only [norm_neg] using hM
    have hh := fiberWeyl_shifted_domain r hr hs (fun x => -b x)
      (continuous_neg.comp_stronglyMeasurable hb) M hn (fiberWeylUnitary b hb U) h
    change fiberWeylClass (fun x => -b x) (continuous_neg.comp_stronglyMeasurable hb)
      (fiberWeylClass b hb U) ∈ _ at hh
    rw [fiberWeylClass_inverse_left] at hh
    exact hh
  · exact fiberWeyl_shifted_domain r hr hs b hb M hM U

lemma fiberWeyl_number_domain_iff (r : ℝ) (hr : 0 ≤ r) (hs : r ≤ 1)
    (b : GW.Space → OneBoson) (hb : StronglyMeasurable b)
    (hfin : eLpNormEssSup b (volume : Measure GW.Space) < ⊤) (U : Physical) :
    fiberWeylUnitary b hb U ∈ (physicalNumberPower r).domain ↔
      U ∈ (physicalNumberPower r).domain := by
  rcases hr.eq_or_lt with (rfl | hp)
  · rw [physicalNumberPower_zero,LinearMap.toPMap_domain]
    exact iff_of_true Submodule.mem_top Submodule.mem_top
  · rw [physicalNumberPower_domains_eq r hp]
    exact fiberWeyl_shifted_domain_iff r hp.le hs b hb (fiberWeylEssBound b)
      (fiberWeylEssBound_ae b hfin) U

set_option backward.isDefEq.respectTransparency.types false in
lemma fiberWeyl_shifted_bound (r : ℝ) (hr : 0 ≤ r) (hs : r ≤ 1)
    (b : GW.Space → OneBoson) (hb : StronglyMeasurable b)
    (hfin : eLpNormEssSup b (volume : Measure GW.Space) < ⊤)
    (U : (physicalShiftedNumberPower r).domain) :
    ‖physicalShiftedNumberPower r
      ⟨fiberWeylUnitary b hb U.val,
        fiberWeyl_shifted_domain r hr hs b hb (fiberWeylEssBound b) (fiberWeylEssBound_ae b hfin) U.val U.property⟩‖ ≤
      (1+fiberWeylEssBound b)^(2*r)*‖physicalShiftedNumberPower r U‖ := by
  let V : PhysicalNumberDomain r hr := U
  let T := fiberWeylPhysicalGraphMap r hr hs b hb (fiberWeylEssBound b) (fiberWeylEssBound_ae b hfin)
  have he : (show (physicalShiftedNumberPower r).domain from T V) =
      ⟨fiberWeylUnitary b hb U.val,
        fiberWeyl_shifted_domain r hr hs b hb (fiberWeylEssBound b) (fiberWeylEssBound_ae b hfin) U.val U.property⟩ :=
    Subtype.ext (fiberWeylPhysicalGraphMap_inclusion r hr hs b hb (fiberWeylEssBound b) (fiberWeylEssBound_ae b hfin) V)
  have hn := fiberWeylPhysicalGraphMap_bound r hr hs b hb (fiberWeylEssBound b) (fiberWeylEssBound_ae b hfin) V
  change ‖physicalShiftedNumberPower r (show (physicalShiftedNumberPower r).domain from T V)‖ ≤
    (1+fiberWeylEssBound b)^(2*r)*‖physicalShiftedNumberPower r U‖ at hn
  rw [he] at hn
  exact hn


lemma numberDomainEmbedding_injective (r : ℝ) (hr : 0 ≤ r) :
    Function.Injective (numberDomainEmbedding r hr) := by
  intro u v h
  apply Subtype.ext
  exact (numberDomainEmbedding_apply r hr u).symm.trans
    (h.trans (numberDomainEmbedding_apply r hr v))

lemma fiberOrdinaryField_eq (f : OneBoson) (u : FiberRootDomain) :
    fiberOrdinaryAnnihilator f u+fiberOrdinaryCreator f u = ordinaryFieldHalfMap f u := by
  change _ = ordinaryField f (ordinaryFieldHalfInput f u)
  rw [ordinaryField_action]
  have ha : (⟨(fiberOrdinaryRootInput u).val,
      (ordinaryAnnihilationRootInput f (fiberOrdinaryRootInputUnshifted u)).property⟩ : (ordinaryAnnihilation f).domain) =
      ordinaryAnnihilationRootInput f (ordinaryFieldHalfInput f u) :=
    Subtype.ext (numberDomainEmbedding_apply (1/2) (by norm_num) u).symm
  have hc : (⟨(fiberOrdinaryRootInput u).val,
      creation_mem_shiftedRoot ordinarySectorKernel (ordinaryKernel f) (fiberOrdinaryRootInput u)⟩ : (ordinaryCreation f).domain) =
      ordinaryCreationRootInput f (ordinaryFieldHalfInput f u) :=
    Subtype.ext (numberDomainEmbedding_apply (1/2) (by norm_num) u).symm
  exact congrArg₂ (fun a c : Carrier => a+c)
    (congrArg (ordinaryAnnihilation f).toFun ha) (congrArg (ordinaryCreation f).toFun hc)

set_option backward.isDefEq.respectTransparency.types false in
lemma fiberGeneralizedField_ae (F : GW.Space → OneBoson) (hF : StronglyMeasurable F)
    (M : ℝ) (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M)
    (U : (physicalNumberPower (1/2)).domain)
    (G : Lp FiberRootDomain 2 (volume : Measure GW.Space))
    (hG : (fun x => numberDomainEmbedding (1/2) (by norm_num) (G x)) =ᵐ[volume] U.val) :
    generalizedField (fiberKernel F hF.aestronglyMeasurable hM) U =ᵐ[volume]
      fun x => ordinaryFieldHalfMap (F x) (G x) := by
  obtain ⟨g,hg,hl,hi,hc,ha,hcl,hal⟩ := multiplicationKernel_fiberwise F hF.aestronglyMeasurable hM U
  have he : generalizedField (fiberKernel F hF.aestronglyMeasurable hM) U =
      generalizedAnnihilation (fiberKernel F hF.aestronglyMeasurable hM)
        (fiberGeneralizedAnnihilationRootInput (fiberKernel F hF.aestronglyMeasurable hM) U)+
      generalizedCreation (fiberKernel F hF.aestronglyMeasurable hM)
        (generalizedCreationRootInput (fiberKernel F hF.aestronglyMeasurable hM) U) := by
    rw [generalizedField_action]
    congr 1
  rw [he]
  filter_upwards [hi,hG,hc,ha,Lp.coeFn_add
    (generalizedAnnihilation (fiberKernel F hF.aestronglyMeasurable hM)
      (fiberGeneralizedAnnihilationRootInput (fiberKernel F hF.aestronglyMeasurable hM) U))
    (generalizedCreation (fiberKernel F hF.aestronglyMeasurable hM)
      (generalizedCreationRootInput (fiberKernel F hF.aestronglyMeasurable hM) U))] with x hi hG hc ha hadd
  have hgg : g x = G x := by
    apply numberDomainEmbedding_injective (1/2) (by norm_num)
    exact hi.trans hG.symm
  rw [hadd]
  simp only [Pi.add_apply]
  rw [ha,hc,hgg,fiberOrdinaryField_eq]


def fiberScalarRep (c : GW.Space → ℂ) (U : Physical) (x : GW.Space) : Carrier := c x • U x

lemma fiberScalarRep_memLp (c : GW.Space → ℂ) (hc : StronglyMeasurable c) (C : ℝ)
    (hC : ∀ᵐ x ∂(volume : Measure GW.Space), ‖c x‖ ≤ C) (U : Physical) :
    MemLp (fiberScalarRep c U) 2 (volume : Measure GW.Space) := by
  apply (Lp.memLp U).of_le_mul (hc.smul (Lp.stronglyMeasurable U)).aestronglyMeasurable
  filter_upwards [hC] with x hx
  change ‖c x • U x‖ ≤ C*‖U x‖
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

def fiberScalarClass (c : GW.Space → ℂ) (hc : StronglyMeasurable c) (C : ℝ)
    (hC : ∀ᵐ x ∂(volume : Measure GW.Space), ‖c x‖ ≤ C) (U : Physical) : Physical :=
  (fiberScalarRep_memLp c hc C hC U).toLp (fiberScalarRep c U)

lemma fiberScalarClass_ae (c : GW.Space → ℂ) (hc : StronglyMeasurable c) (C : ℝ)
    (hC : ∀ᵐ x ∂(volume : Measure GW.Space), ‖c x‖ ≤ C) (U : Physical) :
    fiberScalarClass c hc C hC U =ᵐ[(volume : Measure GW.Space)] fiberScalarRep c U := MemLp.coeFn_toLp _

lemma fiberScalarClass_bound (c : GW.Space → ℂ) (hc : StronglyMeasurable c) (C : ℝ)
    (hC : ∀ᵐ x ∂(volume : Measure GW.Space), ‖c x‖ ≤ C) (U : Physical) :
    ‖fiberScalarClass c hc C hC U‖ ≤ C*‖U‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [fiberScalarClass_ae c hc C hC U,hC] with x hx hy
  rw [hx]
  change ‖c x • U x‖ ≤ C*‖U x‖
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right hy (norm_nonneg _)

def fiberScalarLinear (c : GW.Space → ℂ) (hc : StronglyMeasurable c) (C : ℝ)
    (hC : ∀ᵐ x ∂(volume : Measure GW.Space), ‖c x‖ ≤ C) : Physical →ₗ[ℂ] Physical where
  toFun := fiberScalarClass c hc C hC
  map_add' U V := by
    apply Lp.ext
    filter_upwards [fiberScalarClass_ae c hc C hC (U+V),fiberScalarClass_ae c hc C hC U,
      fiberScalarClass_ae c hc C hC V,Lp.coeFn_add U V,
      Lp.coeFn_add (fiberScalarClass c hc C hC U) (fiberScalarClass c hc C hC V)] with x h₁ h₂ h₃ h₄ h₅
    change fiberScalarClass c hc C hC (U+V) x = (fiberScalarClass c hc C hC U+fiberScalarClass c hc C hC V) x
    rw [h₁,h₅,Pi.add_apply,h₂,h₃]
    change c x • ((U+V) x) = c x • U x+c x • V x
    rw [show (U+V) x = U x+V x from h₄,smul_add]
  map_smul' a U := by
    apply Lp.ext
    filter_upwards [fiberScalarClass_ae c hc C hC (a • U),fiberScalarClass_ae c hc C hC U,
      Lp.coeFn_smul a U,Lp.coeFn_smul a (fiberScalarClass c hc C hC U)] with x h₁ h₂ h₃ h₄
    change fiberScalarClass c hc C hC (a • U) x = (a • fiberScalarClass c hc C hC U) x
    rw [h₁,h₄,Pi.smul_apply,h₂]
    change c x • ((a • U) x) = a • (c x • U x)
    rw [show (a • U) x = a • U x from h₃,smul_comm]

def fiberScalarMap (c : GW.Space → ℂ) (hc : StronglyMeasurable c) (C : ℝ)
    (hC : ∀ᵐ x ∂(volume : Measure GW.Space), ‖c x‖ ≤ C) : Physical →L[ℂ] Physical :=
  (fiberScalarLinear c hc C hC).mkContinuous C (fiberScalarClass_bound c hc C hC)


lemma fiberFieldShift_stronglyMeasurable (b g : GW.Space → OneBoson)
    (hb : StronglyMeasurable b) (hg : StronglyMeasurable g) :
    StronglyMeasurable (fun x => fieldConjugationShift (b x) (g x)) :=
  (hg.inner hb).add (hb.inner hg)

lemma fiberFieldShift_bound (b g : GW.Space → OneBoson) (Mb Mg : ℝ) (hMb : 0 ≤ Mb) (hMg : 0 ≤ Mg)
    (hb : ∀ᵐ x ∂(volume : Measure GW.Space), ‖b x‖ ≤ Mb)
    (hg : ∀ᵐ x ∂(volume : Measure GW.Space), ‖g x‖ ≤ Mg) :
    ∀ᵐ x ∂(volume : Measure GW.Space), ‖fieldConjugationShift (b x) (g x)‖ ≤ 2*Mb*Mg := by
  filter_upwards [hb,hg] with x hb hg
  calc
    _ ≤ ‖⟪g x,b x⟫_ℂ‖+‖⟪b x,g x⟫_ℂ‖ := norm_add_le _ _
    _ ≤ ‖g x‖*‖b x‖+‖b x‖*‖g x‖ := add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ Mg*Mb+Mb*Mg := add_le_add (mul_le_mul hg hb (norm_nonneg _) hMg)
      (mul_le_mul hb hg (norm_nonneg _) hMb)
    _ = _ := by ring

def fiberFieldShiftMap (b g : GW.Space → OneBoson) (hb : StronglyMeasurable b) (hg : StronglyMeasurable g)
    (Mb Mg : ℝ) (hMb : 0 ≤ Mb) (hMg : 0 ≤ Mg)
    (hB : ∀ᵐ x ∂(volume : Measure GW.Space), ‖b x‖ ≤ Mb)
    (hG : ∀ᵐ x ∂(volume : Measure GW.Space), ‖g x‖ ≤ Mg) : Physical →L[ℂ] Physical :=
  fiberScalarMap (fun x => fieldConjugationShift (b x) (g x)) (fiberFieldShift_stronglyMeasurable b g hb hg)
    (2*Mb*Mg) (fiberFieldShift_bound b g Mb Mg hMb hMg hB hG)

lemma fiberFieldShiftMap_ae (b g : GW.Space → OneBoson) (hb : StronglyMeasurable b) (hg : StronglyMeasurable g)
    (Mb Mg : ℝ) (hMb : 0 ≤ Mb) (hMg : 0 ≤ Mg)
    (hB : ∀ᵐ x ∂(volume : Measure GW.Space), ‖b x‖ ≤ Mb)
    (hG : ∀ᵐ x ∂(volume : Measure GW.Space), ‖g x‖ ≤ Mg) (U : Physical) :
    fiberFieldShiftMap b g hb hg Mb Mg hMb hMg hB hG U =ᵐ[volume]
      fun x => ((2*(⟪b x,g x⟫_ℂ).re:ℝ):ℂ) • U x := by
  have hh := fiberScalarClass_ae (fun x => fieldConjugationShift (b x) (g x))
    (fiberFieldShift_stronglyMeasurable b g hb hg) (2*Mb*Mg)
    (fiberFieldShift_bound b g Mb Mg hMb hMg hB hG) U
  filter_upwards [hh] with x hx
  exact hx.trans (congrArg (fun c : ℂ => c • U x) (fieldConjugationShift_real (b x) (g x)))

set_option backward.isDefEq.respectTransparency.types false in
lemma fiberWeylGraphClass_ambient_ae (b : GW.Space → OneBoson) (hb : StronglyMeasurable b) (M : ℝ)
    (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖b x‖ ≤ M)
    (U : Physical) (G : Lp FiberRootDomain 2 (volume : Measure GW.Space))
    (hG : (fun x => numberDomainEmbedding (1/2) (by norm_num) (G x)) =ᵐ[volume] U) :
    (fun x => numberDomainEmbedding (1/2) (by norm_num)
      (fiberWeylGraphClass (1/2) (by norm_num) (by norm_num) b hb M hM G x)) =ᵐ[volume]
        fiberWeylUnitary b hb U := by
  filter_upwards [fiberWeylGraphClass_ae (1/2) (by norm_num) (by norm_num) b hb M hM G,
    hG,fiberWeylUnitary_ae b hb U] with x hx hy hz
  rw [hx,hz]
  change numberDomainEmbedding (1/2) (by norm_num)
    (weylWeightedInput (1/2) (by norm_num) (by norm_num) (b x) (G x)) = _
  rw [weylWeightedInput_embedding,hy]


def fiberWeylRootInput (b : GW.Space → OneBoson) (hb : StronglyMeasurable b)
    (hfin : eLpNormEssSup b (volume : Measure GW.Space) < ⊤)
    (U : (physicalNumberPower (1/2)).domain) : (physicalNumberPower (1/2)).domain :=
  ⟨fiberWeylUnitary b hb U.val,
    (fiberWeyl_number_domain_iff (1/2) (by norm_num) (by norm_num) b hb hfin U.val).mpr U.property⟩

set_option backward.isDefEq.respectTransparency.types false in
lemma fiberRootRepresentative_original_ae (U : (physicalNumberPower (1/2)).domain) :
    (fun x => numberDomainEmbedding (1/2) (by norm_num)
      (fiberRootRepresentative (fiberPhysicalFromUnshifted U) x)) =ᵐ[volume] U.val := by
  have hh := fiberRootRepresentative_ambient (fiberPhysicalFromUnshifted U)
  have he := fiberPhysicalFromUnshifted_value U
  filter_upwards [hh] with x hx
  exact hx.trans (congrArg (fun V : Physical => V x) he)

set_option backward.isDefEq.respectTransparency.types false in
lemma fiberWeyl_field_action (b g : GW.Space → OneBoson) (hb : StronglyMeasurable b) (hg : StronglyMeasurable g)
    (hbf : eLpNormEssSup b (volume : Measure GW.Space) < ⊤)
    (hgf : eLpNormEssSup g (volume : Measure GW.Space) < ⊤)
    (U : (physicalNumberPower (1/2)).domain) :
    generalizedField (fiberKernel g hg.aestronglyMeasurable (fiberWeylEssBound_ae g hgf))
      (fiberWeylRootInput b hb hbf U) =
    fiberWeylUnitary b hb
      (generalizedField (fiberKernel g hg.aestronglyMeasurable (fiberWeylEssBound_ae g hgf)) U+
        fiberFieldShiftMap b g hb hg (fiberWeylEssBound b) (fiberWeylEssBound g)
          (fiberWeylEssBound_nonneg b) (fiberWeylEssBound_nonneg g)
          (fiberWeylEssBound_ae b hbf) (fiberWeylEssBound_ae g hgf) U.val) := by
  let Mb := fiberWeylEssBound b
  let Mg := fiberWeylEssBound g
  let hB := fiberWeylEssBound_ae b hbf
  let hG := fiberWeylEssBound_ae g hgf
  let K := fiberKernel g hg.aestronglyMeasurable hG
  let S := fiberFieldShiftMap b g hb hg Mb Mg (fiberWeylEssBound_nonneg b) (fiberWeylEssBound_nonneg g) hB hG
  let G := fiberRootRepresentative (fiberPhysicalFromUnshifted U)
  let H := fiberWeylGraphClass (1/2) (by norm_num) (by norm_num) b hb Mb hB G
  let V := fiberWeylRootInput b hb hbf U
  have ha := fiberRootRepresentative_original_ae U
  have hH : (fun x => numberDomainEmbedding (1/2) (by norm_num) (H x)) =ᵐ[volume] V.val :=
    fiberWeylGraphClass_ambient_ae b hb Mb hB U.val G ha
  have hl := fiberGeneralizedField_ae g hg Mg hG V H hH
  have hr := fiberGeneralizedField_ae g hg Mg hG U G ha
  have hs := fiberScalarClass_ae (fun x => fieldConjugationShift (b x) (g x))
    (fiberFieldShift_stronglyMeasurable b g hb hg) (2*Mb*Mg)
    (fiberFieldShift_bound b g Mb Mg (fiberWeylEssBound_nonneg b) (fiberWeylEssBound_nonneg g) hB hG) U.val
  have hw := fiberWeylUnitary_ae b hb (generalizedField K U+S U.val)
  have hc := fiberWeylGraphClass_ae (1/2) (by norm_num) (by norm_num) b hb Mb hB G
  change generalizedField K V = fiberWeylUnitary b hb (generalizedField K U+S U.val)
  apply Lp.ext
  filter_upwards [hl,hr,hs,hw,hc,ha,Lp.coeFn_add (generalizedField K U) (S U.val)] with x hl hr hs hw hc ha hadd
  rw [hl,hw,hadd,Pi.add_apply,hr]
  change ordinaryFieldHalfMap (g x) (H x) =
    weylUnitary (b x) (ordinaryFieldHalfMap (g x) (G x)+S U.val x)
  rw [show H x = weylWeightedMap (1/2) (by norm_num) (by norm_num) (b x) (G x) from hc,
    fieldConjugation_half,ha]
  congr 1
  congr 1
  exact hs.symm

lemma fiberWeyl_field_conjugation (b g : GW.Space → OneBoson) (hb : StronglyMeasurable b) (hg : StronglyMeasurable g)
    (hbf : eLpNormEssSup b (volume : Measure GW.Space) < ⊤)
    (hgf : eLpNormEssSup g (volume : Measure GW.Space) < ⊤)
    (U : (physicalNumberPower (1/2)).domain) :
    (fiberWeylUnitary b hb).symm
      (generalizedField (fiberKernel g hg.aestronglyMeasurable (fiberWeylEssBound_ae g hgf))
        (fiberWeylRootInput b hb hbf U)) =
      generalizedField (fiberKernel g hg.aestronglyMeasurable (fiberWeylEssBound_ae g hgf)) U+
        fiberFieldShiftMap b g hb hg (fiberWeylEssBound b) (fiberWeylEssBound g)
          (fiberWeylEssBound_nonneg b) (fiberWeylEssBound_nonneg g)
          (fiberWeylEssBound_ae b hbf) (fiberWeylEssBound_ae g hgf) U.val := by
  rw [fiberWeyl_field_action b g hb hg hbf hgf U,LinearIsometryEquiv.symm_apply_apply]


lemma physicalNumberOperator_domain_eq :
    physicalNumberOperator.domain = (physicalShiftedNumberPower 1).domain := by
  rw [← physicalNumberPower_one,physicalNumberPower_domains_eq 1 zero_lt_one]

lemma fiberPhysicalNumber_mem_root (U : physicalNumberOperator.domain) :
    U.val ∈ (physicalNumberPower (1/2)).domain := by
  have hU : U.val ∈ (physicalShiftedNumberPower 1).domain := physicalNumberOperator_domain_eq ▸ U.property
  let z := physicalShiftedSectorInput 1 ⟨U.val,hU⟩
  have hs : z.val ∈ (shiftedNumberPower ElectronSector (1/2)).domain :=
    shiftedNumberDomain_mono (by norm_num) z.property
  have hn : z.val ∈ (numberPower ElectronSector (1/2)).domain := by
    rw [numberPower_domain_eq ElectronSector (1/2) (by norm_num)]
    exact hs
  rw [physicalNumberPower_domain_map]
  exact Submodule.mem_map.mpr ⟨z.val,hn,electronBosonUnitary.apply_symm_apply U.val⟩

def fiberPhysicalNumberRootInput (U : physicalNumberOperator.domain) : (physicalNumberPower (1/2)).domain :=
  ⟨U.val,fiberPhysicalNumber_mem_root U⟩

lemma fiberWeyl_number_mem_domain (b : GW.Space → OneBoson) (hb : StronglyMeasurable b)
    (hfin : eLpNormEssSup b (volume : Measure GW.Space) < ⊤) (U : physicalNumberOperator.domain) :
    fiberWeylUnitary b hb U.val ∈ physicalNumberOperator.domain := by
  have hU : U.val ∈ (physicalNumberPower 1).domain := by
    simpa only [physicalNumberPower_one] using U.property
  have hh := (fiberWeyl_number_domain_iff 1 zero_le_one le_rfl b hb hfin U.val).mpr hU
  simpa only [physicalNumberPower_one] using hh

def fiberWeylNumberInput (b : GW.Space → OneBoson) (hb : StronglyMeasurable b)
    (hfin : eLpNormEssSup b (volume : Measure GW.Space) < ⊤)
    (U : physicalNumberOperator.domain) : physicalNumberOperator.domain :=
  ⟨fiberWeylUnitary b hb U.val,fiberWeyl_number_mem_domain b hb hfin U⟩

lemma fiberNumberRoot_mk_value (A : Physical) (hA : A ∈ (physicalNumberPower (1/2)).domain) :
    (⟨A,hA⟩ : (physicalNumberPower (1/2)).domain).val = A := rfl

lemma fiberPhysicalNumberRootInput_value (U : physicalNumberOperator.domain) :
    (fiberPhysicalNumberRootInput U).val = U.val := by
  have hc : fiberPhysicalNumberRootInput U =
      (⟨U.val,fiberPhysicalNumber_mem_root U⟩ : (physicalNumberPower (1/2)).domain) := rfl
  exact (congrArg (fun V : (physicalNumberPower (1/2)).domain => V.val) hc).trans
    (fiberNumberRoot_mk_value U.val (fiberPhysicalNumber_mem_root U))

lemma fiberWeylNumberInput_value (b : GW.Space → OneBoson) (hb : StronglyMeasurable b)
    (hfin : eLpNormEssSup b (volume : Measure GW.Space) < ⊤) (U : physicalNumberOperator.domain) :
    (fiberWeylNumberInput b hb hfin U).val = fiberWeylUnitary b hb U.val := rfl

lemma physicalNumberOperator_graph_ae (U : physicalNumberOperator.domain) :
    ∀ᵐ x ∂(volume : Measure GW.Space), (U.val x,physicalNumberOperator U x) ∈ numberOperator.graph := by
  filter_upwards [bochnerDiagonal_coordinates (volume : Measure GW.Space) Sector (fun n => (n:ℝ)) U] with x hx
  exact (scalarDiagonal_graph_iff Sector (fun n => (n:ℝ)) _).mpr hx

lemma fiberNumberScalar_stronglyMeasurable (b : GW.Space → OneBoson) (hb : StronglyMeasurable b) :
    StronglyMeasurable (fun x => ((‖b x‖^2:ℝ):ℂ)) :=
  Complex.continuous_ofReal.comp_stronglyMeasurable (hb.norm.pow 2)

lemma fiberNumberScalar_bound (b : GW.Space → OneBoson) (M : ℝ) (hM : 0 ≤ M)
    (hB : ∀ᵐ x ∂(volume : Measure GW.Space), ‖b x‖ ≤ M) :
    ∀ᵐ x ∂(volume : Measure GW.Space), ‖((‖b x‖^2:ℝ):ℂ)‖ ≤ M^2 := by
  filter_upwards [hB] with x hx
  rw [Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) hx 2

def fiberNumberScalarMap (b : GW.Space → OneBoson) (hb : StronglyMeasurable b)
    (hfin : eLpNormEssSup b (volume : Measure GW.Space) < ⊤) : Physical →L[ℂ] Physical :=
  fiberScalarMap (fun x => ((‖b x‖^2:ℝ):ℂ)) (fiberNumberScalar_stronglyMeasurable b hb)
    ((fiberWeylEssBound b)^2)
    (fiberNumberScalar_bound b (fiberWeylEssBound b) (fiberWeylEssBound_nonneg b) (fiberWeylEssBound_ae b hfin))


lemma fiberNumberScalarMap_ae (b : GW.Space → OneBoson) (hb : StronglyMeasurable b)
    (hfin : eLpNormEssSup b (volume : Measure GW.Space) < ⊤) (U : Physical) :
    fiberNumberScalarMap b hb hfin U =ᵐ[volume] fun x => ((‖b x‖^2:ℝ):ℂ) • U x :=
  fiberScalarClass_ae (fun x => ((‖b x‖^2:ℝ):ℂ)) (fiberNumberScalar_stronglyMeasurable b hb)
    ((fiberWeylEssBound b)^2)
    (fiberNumberScalar_bound b (fiberWeylEssBound b) (fiberWeylEssBound_nonneg b) (fiberWeylEssBound_ae b hfin)) U

set_option backward.isDefEq.respectTransparency.types false in
lemma fiberWeyl_number_graph_action (f : OneBoson) (u v Nu Nv : Carrier)
    (hu : (u,Nu) ∈ numberOperator.graph) (hv : (v,Nv) ∈ numberOperator.graph)
    (hw : v = weylUnitary f u) (g : FiberRootDomain)
    (hg : numberDomainEmbedding (1/2) (by norm_num) g = u) :
    Nv = weylUnitary f (Nu+ordinaryFieldHalfMap f g+((‖f‖^2:ℝ):ℂ) • u) := by
  let U : numberOperator.domain := ⟨u,numberConjugation_graph_mem hu⟩
  have hNu : numberOperator U = Nu :=
    numberOperator.mem_graph_snd_inj (numberOperator.mem_graph U) hu rfl
  have hNv : numberOperator (weylNumberInput f U) = Nv :=
    numberOperator.mem_graph_snd_inj (numberOperator.mem_graph (weylNumberInput f U)) hv hw.symm
  have hFu : ordinaryFieldHalfInput f g = numberConjugationFieldInput f (numberConjugationGraphInput U) := by
    apply Subtype.ext
    exact hg
  have ht := congrArg (weylUnitary f) (weyl_number_conjugation f U)
  rw [LinearIsometryEquiv.apply_symm_apply,hNu,hNv,← hFu] at ht
  exact ht

set_option backward.isDefEq.respectTransparency.types false in
lemma fiberWeyl_number_action_from_ae (b : GW.Space → OneBoson) (hb : StronglyMeasurable b)
    (U V : physicalNumberOperator.domain) (R : (physicalNumberPower (1/2)).domain)
    (G : Lp FiberRootDomain 2 (volume : Measure GW.Space))
    (K : BosonKernel ElectronL2) (S : Physical →L[ℂ] Physical)
    (hV : V.val = fiberWeylUnitary b hb U.val)
    (hG : (fun x => numberDomainEmbedding (1/2) (by norm_num) (G x)) =ᵐ[volume] U.val)
    (hF : generalizedField K R =ᵐ[volume] fun x => ordinaryFieldHalfMap (b x) (G x))
    (hS : S U.val =ᵐ[volume] fun x => ((‖b x‖^2:ℝ):ℂ) • U.val x) :
    physicalNumberOperator V = fiberWeylUnitary b hb
      (physicalNumberOperator U+generalizedField K R+S U.val) := by
  have hw := fiberWeylUnitary_ae b hb (physicalNumberOperator U+generalizedField K R+S U.val)
  have hv := fiberWeylUnitary_ae b hb U.val
  rw [← hV] at hv
  apply Lp.ext
  filter_upwards [physicalNumberOperator_graph_ae U,physicalNumberOperator_graph_ae V,
    hG,hF,hS,hw,hv,Lp.coeFn_add (physicalNumberOperator U) (generalizedField K R),
    Lp.coeFn_add (physicalNumberOperator U+generalizedField K R) (S U.val)] with x hN hNV hG hF hS hw hv hsum hsumS
  rw [hw,hsumS,Pi.add_apply,hsum,Pi.add_apply,hF,hS]
  exact fiberWeyl_number_graph_action (b x) (U.val x) (V.val x)
    (physicalNumberOperator U x) (physicalNumberOperator V x) hN hNV hv (G x) hG

lemma fiberWeyl_number_action_from_root_ae (b : GW.Space → OneBoson) (hb : StronglyMeasurable b)
    (U V : physicalNumberOperator.domain) (R : (physicalNumberPower (1/2)).domain)
    (G : Lp FiberRootDomain 2 (volume : Measure GW.Space))
    (K : BosonKernel ElectronL2) (S : Physical →L[ℂ] Physical)
    (hV : V.val = fiberWeylUnitary b hb U.val) (hR : R.val = U.val)
    (hG : (fun x => numberDomainEmbedding (1/2) (by norm_num) (G x)) =ᵐ[volume] R.val)
    (hF : generalizedField K R =ᵐ[volume] fun x => ordinaryFieldHalfMap (b x) (G x))
    (hS : S U.val =ᵐ[volume] fun x => ((‖b x‖^2:ℝ):ℂ) • U.val x) :
    physicalNumberOperator V = fiberWeylUnitary b hb
      (physicalNumberOperator U+generalizedField K R+S U.val) := by
  have he : (fun x => numberDomainEmbedding (1/2) (by norm_num) (G x)) =ᵐ[volume] U.val := by
    filter_upwards [hG] with x hx
    exact hx.trans (congrArg (fun A : Physical => A x) hR)
  exact fiberWeyl_number_action_from_ae b hb U V R G K S hV he hF hS

set_option backward.isDefEq.respectTransparency.types false in
lemma fiberWeyl_number_action (b : GW.Space → OneBoson) (hb : StronglyMeasurable b)
    (hfin : eLpNormEssSup b (volume : Measure GW.Space) < ⊤) (U : physicalNumberOperator.domain) :
    physicalNumberOperator (fiberWeylNumberInput b hb hfin U) =
      fiberWeylUnitary b hb (physicalNumberOperator U+
        generalizedField (fiberKernel b hb.aestronglyMeasurable (fiberWeylEssBound_ae b hfin)) (fiberPhysicalNumberRootInput U)+
        fiberNumberScalarMap b hb hfin U.val) := by
  let R := fiberPhysicalNumberRootInput U
  let G := fiberRootRepresentative (fiberPhysicalFromUnshifted R)
  let K := fiberKernel b hb.aestronglyMeasurable (fiberWeylEssBound_ae b hfin)
  let S := fiberNumberScalarMap b hb hfin
  let V := fiberWeylNumberInput b hb hfin U
  have ha := fiberRootRepresentative_original_ae R
  have hf := fiberGeneralizedField_ae b hb (fiberWeylEssBound b) (fiberWeylEssBound_ae b hfin) R G ha
  have hs : S U.val =ᵐ[volume] fun x => ((‖b x‖^2:ℝ):ℂ) • U.val x :=
    fiberNumberScalarMap_ae b hb hfin U.val
  exact fiberWeyl_number_action_from_root_ae b hb U V R G K S
    (fiberWeylNumberInput_value b hb hfin U) (fiberPhysicalNumberRootInput_value U) ha hf hs

lemma fiberWeyl_number_conjugation (b : GW.Space → OneBoson) (hb : StronglyMeasurable b)
    (hfin : eLpNormEssSup b (volume : Measure GW.Space) < ⊤) (U : physicalNumberOperator.domain) :
    (fiberWeylUnitary b hb).symm (physicalNumberOperator (fiberWeylNumberInput b hb hfin U)) =
      physicalNumberOperator U+
        generalizedField (fiberKernel b hb.aestronglyMeasurable (fiberWeylEssBound_ae b hfin)) (fiberPhysicalNumberRootInput U)+
        fiberNumberScalarMap b hb hfin U.val := by
  rw [fiberWeyl_number_action b hb hfin U,LinearIsometryEquiv.symm_apply_apply]


set_option backward.isDefEq.respectTransparency.types false in
lemma weyl_inner_im_difference_bound (f g : OneBoson) :
    |(⟪f,g⟫_ℂ).im| ≤ ‖f-g‖*‖g‖ := by
  have hs : (⟪g,g⟫_ℂ).im = 0 := by
    convert! inner_self_im (𝕜 := ℂ) g using 1 <;> rfl
  have he : (⟪f-g,g⟫_ℂ).im = (⟪f,g⟫_ℂ).im := by
    rw [inner_sub_left,Complex.sub_im,hs,sub_zero]
  rw [← he]
  exact (Complex.abs_im_le_norm _).trans (norm_inner_le_norm _ _)

def physicalNumberHalfInverse : Physical →L[ℂ] Physical := numberHalfInverse.compLpL 2 (volume : Measure GW.Space)

lemma physicalNumberHalfInverse_ae (U : Physical) :
    physicalNumberHalfInverse U =ᵐ[volume] fun x => numberHalfInverse (U x) :=
  numberHalfInverse.coeFn_compLp U

lemma physicalNumberHalfNegative_domain : (physicalShiftedNumberPower (-(1/2:ℝ))).domain = ⊤ := by
  apply Submodule.ext
  intro U
  constructor
  · intro _
    trivial
  · intro _
    apply (bochnerDiagonal_domain_iff_coordinates (volume : Measure GW.Space) Sector
      (fun n => ((n:ℝ)+1)^(-(1/2:ℝ))) U).mpr
    refine ⟨physicalNumberHalfInverse U,?_⟩
    filter_upwards [physicalNumberHalfInverse_ae U] with x hx
    intro n
    exact (congrArg (fun v : Carrier => v n) hx).trans (numberHalfInverse_apply (U x) n)

def physicalNumberHalfNegativeInput (U : Physical) : (physicalShiftedNumberPower (-(1/2:ℝ))).domain :=
  ⟨U,by rw [physicalNumberHalfNegative_domain]; trivial⟩

lemma physicalNumberHalfInverse_power (U : Physical) :
    physicalShiftedNumberPower (-(1/2:ℝ)) (physicalNumberHalfNegativeInput U) = physicalNumberHalfInverse U := by
  apply Lp.ext
  filter_upwards [bochnerDiagonal_coordinates (volume : Measure GW.Space) Sector
    (fun n => ((n:ℝ)+1)^(-(1/2:ℝ))) (physicalNumberHalfNegativeInput U),
    physicalNumberHalfInverse_ae U] with x hx hy
  apply lp.ext
  funext n
  exact (hx n).trans ((numberHalfInverse_apply (U x) n).symm.trans
    (congrArg (fun v : Carrier => v n) hy).symm)

set_option backward.isDefEq.respectTransparency.types false in
lemma fiberWeyl_difference_halfInverse_bound (a b : GW.Space → OneBoson)
    (ha : StronglyMeasurable a) (hb : StronglyMeasurable b)
    (M δ : ℝ) (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hB : ∀ᵐ x ∂(volume : Measure GW.Space), ‖b x‖ ≤ M)
    (hD : ∀ᵐ x ∂(volume : Measure GW.Space), ‖a x-b x‖ ≤ δ) :
    ‖((fiberWeylUnitary a ha : Physical →L[ℂ] Physical)-
      (fiberWeylUnitary b hb : Physical →L[ℂ] Physical)).comp physicalNumberHalfInverse‖ ≤ (2+M)*δ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro U
  change ‖fiberWeylUnitary a ha (physicalNumberHalfInverse U)-
    fiberWeylUnitary b hb (physicalNumberHalfInverse U)‖ ≤ (2+M)*δ*‖U‖
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [fiberWeylUnitary_ae a ha (physicalNumberHalfInverse U),
    fiberWeylUnitary_ae b hb (physicalNumberHalfInverse U),physicalNumberHalfInverse_ae U,
    Lp.coeFn_sub (fiberWeylUnitary a ha (physicalNumberHalfInverse U))
      (fiberWeylUnitary b hb (physicalNumberHalfInverse U)),hB,hD] with x ha hb hi hs hB hD
  rw [hs,Pi.sub_apply,ha,hb,hi]
  have hh := (ContinuousLinearMap.le_opNorm
    (((weylUnitary (a x) : Carrier →L[ℂ] Carrier)-(weylUnitary (b x) : Carrier →L[ℂ] Carrier)).comp numberHalfInverse) (U x)).trans
      (mul_le_mul_of_nonneg_right (weyl_difference_halfInverse_norm (a x) (b x)) (norm_nonneg _))
  change ‖weylUnitary (a x) (numberHalfInverse (U x))-weylUnitary (b x) (numberHalfInverse (U x))‖ ≤
    (2*‖a x-b x‖+|(⟪a x,b x⟫_ℂ).im|)*‖U x‖ at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have hp : |(⟪a x,b x⟫_ℂ).im| ≤ δ*M :=
    (weyl_inner_im_difference_bound (a x) (b x)).trans (mul_le_mul hD hB (norm_nonneg _) hδ)
  nlinarith


lemma fiberWeyl_approximation_essentiallyBounded (a b : GW.Space → OneBoson)
    (hb : eLpNormEssSup b (volume : Measure GW.Space) < ⊤)
    (hd : eLpNormEssSup (fun x => a x-b x) (volume : Measure GW.Space) < ⊤) :
    eLpNormEssSup a (volume : Measure GW.Space) < ⊤ := by
  apply eLpNormEssSup_lt_top_of_ae_bound (C := fiberWeylEssBound b+fiberWeylEssBound (fun x => a x-b x))
  filter_upwards [fiberWeylEssBound_ae b hb,fiberWeylEssBound_ae (fun x => a x-b x) hd] with x hb hd
  calc
    ‖a x‖ = ‖b x+(a x-b x)‖ := by congr 1; abel
    _ ≤ ‖b x‖+‖a x-b x‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hb hd

lemma fiberWeyl_difference_esssup (a b : GW.Space → OneBoson)
    (ha : StronglyMeasurable a) (hb : StronglyMeasurable b)
    (hbf : eLpNormEssSup b (volume : Measure GW.Space) < ⊤)
    (hdf : eLpNormEssSup (fun x => a x-b x) (volume : Measure GW.Space) < ⊤) :
    ‖((fiberWeylUnitary a ha : Physical →L[ℂ] Physical)-
      (fiberWeylUnitary b hb : Physical →L[ℂ] Physical)).comp physicalNumberHalfInverse‖ ≤
      (2+fiberWeylEssBound b)*fiberWeylEssBound (fun x => a x-b x) :=
  fiberWeyl_difference_halfInverse_bound a b ha hb _ _ (fiberWeylEssBound_nonneg b)
    (fiberWeylEssBound_nonneg _) (fiberWeylEssBound_ae b hbf) (fiberWeylEssBound_ae _ hdf)

lemma fiberWeyl_difference_converges (a : ℕ → GW.Space → OneBoson) (b : GW.Space → OneBoson)
    (ha : ∀ m, StronglyMeasurable (a m)) (hb : StronglyMeasurable b)
    (hbf : eLpNormEssSup b (volume : Measure GW.Space) < ⊤)
    (hdf : ∀ m, eLpNormEssSup (fun x => a m x-b x) (volume : Measure GW.Space) < ⊤)
    (hδ : Tendsto (fun m => fiberWeylEssBound (fun x => a m x-b x)) atTop (𝓝 0)) :
    Tendsto (fun m => ‖((fiberWeylUnitary (a m) (ha m) : Physical →L[ℂ] Physical)-
      (fiberWeylUnitary b hb : Physical →L[ℂ] Physical)).comp physicalNumberHalfInverse‖) atTop (𝓝 0) := by
  have hh := hδ.const_mul (2+fiberWeylEssBound b)
  simp only [mul_zero] at hh
  exact squeeze_zero (fun _ => norm_nonneg _) (fun m => fiberWeyl_difference_esssup (a m) b (ha m) hb hbf (hdf m)) hh


lemma fiberWeylUnitary_congr_ae (b c : GW.Space → OneBoson)
    (hb : StronglyMeasurable b) (hc : StronglyMeasurable c) (he : b =ᵐ[(volume : Measure GW.Space)] c) :
    (fiberWeylUnitary b hb : Physical →L[ℂ] Physical) = (fiberWeylUnitary c hc : Physical →L[ℂ] Physical) := by
  apply ContinuousLinearMap.ext
  intro U
  apply Lp.ext
  filter_upwards [fiberWeylUnitary_ae b hb U,fiberWeylUnitary_ae c hc U,he] with x h₁ h₂ h₃
  change fiberWeylUnitary b hb U x = fiberWeylUnitary c hc U x
  rw [h₁,h₂,h₃]

lemma fiberWeyl_number_domain_image (r : ℝ) (hr : 0 ≤ r) (hs : r ≤ 1)
    (b : GW.Space → OneBoson) (hb : StronglyMeasurable b)
    (hfin : eLpNormEssSup b (volume : Measure GW.Space) < ⊤) :
    (fiberWeylUnitary b hb) '' ((physicalNumberPower r).domain : Set Physical) =
      ((physicalNumberPower r).domain : Set Physical) := by
  ext U
  constructor
  · rintro ⟨V,hV,rfl⟩
    exact (fiberWeyl_number_domain_iff r hr hs b hb hfin V).mpr hV
  · intro hU
    refine ⟨(fiberWeylUnitary b hb).symm U,?_,LinearIsometryEquiv.apply_symm_apply _ _⟩
    apply (fiberWeyl_number_domain_iff r hr hs b hb hfin _).mp
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact hU


lemma fiberWeyl_sourceShifted_mem (σ : ℝ) (hσ : 0 ≤ σ) (U : (physicalNumberPower σ).domain) :
    U.val ∈ (physicalShiftedNumberPower σ).domain :=
  fractionalNumber_domains_eq σ hσ ▸ U.property

lemma fiberWeyl_shifted_mk_value (σ : ℝ) (A : Physical)
    (hA : A ∈ (physicalShiftedNumberPower σ).domain) :
    (⟨A,hA⟩ : (physicalShiftedNumberPower σ).domain).val = A := rfl

set_option backward.isDefEq.respectTransparency.types false in
lemma fiberWeyl_number_shifted_bound (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1)
    (b : GW.Space → OneBoson) (hb : StronglyMeasurable b)
    (hfin : eLpNormEssSup b (volume : Measure GW.Space) < ⊤)
    (U : (physicalNumberPower σ).domain) :
    ∃ V : (physicalShiftedNumberPower σ).domain, V.val = fiberWeylUnitary b hb U.val ∧
      ‖physicalShiftedNumberPower σ V‖ ≤ (1+fiberWeylEssBound b)^(2*σ)*
        ‖physicalShiftedNumberPower σ ⟨U.val,fiberWeyl_sourceShifted_mem σ hσ₀ U⟩‖ := by
  let A : (physicalShiftedNumberPower σ).domain := ⟨U.val,fiberWeyl_sourceShifted_mem σ hσ₀ U⟩
  let V : (physicalShiftedNumberPower σ).domain := ⟨fiberWeylUnitary b hb A.val,
    fiberWeyl_shifted_domain σ hσ₀ hσ₁ b hb (fiberWeylEssBound b) (fiberWeylEssBound_ae b hfin) A.val A.property⟩
  refine ⟨V,?_,?_⟩
  · change fiberWeylUnitary b hb A.val = fiberWeylUnitary b hb U.val
    exact congrArg (fiberWeylUnitary b hb)
      (fiberWeyl_shifted_mk_value σ U.val (fiberWeyl_sourceShifted_mem σ hσ₀ U))
  · exact fiberWeyl_shifted_bound σ hσ₀ hσ₁ b hb hfin A

end GW.Fock

