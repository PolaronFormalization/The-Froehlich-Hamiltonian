module
public import GW.Gross.MainFormH
public import GW.Gross.MainGrossForm

/-! Source main:conjugation, manuscript6288–6385.
Original finite Gross transform, explicit creator-momentum/annihilator products,
exact finite counterterm and literal operator and full domain identities. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Gross
open GW.Model GW.Fock GW.Analysis

/- Source argument component Phase01. -/
lemma conjugationPhase_finite (f : OneBoson) : eLpNormEssSup (phaseAt f) (volume : Measure GW.Space) < ⊤ :=
  eLpNormEssSup_lt_top_of_ae_bound (commutatorPhase_norm_bound f)

lemma conjugationPhase_kernel (f : OneBoson) {M : ℝ}
    (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖phaseAt f x‖ ≤ M) :
    fiberKernel (phaseAt f) (phaseAt_continuous f).stronglyMeasurable.aestronglyMeasurable hM = phaseMultiplicationKernel f := by
  have he : fiberKernel (phaseAt f) (phaseAt_continuous f).stronglyMeasurable.aestronglyMeasurable hM =
      fiberKernel (phaseAt f) (phaseAt_continuous f).aestronglyMeasurable (commutatorPhase_norm_bound f) := rfl
  exact he.trans (commutatorPhase_kernel f)

lemma conjugationNumberScalar (f : OneBoson) (U : Physical) :
    fiberNumberScalarMap (phaseAt f) (phaseAt_continuous f).stronglyMeasurable (conjugationPhase_finite f) U =
      ((‖f‖^2:ℝ):ℂ) • U := by
  apply Lp.ext
  filter_upwards [fiberNumberScalarMap_ae (phaseAt f) (phaseAt_continuous f).stronglyMeasurable
    (conjugationPhase_finite f) U,Lp.coeFn_smul (((‖f‖^2:ℝ):ℂ)) U] with x hx hs
  rw [hx,hs,Pi.smul_apply,phaseAt_norm]

lemma conjugationFieldScalar (f g : OneBoson) (U : Physical) :
    fiberFieldShiftMap (phaseAt f) (phaseAt g) (phaseAt_continuous f).stronglyMeasurable (phaseAt_continuous g).stronglyMeasurable
      (fiberWeylEssBound (phaseAt f)) (fiberWeylEssBound (phaseAt g))
      (fiberWeylEssBound_nonneg _) (fiberWeylEssBound_nonneg _)
      (fiberWeylEssBound_ae _ (conjugationPhase_finite f)) (fiberWeylEssBound_ae _ (conjugationPhase_finite g)) U =
      (((2*(⟪f,g⟫_ℂ).re:ℝ):ℂ)) • U := by
  apply Lp.ext
  filter_upwards [fiberFieldShiftMap_ae (phaseAt f) (phaseAt g) (phaseAt_continuous f).stronglyMeasurable (phaseAt_continuous g).stronglyMeasurable
      (fiberWeylEssBound (phaseAt f)) (fiberWeylEssBound (phaseAt g))
      (fiberWeylEssBound_nonneg _) (fiberWeylEssBound_nonneg _)
      (fiberWeylEssBound_ae _ (conjugationPhase_finite f)) (fiberWeylEssBound_ae _ (conjugationPhase_finite g)) U,
    Lp.coeFn_smul (((2*(⟪f,g⟫_ℂ).re:ℝ):ℂ)) U] with x hx hs
  rw [hx,hs,Pi.smul_apply,weylPhase_inner]

/- Source argument component Actions01. -/
lemma conjugationField_graph_value (f : OneBoson) {M : ℝ}
    (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖phaseAt f x‖ ≤ M)
    (a : (generalizedField (fiberKernel (phaseAt f) (phaseAt_continuous f).stronglyMeasurable.aestronglyMeasurable hM)).domain)
    (R : FiberPhysicalRoot) (hv : a.val = (fiberPhysicalRootInput R).val) :
    generalizedField (fiberKernel (phaseAt f) (phaseAt_continuous f).stronglyMeasurable.aestronglyMeasurable hM) a = grossFormFieldMap f R := by
  let K := fiberKernel (phaseAt f) (phaseAt_continuous f).stronglyMeasurable.aestronglyMeasurable hM
  have hk : generalizedField K = generalizedField (phaseMultiplicationKernel f) :=
    congrArg generalizedField (conjugationPhase_kernel f hM)
  have hg : (a.val,generalizedField K a) ∈ (generalizedField (phaseMultiplicationKernel f)).graph :=
    (congrArg (fun T : Physical →ₗ.[ℂ] Physical => (a.val,generalizedField K a) ∈ T.graph) hk).mp
      ((generalizedField K).mem_graph a)
  exact (generalizedField (phaseMultiplicationKernel f)).mem_graph_snd_inj hg (grossFormFieldMap_graph f R) hv

lemma conjugationNumber_action (f : OneBoson) (U : physicalNumberOperator.domain) :
    (grossWeylCoefficient f).symm
      (physicalNumberOperator (fiberWeylNumberInput (phaseAt f) (phaseAt_continuous f).stronglyMeasurable
        (conjugationPhase_finite f) U)) =
      physicalNumberOperator U+grossFormFieldMap f (fiberPhysicalFromUnshifted (fiberPhysicalNumberRootInput U))+
        ((‖f‖^2:ℝ):ℂ) • U.val := by
  have h := fiberWeyl_number_conjugation (phaseAt f) (phaseAt_continuous f).stronglyMeasurable (conjugationPhase_finite f) U
  have hf := conjugationField_graph_value f (fiberWeylEssBound_ae _ (conjugationPhase_finite f))
    (show (generalizedField (fiberKernel (phaseAt f) (phaseAt_continuous f).stronglyMeasurable.aestronglyMeasurable
      (fiberWeylEssBound_ae _ (conjugationPhase_finite f)))).domain from fiberPhysicalNumberRootInput U)
    (fiberPhysicalFromUnshifted (fiberPhysicalNumberRootInput U))
    (fiberPhysicalFromUnshifted_value (fiberPhysicalNumberRootInput U)).symm
  rw [hf,conjugationNumberScalar] at h
  exact h

lemma conjugationField_action (f g : OneBoson) (U : (physicalNumberPower (1/2)).domain) :
    (grossWeylCoefficient f).symm
      (grossFormFieldMap g (fiberPhysicalFromUnshifted
        (fiberWeylRootInput (phaseAt f) (phaseAt_continuous f).stronglyMeasurable (conjugationPhase_finite f) U))) =
      grossFormFieldMap g (fiberPhysicalFromUnshifted U)+(((2*(⟪f,g⟫_ℂ).re:ℝ):ℂ)) • U.val := by
  have h := fiberWeyl_field_conjugation (phaseAt f) (phaseAt g) (phaseAt_continuous f).stronglyMeasurable
    (phaseAt_continuous g).stronglyMeasurable (conjugationPhase_finite f) (conjugationPhase_finite g) U
  have h₁ := conjugationField_graph_value g (fiberWeylEssBound_ae _ (conjugationPhase_finite g))
    (show (generalizedField (fiberKernel (phaseAt g) (phaseAt_continuous g).stronglyMeasurable.aestronglyMeasurable
      (fiberWeylEssBound_ae _ (conjugationPhase_finite g)))).domain from
      fiberWeylRootInput (phaseAt f) (phaseAt_continuous f).stronglyMeasurable (conjugationPhase_finite f) U)
    (fiberPhysicalFromUnshifted (fiberWeylRootInput (phaseAt f) (phaseAt_continuous f).stronglyMeasurable (conjugationPhase_finite f) U))
    (fiberPhysicalFromUnshifted_value _).symm
  have h₂ := conjugationField_graph_value g (fiberWeylEssBound_ae _ (conjugationPhase_finite g))
    (show (generalizedField (fiberKernel (phaseAt g) (phaseAt_continuous g).stronglyMeasurable.aestronglyMeasurable
      (fiberWeylEssBound_ae _ (conjugationPhase_finite g)))).domain from U)
    (fiberPhysicalFromUnshifted U) (fiberPhysicalFromUnshifted_value U).symm
  rw [h₁,h₂,conjugationFieldScalar] at h
  exact h

/- Source argument component Square01. -/
def conjugationSourceGraph : freeHamiltonian.domain →ₗ[ℂ] FreeGraphDomain where
  toFun := commutatorSourceGraphInput
  map_add' u v := Subtype.ext rfl
  map_smul' c u := Subtype.ext rfl

lemma conjugationField_output_mem (f : OneBoson) (u : freeHamiltonian.domain) :
    constructionFieldRestriction f u ∈ (generalizedField (phaseMultiplicationKernel f)).domain := by
  obtain ⟨w,hw,hz⟩ := generalizedFieldSquare_graph (phaseMultiplicationKernel f)
    (grossGraphNumberOne (conjugationSourceGraph u))
  change (u.val,w) ∈ (generalizedField (phaseMultiplicationKernel f)).graph at hw
  have he := (generalizedField (phaseMultiplicationKernel f)).mem_graph_snd_inj
    (constructionFieldRestriction_graph f u) hw rfl
  rw [he]
  exact (generalizedField (phaseMultiplicationKernel f)).mem_domain_of_mem_graph hz

def conjugationSquareMap (f : OneBoson) : freeHamiltonian.domain →ₗ[ℂ] Physical :=
  (generalizedField (phaseMultiplicationKernel f)).toFun.comp
    ((constructionFieldRestriction f).codRestrict (generalizedField (phaseMultiplicationKernel f)).domain
      (conjugationField_output_mem f))

lemma conjugationSquareMap_value (f : OneBoson) (u : freeHamiltonian.domain) :
    conjugationSquareMap f u = generalizedFieldSquare (phaseMultiplicationKernel f)
      (grossGraphNumberOne (conjugationSourceGraph u)) := by
  obtain ⟨w,hw,hz⟩ := generalizedFieldSquare_graph (phaseMultiplicationKernel f)
    (grossGraphNumberOne (conjugationSourceGraph u))
  change (u.val,w) ∈ (generalizedField (phaseMultiplicationKernel f)).graph at hw
  have he := (generalizedField (phaseMultiplicationKernel f)).mem_graph_snd_inj
    (constructionFieldRestriction_graph f u) hw rfl
  exact (generalizedField (phaseMultiplicationKernel f)).mem_graph_snd_inj
    ((generalizedField (phaseMultiplicationKernel f)).mem_graph
      ⟨constructionFieldRestriction f u,conjugationField_output_mem f u⟩) hz he

lemma conjugationSquareMap_graph (f : OneBoson) (u : freeHamiltonian.domain) :
    (constructionFieldRestriction f u,conjugationSquareMap f u) ∈ (generalizedField (phaseMultiplicationKernel f)).graph :=
  (generalizedField (phaseMultiplicationKernel f)).mem_graph
    ⟨constructionFieldRestriction f u,conjugationField_output_mem f u⟩

/- Source argument component H0Actions01. -/
lemma conjugationSourceGraph_value (u : freeHamiltonian.domain) :
    freeGraphDomainInclusion (conjugationSourceGraph u) = u.val := commutatorSourceGraphInput_value u

lemma conjugationSourceRoot_value (u : freeHamiltonian.domain) :
    (fiberPhysicalRootInput (commutatorGraphRootMap (conjugationSourceGraph u))).val = u.val :=
  (commutatorGraphRootMap_value _).trans (conjugationSourceGraph_value u)

def conjugationWeylH0Input (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (hjj : ∀ i j : Fin 3, MemLp (fun k => (k j : ℂ)*(weylMomentumCoefficient f i (hj i)) k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2) (u : freeHamiltonian.domain) : freeHamiltonian.domain :=
  ⟨grossWeylCoefficient f u.val,grossH0Weyl_mem f hj hjj heven u⟩

def conjugationNumberInput (u : freeHamiltonian.domain) : physicalNumberOperator.domain :=
  ⟨u.val,freeHamiltonian_number_mem u⟩

lemma conjugationRoot_fromNumber (u : freeHamiltonian.domain) :
    fiberPhysicalFromUnshifted (fiberPhysicalNumberRootInput (conjugationNumberInput u)) =
      commutatorGraphRootMap (conjugationSourceGraph u) := by
  apply Subtype.ext
  exact (fiberPhysicalFromUnshifted_value _).trans
    ((fiberPhysicalNumberRootInput_value _).trans (conjugationSourceRoot_value u).symm)

lemma conjugationRestriction_sourceRoot (f : OneBoson) (u : freeHamiltonian.domain) :
    constructionFieldRestriction f u = grossFormFieldMap f (commutatorGraphRootMap (conjugationSourceGraph u)) :=
  (generalizedField (phaseMultiplicationKernel f)).mem_graph_snd_inj (constructionFieldRestriction_graph f u)
    (grossFormFieldMap_graph f _) (conjugationSourceRoot_value u).symm

lemma conjugationNumber_on_H0 (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (hjj : ∀ i j : Fin 3, MemLp (fun k => (k j : ℂ)*(weylMomentumCoefficient f i (hj i)) k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2) (u : freeHamiltonian.domain) :
    (grossWeylCoefficient f).symm (physicalNumberOperator (conjugationNumberInput (conjugationWeylH0Input f hj hjj heven u))) =
      physicalNumberOperator (conjugationNumberInput u)+constructionFieldRestriction f u+((‖f‖^2:ℝ):ℂ) • u.val := by
  have h := conjugationNumber_action f (conjugationNumberInput u)
  have hi : conjugationNumberInput (conjugationWeylH0Input f hj hjj heven u) =
      fiberWeylNumberInput (phaseAt f) (phaseAt_continuous f).stronglyMeasurable (conjugationPhase_finite f) (conjugationNumberInput u) := by
    apply Subtype.ext
    rfl
  rw [← hi,conjugationRoot_fromNumber,← conjugationRestriction_sourceRoot] at h
  exact h

lemma conjugationField_on_H0 (f g : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (hjj : ∀ i j : Fin 3, MemLp (fun k => (k j : ℂ)*(weylMomentumCoefficient f i (hj i)) k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2) (u : freeHamiltonian.domain) :
    (grossWeylCoefficient f).symm (constructionFieldRestriction g (conjugationWeylH0Input f hj hjj heven u)) =
      constructionFieldRestriction g u+(((2*(⟪f,g⟫_ℂ).re:ℝ):ℂ)) • u.val := by
  let U := fiberPhysicalNumberRootInput (conjugationNumberInput u)
  let V := fiberWeylRootInput (phaseAt f) (phaseAt_continuous f).stronglyMeasurable (conjugationPhase_finite f) U
  let uW := conjugationWeylH0Input f hj hjj heven u
  have hU : U.val = u.val := fiberPhysicalNumberRootInput_value _
  have hV : V.val = uW.val := by
    change grossWeylCoefficient f U.val = grossWeylCoefficient f u.val
    rw [hU]
  have hr : fiberPhysicalFromUnshifted V = commutatorGraphRootMap (conjugationSourceGraph uW) := by
    apply Subtype.ext
    exact (fiberPhysicalFromUnshifted_value V).trans (hV.trans (conjugationSourceRoot_value uW).symm)
  have h := conjugationField_action f g U
  change (grossWeylCoefficient f).symm (grossFormFieldMap g (fiberPhysicalFromUnshifted V)) = _ at h
  rw [hr,conjugationRoot_fromNumber,← conjugationRestriction_sourceRoot,← conjugationRestriction_sourceRoot,hU] at h
  exact h

/- Source argument component Kinetic01. -/
lemma conjugationCovariant_expansion (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (hjj : ∀ i j : Fin 3, MemLp (fun k => (k j : ℂ)*(weylMomentumCoefficient f i (hj i)) k)
      2 (volume : Measure GW.Space)) (u : FreeGraphDomain) (j : Fin 3) :
    grossFormMomentumMap j (grossGraphCovariantInput f hj hjj u j)-
      grossFormFieldMap (weylMomentumCoefficient f j (hj j))
        (grossFormRootMap (grossGraphCovariantInput f hj hjj u j)) =
    grossFormMomentumMap j (grossGraphMomentumQ u j)-
      2 • commutatorPhaseCreatorMap (weylMomentumCoefficient f j (hj j)) (commutatorGraphMomentumRootMap j u)-
      2 • commutatorAnnihilatorRightMap (weylMomentumCoefficient f j (hj j)) j (hjj j j) u+
      generalizedFieldSquare (phaseMultiplicationKernel (weylMomentumCoefficient f j (hj j))) (grossGraphNumberOne u)+
      grossFormFieldMap (weylMomentumCoefficient (weylMomentumCoefficient f j (hj j)) j (hjj j j))
        (commutatorGraphRootMap u) := by
  rw [grossGraphCovariant_square_expansion]
  simp only [grossFormFieldMap,commutatorAnnihilatorRightMap,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply,two_smul]
  abel

lemma conjugationField_sum (fs : Fin 3 → OneBoson) (u : FiberPhysicalRoot) :
    grossFormFieldMap (∑ j,fs j) u = ∑ j,grossFormFieldMap (fs j) u := by
  simp only [grossFormFieldMap,ContinuousLinearMap.add_apply,grossFormAnnihilator_sum,
    grossFormCreator_sum,Finset.sum_add_distrib]

lemma conjugationKinetic_sum_expansion (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (hjj : ∀ i j : Fin 3, MemLp (fun k => (k j : ℂ)*(weylMomentumCoefficient f i (hj i)) k)
      2 (volume : Measure GW.Space)) (u : FreeGraphDomain) :
    (∑ j : Fin 3, (grossFormMomentumMap j (grossGraphCovariantInput f hj hjj u j)-
      grossFormFieldMap (weylMomentumCoefficient f j (hj j))
        (grossFormRootMap (grossGraphCovariantInput f hj hjj u j)))) =
    (∑ j : Fin 3,grossFormMomentumMap j (grossGraphMomentumQ u j))-
      2 • (∑ j : Fin 3,commutatorPhaseCreatorMap (weylMomentumCoefficient f j (hj j)) (commutatorGraphMomentumRootMap j u))-
      2 • (∑ j : Fin 3,commutatorAnnihilatorRightMap (weylMomentumCoefficient f j (hj j)) j (hjj j j) u)+
      (∑ j : Fin 3,generalizedFieldSquare (phaseMultiplicationKernel (weylMomentumCoefficient f j (hj j))) (grossGraphNumberOne u))+
      grossFormFieldMap (∑ j : Fin 3,weylMomentumCoefficient (weylMomentumCoefficient f j (hj j)) j (hjj j j))
        (commutatorGraphRootMap u) := by
  simp_rw [conjugationCovariant_expansion]
  rw [conjugationField_sum]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.smul_sum,two_smul]

/- Source argument component H0Kinetic02. -/
lemma conjugationKinetic_on_H0 (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (hjj : ∀ i j : Fin 3, MemLp (fun k => (k j : ℂ)*(weylMomentumCoefficient f i (hj i)) k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2) (u : freeHamiltonian.domain) :
    (grossWeylCoefficient f).symm
      (freeMomentumSquare ⟨(conjugationWeylH0Input f hj hjj heven u).val,
        freeHamiltonian_momentum_mem (conjugationWeylH0Input f hj hjj heven u)⟩) =
    freeMomentumSquare ⟨u.val,freeHamiltonian_momentum_mem u⟩-
      2 • (∑ j : Fin 3,commutatorPhaseCreatorMap (weylMomentumCoefficient f j (hj j))
        (commutatorGraphMomentumRootMap j (conjugationSourceGraph u)))-
      2 • (∑ j : Fin 3,commutatorAnnihilatorRightMap (weylMomentumCoefficient f j (hj j)) j (hjj j j) (conjugationSourceGraph u))+
      (∑ j : Fin 3,conjugationSquareMap (weylMomentumCoefficient f j (hj j)) u)+
      constructionFieldRestriction (∑ j : Fin 3,weylMomentumCoefficient (weylMomentumCoefficient f j (hj j)) j (hjj j j)) u := by
  let v := conjugationSourceGraph u
  let a : freeMomentumSquare.domain :=
    ⟨(conjugationWeylH0Input f hj hjj heven u).val,freeHamiltonian_momentum_mem (conjugationWeylH0Input f hj hjj heven u)⟩
  let b : freeMomentumSquare.domain := ⟨grossWeylCoefficient f (freeGraphDomainInclusion v),grossGraphWeyl_second_momentum f hj hjj heven v⟩
  have hab : a = b := by
    apply Subtype.ext
    exact congrArg (grossWeylCoefficient f) (conjugationSourceGraph_value u).symm
  have hp := grossGraph_momentum_square_sum v
  rw [conjugationSourceGraph_value] at hp
  have hsum := freeMomentumSquare.mem_graph_snd_inj hp
    (freeMomentumSquare.mem_graph ⟨u.val,freeHamiltonian_momentum_mem u⟩) rfl
  change (grossWeylCoefficient f).symm (freeMomentumSquare a) = _
  rw [hab,grossGraphWeyl_kinetic_identity f hj hjj heven v,conjugationKinetic_sum_expansion f hj hjj v,hsum]
  simp only [conjugationSquareMap_value,conjugationRestriction_sourceRoot]
  rfl

/- Source argument component Remainder01. -/
def conjugationCreatorMomentumMap (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) :
    freeHamiltonian.domain →ₗ[ℂ] Physical :=
  ∑ j : Fin 3, (commutatorPhaseCreatorMap (weylMomentumCoefficient f j (hj j))).toLinearMap.comp
    ((commutatorGraphMomentumRootMap j).toLinearMap.comp conjugationSourceGraph)

def conjugationMomentumAnnihilatorMap (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (hjj : ∀ i j : Fin 3, MemLp (fun k => (k j : ℂ)*(weylMomentumCoefficient f i (hj i)) k) 2 (volume : Measure GW.Space)) :
    freeHamiltonian.domain →ₗ[ℂ] Physical :=
  ∑ j : Fin 3, (commutatorAnnihilatorRightMap (weylMomentumCoefficient f j (hj j)) j (hjj j j)).toLinearMap.comp conjugationSourceGraph

def conjugationRemainder (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (hjj : ∀ i j : Fin 3, MemLp (fun k => (k j : ℂ)*(weylMomentumCoefficient f i (hj i)) k) 2 (volume : Measure GW.Space))
    (C : ℝ) : freeHamiltonian.domain →ₗ[ℂ] Physical :=
  -(2 • conjugationCreatorMomentumMap f hj)-2 • conjugationMomentumAnnihilatorMap f hj hjj+
    (∑ j : Fin 3,conjugationSquareMap (weylMomentumCoefficient f j (hj j)))+(C:ℂ) • freeHamiltonian.domain.subtype

lemma conjugationRemainder_value (f : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (hjj : ∀ i j : Fin 3, MemLp (fun k => (k j : ℂ)*(weylMomentumCoefficient f i (hj i)) k) 2 (volume : Measure GW.Space))
    (C : ℝ) (u : freeHamiltonian.domain) :
    conjugationRemainder f hj hjj C u =
      -(2 • (∑ j : Fin 3,commutatorPhaseCreatorMap (weylMomentumCoefficient f j (hj j))
        (commutatorGraphMomentumRootMap j (conjugationSourceGraph u))))-
      2 • (∑ j : Fin 3,commutatorAnnihilatorRightMap (weylMomentumCoefficient f j (hj j)) j (hjj j j) (conjugationSourceGraph u))+
      (∑ j : Fin 3,conjugationSquareMap (weylMomentumCoefficient f j (hj j)) u)+(C:ℂ) • u.val := by
  simp only [conjugationRemainder,conjugationCreatorMomentumMap,conjugationMomentumAnnihilatorMap,
    LinearMap.add_apply,LinearMap.sub_apply,LinearMap.neg_apply,LinearMap.smul_apply,LinearMap.sum_apply,
    LinearMap.comp_apply,ContinuousLinearMap.coe_coe,Submodule.subtype_apply]

/- Source argument component Assembly02. -/
lemma conjugationRestriction_add (f g : OneBoson) (u : freeHamiltonian.domain) :
    constructionFieldRestriction (f+g) u = constructionFieldRestriction f u+constructionFieldRestriction g u := by
  simp only [conjugationRestriction_sourceRoot,grossFormFieldMap_add]

lemma conjugationFreeField_action (f g : OneBoson)
    (hj : ∀ j : Fin 3, MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space))
    (hjj : ∀ i j : Fin 3, MemLp (fun k => (k j : ℂ)*(weylMomentumCoefficient f i (hj i)) k) 2 (volume : Measure GW.Space))
    (heven : ∀ᵐ k ∂(volume : Measure GW.Space), ‖f (-k)‖^2 = ‖f k‖^2) (u : freeHamiltonian.domain) :
    (grossWeylCoefficient f).symm
      (freeHamiltonian (conjugationWeylH0Input f hj hjj heven u)+
        constructionFieldRestriction g (conjugationWeylH0Input f hj hjj heven u)) =
      freeHamiltonian u+
        constructionFieldRestriction (g+f+∑ j : Fin 3,weylMomentumCoefficient (weylMomentumCoefficient f j (hj j)) j (hjj j j)) u+
        conjugationRemainder f hj hjj (‖f‖^2+2*(⟪f,g⟫_ℂ).re) u := by
  have hk := conjugationKinetic_on_H0 f hj hjj heven u
  have hn := conjugationNumber_on_H0 f hj hjj heven u
  have hf := conjugationField_on_H0 f g hj hjj heven u
  dsimp only [conjugationNumberInput] at hn
  rw [map_add,grossH0_action_split (conjugationWeylH0Input f hj hjj heven u),map_add,hk,hn,hf]
  rw [conjugationRestriction_add,conjugationRestriction_add,conjugationRemainder_value,grossH0_action_split u]
  simp only [conjugationNumberInput,Complex.ofReal_add,add_smul]
  abel

/- Source argument component Coefficient02. -/
lemma conjugationFiniteCancellation (α K L : ℝ) (hKL : K ≤ L) (k : GW.Space) :
    GW.Model.cutoff α L k+(if ‖k‖ ≤ L then GW.Model.b α K k else 0)+
      ‖k‖^2*(if ‖k‖ ≤ L then GW.Model.b α K k else 0) = GW.Model.cutoff α K k := by
  by_cases h : ‖k‖ ≤ L
  · rw [if_pos h,GW.Model.cutoff,if_pos h]
    exact GW.Model.dressing_cancellation α K k
  · have hK : ¬ ‖k‖ ≤ K := fun hk => h (hk.trans hKL)
    simp only [if_neg h,GW.Model.cutoff,if_neg hK,mul_zero,add_zero]

lemma conjugationFinite_boundary_zero (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    grossFiniteDressingCoefficient α K K hα hK = 0 := by
  apply Lp.ext
  filter_upwards [grossFiniteDressingCoefficient_ae α K K hα hK,
    Lp.coeFn_zero ℂ 2 (volume : Measure GW.Space)] with k hb hz
  rw [hb,hz]
  by_cases hk : k ∈ lowRegion K
  · rw [Set.indicator_of_mem hk,GW.Model.b,if_neg (not_lt.mpr hk),Complex.ofReal_zero]
    rfl
  · rw [Set.indicator_of_notMem hk]
    rfl

/- Source argument component Class03. -/
lemma conjugationFiniteClassCancellation (α K L : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (hL : 0 < L) (hKL : K ≤ L) :
    cutoffL2 α L hα hL+grossFiniteDressingCoefficient α K L hα hK+
      grossFormFiniteSecondRadial (grossDressingCoefficient α K hα hK) L = cutoffL2 α K hα hK := by
  let f := grossFiniteDressingCoefficient α K L hα hK
  let r := grossFormFiniteSecondRadial (grossDressingCoefficient α K hα hK) L
  apply Lp.ext
  filter_upwards [cutoffL2_ae α L hα hL,cutoffL2_ae α K hα hK,
    grossFiniteDressingCoefficient_ae α K L hα hK,
    grossFormFiniteSecondRadial_ae (grossDressingCoefficient α K hα hK) L,
    Lp.coeFn_add (cutoffL2 α L hα hL) f,Lp.coeFn_add (cutoffL2 α L hα hL+f) r] with k h₁ h₂ hb hr ha hz
  change r k = ((‖k‖^2:ℝ):ℂ)*f k at hr
  change (cutoffL2 α L hα hL+f+r) k = _
  rw [hz]
  simp only [Pi.add_apply]
  rw [ha]
  simp only [Pi.add_apply]
  rw [h₁,h₂,hr]
  have he := congrArg (fun x : ℝ => (x:ℂ)) (conjugationFiniteCancellation α K L hKL k)
  simp only [Complex.ofReal_add,Complex.ofReal_mul] at he
  by_cases hk : k ∈ lowRegion L
  · rw [hb,Set.indicator_of_mem hk]
    simpa only [if_pos (show ‖k‖ ≤ L from hk)] using he
  · rw [hb,Set.indicator_of_notMem hk]
    simpa only [if_neg (show ¬ ‖k‖ ≤ L from hk),Complex.ofReal_zero] using he

/- Source argument component Scalar02. -/
lemma conjugationScalar_integral (f g : OneBoson) :
    ‖f‖^2+2*(⟪f,g⟫_ℂ).re = ∫ k, (⟪f k,f k⟫_ℂ).re+2*(⟪f k,g k⟫_ℂ).re ∂(volume : Measure GW.Space) := by
  have h₁ := L2.integrable_inner (𝕜 := ℂ) f f
  have h₂ := L2.integrable_inner (𝕜 := ℂ) f g
  have hn : ‖f‖^2 = (⟪f,f⟫_ℂ).re := norm_sq_eq_re_inner (𝕜 := ℂ) f
  rw [hn,L2.inner_def,L2.inner_def]
  have h₁r : Integrable (fun k => (⟪f k,f k⟫_ℂ).re) (volume : Measure GW.Space) := h₁.re
  have h₂r : Integrable (fun k => (⟪f k,g k⟫_ℂ).re) (volume : Measure GW.Space) := h₂.re
  rw [integral_add h₁r (h₂r.const_mul 2),integral_const_mul]
  have hi₁ := integral_re h₁
  have hi₂ := integral_re h₂
  change (∫ k, (⟪f k,f k⟫_ℂ).re ∂(volume : Measure GW.Space)) = (∫ k, ⟪f k,f k⟫_ℂ ∂(volume : Measure GW.Space)).re at hi₁
  change (∫ k, (⟪f k,g k⟫_ℂ).re ∂(volume : Measure GW.Space)) = (∫ k, ⟪f k,g k⟫_ℂ ∂(volume : Measure GW.Space)).re at hi₂
  rw [hi₁,hi₂]

/- Source argument component Counterterm01. -/
lemma conjugationRealInner (a b : ℝ) : (⟪(a:ℂ),(b:ℂ)⟫_ℂ).re = a*b := by
  simp only [RCLike.inner_apply',Complex.conj_ofReal,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]

def conjugationCountertermDensity (α K L : ℝ) (k : GW.Space) : ℝ :=
  (highRegion K ∩ lowRegion L).indicator
    (fun k => (GW.Model.v α k)^2*(1/(1+‖k‖^2)^2-2/(1+‖k‖^2))) k

def conjugationCounterterm (α K L : ℝ) : ℝ :=
  ∫ k in highRegion K ∩ lowRegion L, (GW.Model.v α k)^2*(1/(1+‖k‖^2)^2-2/(1+‖k‖^2)) ∂(volume : Measure GW.Space)

lemma conjugationCounterterm_density_ae (α K L : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (hL : 0 < L) :
    (fun k => (⟪grossFiniteDressingCoefficient α K L hα hK k,grossFiniteDressingCoefficient α K L hα hK k⟫_ℂ).re+
      2*(⟪grossFiniteDressingCoefficient α K L hα hK k,cutoffL2 α L hα hL k⟫_ℂ).re) =ᵐ[volume]
      conjugationCountertermDensity α K L := by
  filter_upwards [grossFiniteDressingCoefficient_ae α K L hα hK,cutoffL2_ae α L hα hL] with k hb hg
  rw [hb,hg]
  by_cases hl : ‖k‖ ≤ L
  · rw [Set.indicator_of_mem (show k ∈ lowRegion L from hl),GW.Model.cutoff,if_pos hl]
    by_cases hk : K < ‖k‖
    · rw [conjugationCountertermDensity,Set.indicator_of_mem (show k ∈ highRegion K ∩ lowRegion L from ⟨hk,hl⟩)]
      simp only [GW.Model.b,if_pos hk]
      rw [conjugationRealInner,conjugationRealInner]
      have hd : 1+‖k‖^2 ≠ 0 := by positivity
      field_simp [hd]
      <;> ring
    · rw [conjugationCountertermDensity,Set.indicator_of_notMem (show k ∉ highRegion K ∩ lowRegion L from fun h => hk h.1)]
      simp only [GW.Model.b,if_neg hk,Complex.ofReal_zero,inner_zero_left,Complex.zero_re,mul_zero,add_zero]
  · rw [Set.indicator_of_notMem (show k ∉ lowRegion L from hl),GW.Model.cutoff,if_neg hl,
      conjugationCountertermDensity,Set.indicator_of_notMem (show k ∉ highRegion K ∩ lowRegion L from fun h => hl h.2)]
    simp only [inner_zero_left,Complex.zero_re,mul_zero,add_zero]

lemma conjugationCounterterm_integrable (α K L : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (hL : 0 < L) :
    Integrable (conjugationCountertermDensity α K L) (volume : Measure GW.Space) := by
  have h₁ := L2.integrable_inner (𝕜 := ℂ) (grossFiniteDressingCoefficient α K L hα hK) (grossFiniteDressingCoefficient α K L hα hK)
  have h₂ := L2.integrable_inner (𝕜 := ℂ) (grossFiniteDressingCoefficient α K L hα hK) (cutoffL2 α L hα hL)
  exact (h₁.re.add (h₂.re.const_mul 2)).congr (conjugationCounterterm_density_ae α K L hα hK hL)

lemma conjugationCounterterm_eq (α K L : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (hL : 0 < L) :
    ‖grossFiniteDressingCoefficient α K L hα hK‖^2+
      2*(⟪grossFiniteDressingCoefficient α K L hα hK,cutoffL2 α L hα hL⟫_ℂ).re = conjugationCounterterm α K L := by
  rw [conjugationScalar_integral]
  rw [integral_congr_ae (conjugationCounterterm_density_ae α K L hα hK hL)]
  exact integral_indicator ((highRegion_measurable K).inter (lowRegion_measurable L))

/- Source argument component Finite04. -/
def conjugationFiniteRemainder (α K L : ℝ) (hα : 0 ≤ α) (hK : 0 < K) : freeHamiltonian.domain →ₗ[ℂ] Physical :=
  conjugationRemainder (grossFiniteDressingCoefficient α K L hα hK)
    (grossForm_finite_first_memLp (grossDressingCoefficient α K hα hK) L)
    (fun i j => grossForm_finite_second_memLp (grossDressingCoefficient α K hα hK) L j i) (conjugationCounterterm α K L)

def conjugationDressedHamiltonian (α K L : ℝ) (hα : 0 ≤ α) (hK : 0 < K) : Physical →ₗ.[ℂ] Physical :=
  GW.Operators.perturbedOperator freeHamiltonian
    (constructionFieldRestriction (cutoffL2 α K hα hK)+conjugationFiniteRemainder α K L hα hK)

def conjugationFiniteWeylInput (α K L : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (u : freeHamiltonian.domain) : freeHamiltonian.domain :=
  conjugationWeylH0Input (grossFiniteDressingCoefficient α K L hα hK)
    (grossForm_finite_first_memLp (grossDressingCoefficient α K hα hK) L)
    (fun i j => grossForm_finite_second_memLp (grossDressingCoefficient α K hα hK) L j i)
    (grossFiniteSideEven true (grossDressingCoefficient α K hα hK) L (grossForm_coefficient_even α K hα hK)) u

lemma conjugationFinite_action (α K L : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (hL : 0 < L) (hKL : K ≤ L)
    (u : freeHamiltonian.domain) :
    (grossWeylCoefficient (grossFiniteDressingCoefficient α K L hα hK)).symm
      (constructionCutoffHamiltonian α L hα hL (conjugationFiniteWeylInput α K L hα hK u)) =
      conjugationDressedHamiltonian α K L hα hK u := by
  let f₀ := grossDressingCoefficient α K hα hK
  let f := grossFiniteDressingCoefficient α K L hα hK
  let hj := grossForm_finite_first_memLp f₀ L
  let hjj := fun i j => grossForm_finite_second_memLp f₀ L j i
  let heven := grossFiniteSideEven true f₀ L (grossForm_coefficient_even α K hα hK)
  have h := conjugationFreeField_action f (cutoffL2 α L hα hL) hj hjj heven u
  have hm : (∑ j : Fin 3,weylMomentumCoefficient (weylMomentumCoefficient f j (hj j)) j (hjj j j)) =
      grossFormFiniteSecondRadial f₀ L := grossFormSecondCoefficient_sum f₀ L
  have hc : cutoffL2 α L hα hL+f+grossFormFiniteSecondRadial f₀ L = cutoffL2 α K hα hK :=
    conjugationFiniteClassCancellation α K L hα hK hL hKL
  have hC : ‖f‖^2+2*(⟪f,cutoffL2 α L hα hL⟫_ℂ).re = conjugationCounterterm α K L :=
    conjugationCounterterm_eq α K L hα hK hL
  rw [hm,hc,hC] at h
  exact h.trans (add_assoc _ _ _)

/- Source argument component Transport01. -/
lemma conjugationTransport_domain (α K L : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (hL : 0 < L) :
    (GW.Operators.unitaryTransport (grossWeylCoefficient (grossFiniteDressingCoefficient α K L hα hK))
      (constructionCutoffHamiltonian α L hα hL)).domain = freeHamiltonian.domain := by
  rw [GW.Operators.unitaryTransport_domain,constructionCutoffHamiltonian_domain]
  apply SetLike.coe_injective
  rw [Submodule.map_coe]
  exact main_gross_finite_H0_domain_image false α K L hα hK

lemma main_conjugation_operator (α K L : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (hL : 0 < L) (hKL : K ≤ L) :
    GW.Operators.unitaryTransport (grossWeylCoefficient (grossFiniteDressingCoefficient α K L hα hK))
      (constructionCutoffHamiltonian α L hα hL) = conjugationDressedHamiltonian α K L hα hK := by
  let W := grossWeylCoefficient (grossFiniteDressingCoefficient α K L hα hK)
  let A := constructionCutoffHamiltonian α L hα hL
  let T := GW.Operators.unitaryTransport W A
  apply LinearPMap.ext
  · exact conjugationTransport_domain α K L hα hK hL
  · intro x hx hy
    let u : freeHamiltonian.domain := ⟨x,hy⟩
    have hval := conjugationFinite_action α K L hα hK hL hKL u
    have hout : A (conjugationFiniteWeylInput α K L hα hK u) =
        W (conjugationDressedHamiltonian α K L hα hK u) := by
      have h := congrArg W hval
      rw [LinearIsometryEquiv.apply_symm_apply] at h
      exact h
    have hg : (x,conjugationDressedHamiltonian α K L hα hK u) ∈ T.graph := by
      apply (GW.Operators.unitaryTransport_graph_iff W A _).mpr
      exact A.mem_graph_iff.mpr ⟨conjugationFiniteWeylInput α K L hα hK u,rfl,hout⟩
    exact T.mem_graph_snd_inj (T.mem_graph ⟨x,hx⟩) hg rfl

lemma main_conjugation_domain (α K L : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    (conjugationDressedHamiltonian α K L hα hK).domain = freeHamiltonian.domain := rfl

lemma main_conjugation_selfadjoint (α K L : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (hL : 0 < L) (hKL : K ≤ L) :
    GW.IsSelfAdjointOperator (conjugationDressedHamiltonian α K L hα hK) := by
  rw [← main_conjugation_operator α K L hα hK hL hKL]
  exact GW.Operators.unitaryTransport_selfadjoint _ _ (constructionCutoffHamiltonian_selfadjoint α L hα hL)

/- Source argument component Boundary02. -/
lemma conjugationWeyl_zero_apply (U : Physical) : grossWeylCoefficient 0 U = U := by
  apply Lp.ext
  filter_upwards [grossWeylCoefficient_ae 0 U] with x hx
  rw [hx,show phaseAt 0 x = 0 from (weylPhaseIsometry x).map_zero,weyl_zero_apply]

lemma conjugationWeyl_zero : grossWeylCoefficient 0 = LinearIsometryEquiv.refl ℂ Physical := by
  apply LinearIsometryEquiv.ext
  intro U
  exact conjugationWeyl_zero_apply U

lemma conjugationCounterterm_boundary (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    conjugationCounterterm α K K = 0 := by
  have h := conjugationCounterterm_eq α K K hα hK hK
  rw [grossFiniteDressingCoefficient_at_K,norm_zero,inner_zero_left,Complex.zero_re] at h
  simpa using h.symm

/- Source argument component BoundaryOperator01. -/
lemma conjugationTransport_refl (A : Physical →ₗ.[ℂ] Physical) :
    GW.Operators.unitaryTransport (LinearIsometryEquiv.refl ℂ Physical) A = A := by
  apply LinearPMap.ext
  · ext x
    rfl
  · intro x hx hy
    rfl

lemma conjugationBoundary_operator (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    conjugationDressedHamiltonian α K K hα hK = constructionCutoffHamiltonian α K hα hK := by
  have h := main_conjugation_operator α K K hα hK hK le_rfl
  rw [grossFiniteDressingCoefficient_at_K,conjugationWeyl_zero,conjugationTransport_refl] at h
  exact h.symm

lemma conjugationBoundary_remainder (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    conjugationFiniteRemainder α K K hα hK = 0 := by
  apply LinearMap.ext
  intro u
  change conjugationFiniteRemainder α K K hα hK u = 0
  let A := constructionCutoffHamiltonian α K hα hK
  let D := conjugationDressedHamiltonian α K K hα hK
  have hEq : D = A := conjugationBoundary_operator α K hα hK
  have hg : (u.val,D u) ∈ A.graph :=
    (congrArg (fun T : Physical →ₗ.[ℂ] Physical => (u.val,D u) ∈ T.graph) hEq).mp (D.mem_graph u)
  have he := A.mem_graph_snd_inj hg (A.mem_graph u) rfl
  change freeHamiltonian u+(constructionFieldRestriction (cutoffL2 α K hα hK) u+conjugationFiniteRemainder α K K hα hK u) =
    freeHamiltonian u+constructionFieldRestriction (cutoffL2 α K hα hK) u at he
  exact add_left_cancel ((add_left_cancel he).trans (add_zero _).symm)

/- Source argument component Products01. -/
lemma conjugationProducts_graphs (f : OneBoson) (j : Fin 3)
    (hj : MemLp (fun k => (k j : ℂ)*f k) 2 (volume : Measure GW.Space)) (u : freeHamiltonian.domain) :
    (u.val,commutatorPhaseCreatorMap f (commutatorGraphRootMap (conjugationSourceGraph u))) ∈
        (generalizedCreation (phaseMultiplicationKernel f)).graph ∧
    (u.val,commutatorPhaseAnnihilatorMap f (commutatorGraphRootMap (conjugationSourceGraph u))) ∈
        (generalizedAnnihilation (phaseMultiplicationKernel f)).graph ∧
    (commutatorPhaseCreatorMap f (commutatorGraphRootMap (conjugationSourceGraph u)),
      commutatorCreatorRightMap f j hj (conjugationSourceGraph u)) ∈ (electronMomentumCoordinate j).graph ∧
    (commutatorPhaseAnnihilatorMap f (commutatorGraphRootMap (conjugationSourceGraph u)),
      commutatorAnnihilatorRightMap f j hj (conjugationSourceGraph u)) ∈ (electronMomentumCoordinate j).graph ∧
    (electronMomentumCoordinate j (commutatorMomentumInput (conjugationSourceGraph u) j),
      commutatorPhaseCreatorMap f (commutatorGraphMomentumRootMap j (conjugationSourceGraph u))) ∈
        (generalizedCreation (phaseMultiplicationKernel f)).graph ∧
    (electronMomentumCoordinate j (commutatorMomentumInput (conjugationSourceGraph u) j),
      commutatorPhaseAnnihilatorMap f (commutatorGraphMomentumRootMap j (conjugationSourceGraph u))) ∈
        (generalizedAnnihilation (phaseMultiplicationKernel f)).graph ∧
    (u.val,constructionFieldRestriction f u) ∈ (generalizedField (phaseMultiplicationKernel f)).graph ∧
    (constructionFieldRestriction f u,conjugationSquareMap f u) ∈ (generalizedField (phaseMultiplicationKernel f)).graph := by
  have hc := commutatorPhaseCreatorMap_graph f (commutatorGraphRootMap (conjugationSourceGraph u))
  have ha := commutatorPhaseAnnihilatorMap_graph f (commutatorGraphRootMap (conjugationSourceGraph u))
  rw [conjugationSourceRoot_value] at hc ha
  have hpc := commutatorCreator_graph_all f j hj (conjugationSourceGraph u)
  have hpa := commutatorAnnihilator_graph_all f j hj (conjugationSourceGraph u)
  change (commutatorPhaseCreatorMap f (commutatorGraphRootMap (conjugationSourceGraph u)),
    commutatorCreatorRightMap f j hj (conjugationSourceGraph u)) ∈ _ at hpc
  change (commutatorPhaseAnnihilatorMap f (commutatorGraphRootMap (conjugationSourceGraph u)),
    commutatorAnnihilatorRightMap f j hj (conjugationSourceGraph u)) ∈ _ at hpa
  have hcp := commutatorPhaseCreatorMap_graph f (commutatorGraphMomentumRootMap j (conjugationSourceGraph u))
  have hap := commutatorPhaseAnnihilatorMap_graph f (commutatorGraphMomentumRootMap j (conjugationSourceGraph u))
  rw [commutatorGraphMomentumRootMap_value] at hcp hap
  exact ⟨hc,ha,hpc,hpa,hcp,hap,constructionFieldRestriction_graph f u,conjugationSquareMap_graph f u⟩

/- Source argument component Public01. -/
lemma main_conjugation_products (α K L : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (hKL : K ≤ L)
    (u : freeHamiltonian.domain) (j : Fin 3) :
    let f := grossFiniteDressingCoefficient α K L hα hK
    let F := weylMomentumCoefficient f j (grossForm_finite_first_memLp (grossDressingCoefficient α K hα hK) L j)
    let hFj := grossForm_finite_second_memLp (grossDressingCoefficient α K hα hK) L j j
    (u.val,commutatorPhaseCreatorMap F (commutatorGraphRootMap (conjugationSourceGraph u))) ∈
        (generalizedCreation (phaseMultiplicationKernel F)).graph ∧
    (u.val,commutatorPhaseAnnihilatorMap F (commutatorGraphRootMap (conjugationSourceGraph u))) ∈
        (generalizedAnnihilation (phaseMultiplicationKernel F)).graph ∧
    (commutatorPhaseCreatorMap F (commutatorGraphRootMap (conjugationSourceGraph u)),
      commutatorCreatorRightMap F j hFj (conjugationSourceGraph u)) ∈ (electronMomentumCoordinate j).graph ∧
    (commutatorPhaseAnnihilatorMap F (commutatorGraphRootMap (conjugationSourceGraph u)),
      commutatorAnnihilatorRightMap F j hFj (conjugationSourceGraph u)) ∈ (electronMomentumCoordinate j).graph ∧
    (electronMomentumCoordinate j (commutatorMomentumInput (conjugationSourceGraph u) j),
      commutatorPhaseCreatorMap F (commutatorGraphMomentumRootMap j (conjugationSourceGraph u))) ∈
        (generalizedCreation (phaseMultiplicationKernel F)).graph ∧
    (electronMomentumCoordinate j (commutatorMomentumInput (conjugationSourceGraph u) j),
      commutatorPhaseAnnihilatorMap F (commutatorGraphMomentumRootMap j (conjugationSourceGraph u))) ∈
        (generalizedAnnihilation (phaseMultiplicationKernel F)).graph ∧
    (u.val,constructionFieldRestriction F u) ∈ (generalizedField (phaseMultiplicationKernel F)).graph ∧
    (constructionFieldRestriction F u,conjugationSquareMap F u) ∈ (generalizedField (phaseMultiplicationKernel F)).graph := by
  dsimp only
  exact conjugationProducts_graphs
    (weylMomentumCoefficient (grossFiniteDressingCoefficient α K L hα hK) j
      (grossForm_finite_first_memLp (grossDressingCoefficient α K hα hK) L j)) j
    (grossForm_finite_second_memLp (grossDressingCoefficient α K hα hK) L j j) u

lemma main_conjugation (α K L : ℝ) (hα : 0 ≤ α) (hK : 0 < K) (hKL : K ≤ L) :
    GW.Operators.unitaryTransport (grossWeylCoefficient (grossFiniteDressingCoefficient α K L hα hK))
      (constructionCutoffHamiltonian α L hα (hK.trans_le hKL)) = conjugationDressedHamiltonian α K L hα hK ∧
    (conjugationDressedHamiltonian α K L hα hK).domain = freeHamiltonian.domain ∧
    GW.IsSelfAdjointOperator (conjugationDressedHamiltonian α K L hα hK) ∧
    Integrable (conjugationCountertermDensity α K L) (volume : Measure GW.Space) ∧
    conjugationCounterterm α K L = ‖grossFiniteDressingCoefficient α K L hα hK‖^2+
      2*(⟪grossFiniteDressingCoefficient α K L hα hK,cutoffL2 α L hα (hK.trans_le hKL)⟫_ℂ).re :=
  ⟨main_conjugation_operator α K L hα hK (hK.trans_le hKL) hKL,
    main_conjugation_domain α K L hα hK,
    main_conjugation_selfadjoint α K L hα hK (hK.trans_le hKL) hKL,
    conjugationCounterterm_integrable α K L hα hK (hK.trans_le hKL),
    (conjugationCounterterm_eq α K L hα hK (hK.trans_le hKL)).symm⟩

end GW.Gross
