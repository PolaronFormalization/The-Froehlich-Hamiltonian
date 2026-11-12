module
public import GW.Gross.MainGrossForm
/-! Source reg:invariance, manuscript7141–7197.
Actual fractional domains, sharp endpoint interpolation, original Weyl
restrictions and explicit inverse preimages, including zero exponent. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal
namespace GW.Regularity
open GW.Model GW.Fock GW.Analysis GW.Gross

/- Source argument component Endpoint02. -/
lemma regGross_sourceL_pos (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K) :
    0 < grossSourceL α K hα hK := by
  apply Real.sqrt_pos.mpr
  have hb : 0 ≤ grossSourceBeta α K hα hK := norm_nonneg _
  have ha : 0 ≤ grossSourceA α K hα hK := norm_nonneg _
  change 0 < (1+grossSourceBeta α K hα hK)^2+(1+2*grossSourceA α K hα hK)^2
  nlinarith [sq_nonneg (1+2*grossSourceA α K hα hK)]

lemma regGross_form_endpoint (adj : Bool) (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (u : freeFormOperator.domain) :
    ∃ hu : grossWeylSide adj (grossDressingCoefficient α K hα hK) u.val ∈ freeFormOperator.domain,
      ‖freeFormOperator ⟨grossWeylSide adj (grossDressingCoefficient α K hα hK) u.val,hu⟩‖ ≤
        grossSourceL α K hα hK*‖freeFormOperator u‖ := by
  let U : FreeFormDomain := u
  let V := grossSourceQInput adj α K hα hK U
  have hV := grossFormSideInput_value adj (grossDressingCoefficient α K hα hK)
    (grossForm_momentum_memLp α K hα hK) (grossForm_coefficient_even α K hα hK) U
  have hUval : freeFormDomainInclusion U = u.val := freeFormDomainInclusion_apply U
  rw [hUval] at hV
  have hval : V.val = grossWeylSide adj (grossDressingCoefficient α K hα hK) u.val :=
    (freeFormDomainInclusion_apply V).symm.trans hV
  have hm : grossWeylSide adj (grossDressingCoefficient α K hα hK) u.val ∈ freeFormOperator.domain :=
    hval ▸ (show freeFormOperator.domain from V).property
  refine ⟨hm,?_⟩
  have he : (⟨grossWeylSide adj (grossDressingCoefficient α K hα hK) u.val,hm⟩ : freeFormOperator.domain) =
      (show freeFormOperator.domain from V) := Subtype.ext hval.symm
  rw [he,← freeFormDomain_norm V]
  have hU : ‖U‖ = ‖freeFormOperator u‖ := freeFormDomain_norm U
  exact (main_gross_infinite_form_bound adj α K hα hK U).trans_eq (congrArg (fun t : ℝ => grossSourceL α K hα hK*t) hU)

/- Source argument component Fractional02. -/
lemma regGross_fractional_bound (adj : Bool) (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (σ : ℝ) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (u : (freeFractionalOperator σ).domain) :
    ∃ hv : grossWeylSide adj (grossDressingCoefficient α K hα hK) u.val ∈ (freeFractionalOperator σ).domain,
      ‖freeFractionalOperator σ ⟨grossWeylSide adj (grossDressingCoefficient α K hα hK) u.val,hv⟩‖ ≤
        (grossSourceL α K hα hK)^σ*‖freeFractionalOperator σ u‖ := by
  let T : Physical →L[ℂ] Physical := grossWeylSide adj (grossDressingCoefficient α K hα hK)
  let P := physicalSectorMultiplier (fun n q => (freeFormWeight n q)^σ)
  have hT₀ (z : Physical) : ‖T z‖ ≤ (1:ℝ)*‖z‖ := by
    change ‖grossWeylSide adj (grossDressingCoefficient α K hα hK) z‖ ≤ _
    rw [LinearIsometryEquiv.norm_map,one_mul]
  have hum : u.val ∈ P.domain :=
    (congrArg (fun A : Physical →ₗ.[ℂ] Physical => u.val ∈ A.domain)
      (fractionalFormWeight_operator σ)).mpr u.property
  obtain ⟨hm,hb⟩ := fractionalPhysical_interpolation freeFormWeight freeFormWeight_measurable freeFormWeight_one
    T 1 (grossSourceL α K hα hK) zero_lt_one (regGross_sourceL_pos α K hα hK)
    hT₀ (regGross_form_endpoint adj α K hα hK) σ hσ hσ1 u.val hum
  let v := P ⟨u.val,hum⟩
  let w := P ⟨T u.val,hm⟩
  have hgu : (u.val,v) ∈ (freeFractionalOperator σ).graph :=
    (congrArg (fun A : Physical →ₗ.[ℂ] Physical => (u.val,v) ∈ A.graph)
      (fractionalFormWeight_operator σ)).mp (P.mem_graph ⟨u.val,hum⟩)
  have hgw : (T u.val,w) ∈ (freeFractionalOperator σ).graph :=
    (congrArg (fun A : Physical →ₗ.[ℂ] Physical => (T u.val,w) ∈ A.graph)
      (fractionalFormWeight_operator σ)).mp (P.mem_graph ⟨T u.val,hm⟩)
  have hv := (freeFractionalOperator σ).mem_domain_of_mem_graph hgw
  have heu := (freeFractionalOperator σ).mem_graph_snd_inj ((freeFractionalOperator σ).mem_graph u) hgu rfl
  have hew := (freeFractionalOperator σ).mem_graph_snd_inj ((freeFractionalOperator σ).mem_graph ⟨T u.val,hv⟩) hgw rfl
  refine ⟨hv,?_⟩
  change ‖freeFractionalOperator σ ⟨T u.val,hv⟩‖ ≤ (grossSourceL α K hα hK)^σ*‖freeFractionalOperator σ u‖
  rw [heu,hew]
  simpa only [Real.one_rpow,one_mul] using hb

/- Source argument component Domains02. -/
def regGrossQsigma (σ : ℝ) : Submodule ℂ Physical :=
  (electronRadialPower σ).domain ⊓ (physicalNumberPower (σ/2)).domain

lemma regGrossQsigma_eq (σ : ℝ) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    regGrossQsigma σ = (freeFractionalOperator σ).domain := (fractionalFree_domain σ hσ hσ1).symm

lemma regGrossQsigma_zero : regGrossQsigma 0 = ⊤ := by
  rw [regGrossQsigma_eq 0 le_rfl zero_le_one,freeFractionalOperator_zero]
  rfl

lemma regGross_side_inverse (adj : Bool) (f : OneBoson) (U : Physical) :
    grossWeylSide adj f (grossWeylSide (!adj) f U) = U := by
  cases adj
  · exact (grossWeylCoefficient f).symm_apply_apply U
  · exact (grossWeylCoefficient f).apply_symm_apply U

lemma main_gross_fractional_domain_image (adj : Bool) (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (σ : ℝ) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    (grossWeylSide adj (grossDressingCoefficient α K hα hK)) '' (regGrossQsigma σ : Set Physical) =
      (regGrossQsigma σ : Set Physical) := by
  rw [regGrossQsigma_eq σ hσ hσ1]
  apply Set.Subset.antisymm
  · rintro _ ⟨u,hu,rfl⟩
    exact (regGross_fractional_bound adj α K hα hK σ hσ hσ1 ⟨u,hu⟩).choose
  · intro v hv
    have hm := (regGross_fractional_bound (!adj) α K hα hK σ hσ hσ1 ⟨v,hv⟩).choose
    exact ⟨grossWeylSide (!adj) (grossDressingCoefficient α K hα hK) v,hm,
      regGross_side_inverse adj (grossDressingCoefficient α K hα hK) v⟩

lemma main_gross_fractional_bound (adj : Bool) (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (σ : ℝ) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (u : Physical) (hu : u ∈ regGrossQsigma σ) :
    ∃ hσu : u ∈ (freeFractionalOperator σ).domain,
      ∃ hσW : grossWeylSide adj (grossDressingCoefficient α K hα hK) u ∈ (freeFractionalOperator σ).domain,
      ‖freeFractionalOperator σ ⟨grossWeylSide adj (grossDressingCoefficient α K hα hK) u,hσW⟩‖ ≤
        (grossSourceL α K hα hK)^σ*‖freeFractionalOperator σ ⟨u,hσu⟩‖ := by
  have hm : u ∈ (freeFractionalOperator σ).domain := (regGrossQsigma_eq σ hσ hσ1) ▸ hu
  obtain ⟨hW,hb⟩ := regGross_fractional_bound adj α K hα hK σ hσ hσ1 ⟨u,hm⟩
  exact ⟨hm,hW,hb⟩

/- Source argument component Maps02. -/
def regFractionalGraph (σ : ℝ) (hσ : 0 ≤ σ) : GW.Spaces.WeightedGraph Physical ElectronBosonSum :=
  physicalWeightedGraph (fractionalFreeWeight σ) (fractionalFreeWeight_measurable σ) (fractionalFreeWeight_one σ hσ)
abbrev RegFractionalDomain (σ : ℝ) (hσ : 0 ≤ σ) := GW.Spaces.WeightedDomain (regFractionalGraph σ hσ)

lemma regFractional_norm (σ : ℝ) (hσ : 0 ≤ σ) (u : RegFractionalDomain σ hσ) :
    ‖u‖ = ‖freeFractionalOperator σ (show (freeFractionalOperator σ).domain from u)‖ := by
  change ‖freeFourierRepresentation (freeFractionalOperator σ u)‖ = ‖freeFractionalOperator σ u‖
  exact freeFourierRepresentation.norm_map _

def regGrossFractionalInput (adj : Bool) (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (σ : ℝ) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (u : RegFractionalDomain σ hσ) : RegFractionalDomain σ hσ :=
  ⟨grossWeylSide adj (grossDressingCoefficient α K hα hK) (show (freeFractionalOperator σ).domain from u).val,
    (regGross_fractional_bound adj α K hα hK σ hσ hσ1 u).choose⟩

def regGrossFractionalLinear (adj : Bool) (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (σ : ℝ) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) : RegFractionalDomain σ hσ →ₗ[ℂ] RegFractionalDomain σ hσ where
  toFun := regGrossFractionalInput adj α K hα hK σ hσ hσ1
  map_add' u v := Subtype.ext ((grossWeylSide adj (grossDressingCoefficient α K hα hK)).map_add _ _)
  map_smul' c u := by
    apply Subtype.ext
    exact (grossWeylSide adj (grossDressingCoefficient α K hα hK)).map_smul c _

lemma regGrossFractionalInput_bound (adj : Bool) (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (σ : ℝ) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (u : RegFractionalDomain σ hσ) :
    ‖regGrossFractionalInput adj α K hα hK σ hσ hσ1 u‖ ≤ (grossSourceL α K hα hK)^σ*‖u‖ := by
  rw [regFractional_norm,regFractional_norm]
  exact (regGross_fractional_bound adj α K hα hK σ hσ hσ1 u).choose_spec

def regGrossFractionalMap (adj : Bool) (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (σ : ℝ) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) : RegFractionalDomain σ hσ →L[ℂ] RegFractionalDomain σ hσ :=
  (regGrossFractionalLinear adj α K hα hK σ hσ hσ1).mkContinuous ((grossSourceL α K hα hK)^σ)
    (regGrossFractionalInput_bound adj α K hα hK σ hσ hσ1)

lemma regFractionalDomain_complete (σ : ℝ) (hσ : 0 ≤ σ) : CompleteSpace (RegFractionalDomain σ hσ) :=
  inferInstance

lemma regGrossFractionalMap_value (adj : Bool) (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (σ : ℝ) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (u : RegFractionalDomain σ hσ) :
    (regGrossFractionalMap adj α K hα hK σ hσ hσ1 u).val =
      grossWeylSide adj (grossDressingCoefficient α K hα hK) (show (freeFractionalOperator σ).domain from u).val := rfl

lemma main_gross_fractional_restriction_bound (adj : Bool) (α K : ℝ) (hα : 0 ≤ α) (hK : 0 < K)
    (σ : ℝ) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (u : RegFractionalDomain σ hσ) :
    ‖regGrossFractionalMap adj α K hα hK σ hσ hσ1 u‖ ≤ (grossSourceL α K hα hK)^σ*‖u‖ :=
  regGrossFractionalInput_bound adj α K hα hK σ hσ hσ1 u

end GW.Regularity
