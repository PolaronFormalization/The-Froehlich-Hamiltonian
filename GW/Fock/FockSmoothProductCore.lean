module
public import GW.Operators.BasicFourierIntegralCompat
public import GW.Fock.ProductDensity
public import GW.Operators.BasicFree
public import GW.Fock.FockSmoothCore
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal
namespace GW.Fock

lemma smoothProduct_integral_postcomp
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (T : E →L[ℂ] F) (f : GW.Space → E) (hf : Integrable f volume) (q : GW.Space) :
    GW.Analysis.physicalFourierIntegral (fun x => T (f x)) q = T (GW.Analysis.physicalFourierIntegral f q) := by
  unfold GW.Analysis.physicalFourierIntegral
  rw [map_smul,← T.integral_comp_comm (GW.Analysis.physicalPhase_smul_integrable f hf q)]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => (T.map_smul _ _).symm)

lemma smoothProduct_schwartz_postcomp_L2
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (T : E →L[ℂ] F) (f : SchwartzMap GW.Space E) :
    (f.postcompCLM T).toLp 2 (volume : Measure GW.Space) = T.compLp (f.toLp 2 volume) := by
  apply Lp.ext
  filter_upwards [(f.postcompCLM T).coeFn_toLp 2 (volume : Measure GW.Space),
    T.coeFn_compLp (f.toLp 2 (volume : Measure GW.Space)),f.coeFn_toLp 2 (volume : Measure GW.Space)] with x hx hy hz
  rw [hx,hy,hz]
  rfl

lemma smoothProduct_schwartzFourier_postcomp
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (T : E →L[ℂ] F) (f : SchwartzMap GW.Space E) :
    GW.Analysis.schwartzPhysicalFourier (f.postcompCLM T) = (GW.Analysis.schwartzPhysicalFourier f).postcompCLM T := by
  ext q
  rw [GW.Analysis.schwartzPhysicalFourier_apply,SchwartzMap.postcompCLM_apply,
    GW.Analysis.schwartzPhysicalFourier_apply]
  exact smoothProduct_integral_postcomp T f f.integrable q

lemma smoothProduct_fourier_postcomp
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (T : E →L[ℂ] F) (u : Lp E 2 (volume : Measure GW.Space)) :
    GW.Analysis.physicalFourierUnitary (T.compLp u) = T.compLp (GW.Analysis.physicalFourierUnitary u) := by
  have hd := SchwartzMap.denseRange_toLpCLM (E := GW.Space) (F := E) (p := 2)
    (μ := (volume : Measure GW.Space)) (by norm_num)
  refine hd.induction_on u (isClosed_eq
    (GW.Analysis.physicalFourierUnitary.continuous.comp (T.compLpL 2 volume).continuous)
    ((T.compLpL 2 volume).continuous.comp GW.Analysis.physicalFourierUnitary.continuous)) ?_
  intro f
  change GW.Analysis.physicalFourierUnitary (T.compLp (f.toLp 2 volume)) =
    T.compLp (GW.Analysis.physicalFourierUnitary (f.toLp 2 volume))
  rw [← smoothProduct_schwartz_postcomp_L2,GW.Analysis.physicalFourier_schwartz,
    smoothProduct_schwartzFourier_postcomp,smoothProduct_schwartz_postcomp_L2,
    GW.Analysis.physicalFourier_schwartz]

/-- Exactly the source smooth-electron and arbitrary finite-sector Fock products. -/
def smoothFiniteProductGenerators : Set Physical :=
  {u | ∃ (φ : GW.Analysis.SmoothScalarTest) (v : Carrier), v ∈ finiteSectorDomain Sector ∧
    u = (ContinuousLinearMap.toSpanSingleton ℂ v).compLp φ.toL2}

def smoothFiniteProductCore : Submodule ℂ Physical := Submodule.span ℂ smoothFiniteProductGenerators

lemma smoothFiniteProduct_mem (φ : GW.Analysis.SmoothScalarTest) (v : Carrier) (hv : v ∈ finiteSectorDomain Sector) :
    (ContinuousLinearMap.toSpanSingleton ℂ v).compLp φ.toL2 ∈ smoothFiniteProductCore :=
  Submodule.subset_span ⟨φ,v,hv,rfl⟩

lemma smoothProduct_fourier_coordinates (γ : GW.OnePhonon) (v : Carrier) (n : ℕ) :
    freeFourierRepresentation ((ContinuousLinearMap.toSpanSingleton ℂ v).compLp γ) n =
      (ContinuousLinearMap.toSpanSingleton ℂ (v n)).compLp (GW.Analysis.physicalFourierUnitary γ) := by
  rw [← bochnerUnitary_simpleTensor volume Sector γ v]
  change GW.Analysis.physicalFourierUnitary
    ((electronBosonUnitary.symm (electronBosonUnitary (electronSimpleTensor volume Sector γ v))) n) = _
  rw [LinearIsometryEquiv.symm_apply_apply]
  exact smoothProduct_fourier_postcomp (ContinuousLinearMap.toSpanSingleton ℂ (v n)) γ

lemma smoothProduct_fourier_coordinates_ae (γ : GW.OnePhonon) (v : Carrier) (n : ℕ) :
    freeFourierRepresentation ((ContinuousLinearMap.toSpanSingleton ℂ v).compLp γ) n =ᵐ[volume]
      (fun q => GW.Analysis.physicalFourierUnitary γ q • v n) := by
  rw [smoothProduct_fourier_coordinates]
  exact (ContinuousLinearMap.toSpanSingleton ℂ (v n)).coeFn_compLp _

lemma smoothProduct_multiplier_graph (w : ℕ → GW.Space → ℝ) (u z : Physical)
    (h : ∀ n, (fun q => (w n q:ℂ) • freeFourierRepresentation u n q) =ᵐ[volume]
      freeFourierRepresentation z n) : (u,z) ∈ (physicalSectorMultiplier w).graph := by
  have hu : u ∈ (physicalSectorMultiplier w).domain :=
    (physicalSectorMultiplier_domain w u).mpr ⟨freeFourierRepresentation z,h⟩
  refine (physicalSectorMultiplier w).mem_graph_iff.mpr ⟨⟨u,hu⟩,rfl,?_⟩
  apply freeFourierRepresentation.injective
  apply lp.ext
  funext n
  apply Lp.ext
  exact (physicalSectorMultiplier_action w ⟨u,hu⟩ n).symm.trans (h n)

lemma smoothProduct_momentumSquare_fourier_ae
    (γ : (GW.Analysis.absoluteMomentumPower (H := ℂ) 2).domain) :
    GW.Analysis.physicalFourierUnitary (GW.Analysis.absoluteMomentumPower 2 γ) =ᵐ[volume]
      (fun q => ((‖q‖^2:ℝ):ℂ)*GW.Analysis.physicalFourierUnitary γ.val q) := by
  let a : (GW.Analysis.realMultiplier (H := ℂ) (fun q : GW.Space => ‖q‖^(2:ℝ)) volume).domain :=
    ⟨GW.Analysis.physicalFourierUnitary γ.val,γ.property⟩
  have he : GW.Analysis.physicalFourierUnitary (GW.Analysis.absoluteMomentumPower 2 γ) =
      GW.Analysis.realMultiplier (fun q : GW.Space => ‖q‖^(2:ℝ)) volume a :=
    GW.Analysis.fourierMultiplier_action (fun q => ‖q‖^(2:ℝ)) ⟨γ.val,γ.property⟩
  rw [he]
  simpa only [Real.rpow_two,smul_eq_mul] using
    (GW.Analysis.realMultiplier_ae (fun q => ‖q‖^(2:ℝ)) a).symm

lemma smoothProduct_graph_action
    (γ : (GW.Analysis.absoluteMomentumPower (H := ℂ) 2).domain)
    (v : (shiftedNumberPower Sector 1).domain) :
    ((ContinuousLinearMap.toSpanSingleton ℂ v.val).compLp γ.val,
      (ContinuousLinearMap.toSpanSingleton ℂ v.val).compLp (GW.Analysis.absoluteMomentumPower 2 γ)+
      (ContinuousLinearMap.toSpanSingleton ℂ (shiftedNumberPower Sector 1 v)).compLp γ.val) ∈ freeGraphOperator.graph := by
  apply smoothProduct_multiplier_graph
  intro n
  let a := freeFourierRepresentation
    ((ContinuousLinearMap.toSpanSingleton ℂ v.val).compLp (GW.Analysis.absoluteMomentumPower 2 γ)) n
  let b := freeFourierRepresentation
    ((ContinuousLinearMap.toSpanSingleton ℂ (shiftedNumberPower Sector 1 v)).compLp γ.val) n
  have he : freeFourierRepresentation
      ((ContinuousLinearMap.toSpanSingleton ℂ v.val).compLp (GW.Analysis.absoluteMomentumPower 2 γ)+
      (ContinuousLinearMap.toSpanSingleton ℂ (shiftedNumberPower Sector 1 v)).compLp γ.val) n = a+b := by
    simp only [map_add,lp.coeFn_add,Pi.add_apply]
    rfl
  rw [he]
  filter_upwards [smoothProduct_fourier_coordinates_ae γ.val v.val n,
    smoothProduct_fourier_coordinates_ae (GW.Analysis.absoluteMomentumPower 2 γ) v.val n,
    smoothProduct_fourier_coordinates_ae γ.val (shiftedNumberPower Sector 1 v) n,
    Lp.coeFn_add a b,smoothProduct_momentumSquare_fourier_ae γ] with q h₀ h₁ h₂ h₃ h₄
  rw [h₀,h₃]
  change (freeGraphWeight n q:ℂ) • (GW.Analysis.physicalFourierUnitary γ.val q • v.val n) = a q+b q
  change a q = GW.Analysis.physicalFourierUnitary (GW.Analysis.absoluteMomentumPower 2 γ) q • v.val n at h₁
  change b q = GW.Analysis.physicalFourierUnitary γ.val q • shiftedNumberPower Sector 1 v n at h₂
  rw [h₁,h₂,h₄,shiftedNumberPower_apply,Real.rpow_one]
  simp only [freeGraphWeight,freeEnergySymbol,smul_smul,← add_smul]
  congr 1
  push_cast
  ring

lemma smoothProduct_graph_domain
    (γ : (GW.Analysis.absoluteMomentumPower (H := ℂ) 2).domain)
    (v : (shiftedNumberPower Sector 1).domain) :
    (ContinuousLinearMap.toSpanSingleton ℂ v.val).compLp γ.val ∈ freeGraphOperator.domain := by
  obtain ⟨u,hu,_⟩ := freeGraphOperator.mem_graph_iff.mp (smoothProduct_graph_action γ v)
  have he : u.val = (ContinuousLinearMap.toSpanSingleton ℂ v.val).compLp γ.val := hu
  rw [← he]
  exact u.property

def smoothProductGraphInput
    (γ : (GW.Analysis.absoluteMomentumPower (H := ℂ) 2).domain)
    (v : (shiftedNumberPower Sector 1).domain) : FreeGraphDomain :=
  show freeGraphOperator.domain from ⟨(ContinuousLinearMap.toSpanSingleton ℂ v.val).compLp γ.val,
    smoothProduct_graph_domain γ v⟩

lemma smoothProductGraphInput_action
    (γ : (GW.Analysis.absoluteMomentumPower (H := ℂ) 2).domain)
    (v : (shiftedNumberPower Sector 1).domain) :
    freeGraphOperator (smoothProductGraphInput γ v) =
      (ContinuousLinearMap.toSpanSingleton ℂ v.val).compLp (GW.Analysis.absoluteMomentumPower 2 γ)+
      (ContinuousLinearMap.toSpanSingleton ℂ (shiftedNumberPower Sector 1 v)).compLp γ.val :=
  freeGraphOperator.mem_graph_snd_inj (freeGraphOperator.mem_graph (smoothProductGraphInput γ v))
    (smoothProduct_graph_action γ v) rfl

lemma smoothProductGraphInput_norm
    (γ : (GW.Analysis.absoluteMomentumPower (H := ℂ) 2).domain)
    (v : (shiftedNumberPower Sector 1).domain) :
    ‖smoothProductGraphInput γ v‖ ≤ ‖GW.Analysis.absoluteMomentumPower 2 γ‖*‖v.val‖+
      ‖γ.val‖*‖shiftedNumberPower Sector 1 v‖ := by
  rw [freeGraphDomain_norm,smoothProductGraphInput_action]
  exact (norm_add_le _ _).trans (by rw [simpleTensor_norm,simpleTensor_norm])

def smoothProductReciprocalScalar (n : ℕ) (g : GW.OnePhonon) : GW.OnePhonon :=
  GW.Analysis.physicalFourierUnitary.symm
    (GW.Spaces.reciprocalMap (freeGraphWeight_measurable n) (freeGraphWeight_one n) g)

lemma smoothProductReciprocalScalar_fourier (n : ℕ) (g : GW.OnePhonon) :
    GW.Analysis.physicalFourierUnitary (smoothProductReciprocalScalar n g) =
      GW.Spaces.reciprocalMap (freeGraphWeight_measurable n) (freeGraphWeight_one n) g :=
  GW.Analysis.physicalFourierUnitary.apply_symm_apply _

lemma smoothProductReciprocalScalar_mem (n : ℕ) (g : GW.OnePhonon) :
    smoothProductReciprocalScalar n g ∈ (GW.Analysis.absoluteMomentumPower (H := ℂ) 2).domain := by
  let f := GW.Spaces.reciprocalMap (freeGraphWeight_measurable n) (freeGraphWeight_one n) g
  have hf : f ∈ (GW.Analysis.realMultiplier (freeGraphWeight n) volume).domain :=
    GW.Spaces.reciprocalMap_mem_domain (freeGraphWeight_measurable n) (freeGraphWeight_one n) g
  have hdom := realMultiplier_domination (volume : Measure GW.Space) (fun q => ‖q‖^2) (freeGraphWeight n)
    (continuous_norm.pow 2).measurable (C := 1) zero_le_one
    (fun q => by
      rw [abs_of_nonneg (sq_nonneg _),abs_of_nonneg (zero_le_one.trans (freeGraphWeight_one n q)),one_mul]
      unfold freeGraphWeight freeEnergySymbol
      nlinarith [Nat.cast_nonneg (α := ℝ) n]) ⟨f,hf⟩
  apply (GW.Analysis.fourierMultiplier_domain (fun q => ‖q‖^(2:ℝ)) (smoothProductReciprocalScalar n g)).mpr
  rw [smoothProductReciprocalScalar_fourier]
  simpa only [Real.rpow_two] using (GW.Analysis.realMultiplier_domain (fun q => ‖q‖^2) f).mp hdom.choose

lemma smoothProduct_form_le_graph (u : freeGraphOperator.domain) :
    ∃ hu : u.val ∈ freeFormOperator.domain,
      ‖freeFormOperator ⟨u.val,hu⟩‖ ≤ ‖freeGraphOperator u‖ := by
  have h := physicalSectorMultiplier_domination freeFormWeight freeGraphWeight freeFormWeight_measurable
    (C := 1) zero_le_one (fun n q => by
      have hw := freeGraphWeight_one n q
      have hw0 : 0 ≤ freeGraphWeight n q := zero_le_one.trans hw
      change |Real.sqrt (freeGraphWeight n q)| ≤ 1 * |freeGraphWeight n q|
      rw [abs_of_nonneg (Real.sqrt_nonneg _),abs_of_nonneg hw0,one_mul]
      apply Real.sqrt_le_iff.mpr
      exact ⟨hw0,by nlinarith⟩) u
  simpa only [freeFormOperator,freeGraphOperator,one_mul] using h

def smoothProductGraphToForm (u : FreeGraphDomain) : FreeFormDomain :=
  show freeFormOperator.domain from
    ⟨(show freeGraphOperator.domain from u).val,(smoothProduct_form_le_graph u).choose⟩

lemma smoothProductGraphToForm_norm (u : FreeGraphDomain) : ‖smoothProductGraphToForm u‖ ≤ ‖u‖ := by
  rw [freeFormDomain_norm,freeGraphDomain_norm]
  exact (smoothProduct_form_le_graph u).choose_spec

def smoothProductGraphToFormLinear : FreeGraphDomain →ₗ[ℂ] FreeFormDomain where
  toFun := smoothProductGraphToForm
  map_add' _ _ := by apply Subtype.ext; rfl
  map_smul' _ _ := by apply Subtype.ext; rfl

def smoothProductGraphToFormMap : FreeGraphDomain →L[ℂ] FreeFormDomain :=
  smoothProductGraphToFormLinear.mkContinuous 1 (fun u => by
    change ‖smoothProductGraphToForm u‖ ≤ 1*‖u‖
    simpa only [one_mul] using smoothProductGraphToForm_norm u)

lemma smoothProductGraphToForm_inclusion (u : FreeGraphDomain) :
    freeFormDomainInclusion (smoothProductGraphToFormMap u) = freeGraphDomainInclusion u := by
  rw [freeFormDomainInclusion_apply,freeGraphDomainInclusion_apply]
  rfl

lemma smoothProduct_reciprocal_ae
    {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (μ : Measure X) (w : X → ℝ) (hw : Measurable w) (hw1 : ∀ x, 1 ≤ w x) (u : Lp H 2 μ) :
    (fun x => (((w x)⁻¹:ℝ):ℂ) • u x) =ᵐ[μ] GW.Spaces.reciprocalMap hw hw1 u :=
  GW.Analysis.boundedMultiplier_ae _ _ _ _

lemma smoothProduct_reciprocal_postcomp
    {X E F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (μ : Measure X) (w : X → ℝ) (hw : Measurable w) (hw1 : ∀ x, 1 ≤ w x)
    (T : E →L[ℂ] F) (g : Lp E 2 μ) :
    GW.Spaces.reciprocalMap hw hw1 (T.compLp g) = T.compLp (GW.Spaces.reciprocalMap hw hw1 g) := by
  apply Lp.ext
  filter_upwards [smoothProduct_reciprocal_ae μ w hw hw1 (T.compLp g),
    smoothProduct_reciprocal_ae μ w hw hw1 g,T.coeFn_compLp g,
    T.coeFn_compLp (GW.Spaces.reciprocalMap hw hw1 g)] with x h₁ h₂ h₃ h₄
  rw [← h₁,h₃,h₄,← h₂,map_smul]

def smoothProductSmoothInput (φ : GW.Analysis.SmoothScalarTest) (v : Carrier)
    (hv : v ∈ finiteSectorDomain Sector) : FreeGraphDomain :=
  smoothProductGraphInput ⟨φ.toL2,GW.Analysis.smoothCoreTest_square_mem φ⟩
    ⟨v,(finiteSectorDomain_le Sector (fun n => ((n:ℝ)+1)^(1:ℝ))) hv⟩

lemma smoothProductSmoothInput_ambient (φ : GW.Analysis.SmoothScalarTest) (v : Carrier)
    (hv : v ∈ finiteSectorDomain Sector) :
    freeGraphDomainInclusion (smoothProductSmoothInput φ v hv) =
      (ContinuousLinearMap.toSpanSingleton ℂ v).compLp φ.toL2 := by
  rw [freeGraphDomainInclusion_apply]
  rfl

lemma smoothFiniteProductCore_le_H0 : smoothFiniteProductCore ≤ freeHamiltonian.domain := by
  apply Submodule.span_le.mpr
  rintro u ⟨φ,v,hv,rfl⟩
  rw [← freeGraphOperator_domain]
  exact smoothProduct_graph_domain ⟨φ.toL2,GW.Analysis.smoothCoreTest_square_mem φ⟩
    ⟨v,(finiteSectorDomain_le Sector (fun n => ((n:ℝ)+1)^(1:ℝ))) hv⟩

def smoothFiniteGraphCore : Submodule ℂ FreeGraphDomain :=
  smoothFiniteProductCore.comap freeGraphDomainInclusion.toLinearMap

def smoothFiniteFormCore : Submodule ℂ FreeFormDomain :=
  smoothFiniteProductCore.comap freeFormDomainInclusion.toLinearMap

lemma smoothProductSmoothInput_mem (φ : GW.Analysis.SmoothScalarTest) (v : Carrier)
    (hv : v ∈ finiteSectorDomain Sector) : smoothProductSmoothInput φ v hv ∈ smoothFiniteGraphCore := by
  change freeGraphDomainInclusion (smoothProductSmoothInput φ v hv) ∈ smoothFiniteProductCore
  rw [smoothProductSmoothInput_ambient]
  exact smoothFiniteProduct_mem φ v hv

lemma smoothProductGraphInput_sub
    (γ η : (GW.Analysis.absoluteMomentumPower (H := ℂ) 2).domain)
    (v : (shiftedNumberPower Sector 1).domain) :
    smoothProductGraphInput γ v-smoothProductGraphInput η v = smoothProductGraphInput (γ-η) v := by
  apply Subtype.ext
  exact ((ContinuousLinearMap.toSpanSingleton ℂ v.val).compLpL 2 volume).map_sub γ.val η.val |>.symm

lemma smoothProductGraphInput_distance
    (γ η : (GW.Analysis.absoluteMomentumPower (H := ℂ) 2).domain)
    (v : (shiftedNumberPower Sector 1).domain) :
    ‖smoothProductGraphInput γ v-smoothProductGraphInput η v‖ ≤
      ‖GW.Analysis.absoluteMomentumPower 2 γ-GW.Analysis.absoluteMomentumPower 2 η‖*‖v.val‖+
      ‖γ.val-η.val‖*‖shiftedNumberPower Sector 1 v‖ := by
  rw [smoothProductGraphInput_sub]
  have he : GW.Analysis.absoluteMomentumPower 2 (γ-η) =
      GW.Analysis.absoluteMomentumPower 2 γ-GW.Analysis.absoluteMomentumPower 2 η :=
    (GW.Analysis.absoluteMomentumPower 2).toFun.map_sub γ η
  have hb := smoothProductGraphInput_norm (γ-η) v
  rw [he] at hb
  exact hb

lemma smoothProductGraphInput_mem_closure
    (γ : (GW.Analysis.absoluteMomentumPower (H := ℂ) 2).domain)
    (v : (shiftedNumberPower Sector 1).domain) (hv : v.val ∈ finiteSectorDomain Sector) :
    smoothProductGraphInput γ v ∈ smoothFiniteGraphCore.topologicalClosure := by
  change smoothProductGraphInput γ v ∈ closure (smoothFiniteGraphCore : Set FreeGraphDomain)
  rw [Metric.mem_closure_iff]
  intro ε hε
  let K : ℝ := ‖v.val‖+‖shiftedNumberPower Sector 1 v‖+1
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨φ,η,hη,herr⟩ := GW.Analysis.smoothCore_square_graph_dense γ (ε/K) (div_pos hε hK)
  have hy : smoothProductGraphInput η v = smoothProductSmoothInput φ v.val hv := by
    apply Subtype.ext
    exact congrArg (fun f : GW.OnePhonon => (ContinuousLinearMap.toSpanSingleton ℂ v.val).compLp f) hη
  refine ⟨smoothProductGraphInput η v,hy.symm ▸ smoothProductSmoothInput_mem φ v.val hv,?_⟩
  rw [dist_eq_norm]
  have hb := smoothProductGraphInput_distance γ η v
  have hrev₁ : ‖γ.val-η.val‖ = ‖η.val-γ.val‖ := norm_sub_rev _ _
  have hrev₂ : ‖GW.Analysis.absoluteMomentumPower 2 γ-GW.Analysis.absoluteMomentumPower 2 η‖ =
      ‖GW.Analysis.absoluteMomentumPower 2 η-GW.Analysis.absoluteMomentumPower 2 γ‖ := norm_sub_rev _ _
  rw [hrev₁,hrev₂] at hb
  have hsmall := (mul_lt_mul_of_pos_right herr hK)
  have he : (ε/K)*K = ε := div_mul_cancel₀ ε (ne_of_gt hK)
  rw [he] at hsmall
  dsimp [K] at hsmall
  nlinarith [norm_nonneg (η.val-γ.val),
    norm_nonneg (GW.Analysis.absoluteMomentumPower 2 η-GW.Analysis.absoluteMomentumPower 2 γ),
    mul_nonneg (norm_nonneg (η.val-γ.val)) (norm_nonneg v.val),
    mul_nonneg (norm_nonneg (GW.Analysis.absoluteMomentumPower 2 η-GW.Analysis.absoluteMomentumPower 2 γ))
      (norm_nonneg (shiftedNumberPower Sector 1 v))]

/-- The source weighted simple-function approximation, in actual free graph
coordinates. Indicator preimages are the only generator obligation. -/
lemma smoothProduct_graph_closed_criterion (C : Submodule ℂ FreeGraphDomain)
    (hC : IsClosed (C : Set FreeGraphDomain))
    (hind : ∀ (n : ℕ) (A : Set GW.Space) (hA : MeasurableSet A)
      (hf : (volume : Measure GW.Space) A ≠ ∞) (v : Sector n),
      (GW.Spaces.weightedDomainIsometry freeGraphWeightedGraph).symm
        (lp.single 2 n (indicatorConstLp 2 hA hf v)) ∈ C) : C = ⊤ := by
  let e := GW.Spaces.weightedDomainIsometry freeGraphWeightedGraph
  have hsector : ∀ (n : ℕ) (f : Lp (Sector n) 2 (volume : Measure GW.Space)),
      e.symm (lp.single 2 n f) ∈ C := by
    intro n f
    let L : Lp (Sector n) 2 (volume : Measure GW.Space) →L[ℂ] FreeGraphDomain :=
      e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (lp.singleContinuousLinearMap ℂ (fun n => Lp (Sector n) 2 (volume : Measure GW.Space)) 2 n)
    change L f ∈ C
    refine (Lp.simpleFunc.denseRange (E := Sector n) (μ := (volume : Measure GW.Space))
      (p := 2) (by norm_num)).induction_on f (hC.preimage L.continuous) ?_
    intro sf
    refine Lp.simpleFunc.induction (p := 2) (by norm_num) (by norm_num) ?_ ?_ sf
    · intro v A hA hf
      exact hind n A hA hf.ne v
    · intro f g hf hg hd hfc hgc
      change L ((SimpleFunc.toLp f hf).val+(SimpleFunc.toLp g hg).val) ∈ C
      rw [map_add]
      exact C.add_mem hfc hgc
  apply top_unique
  intro U hU
  have hfinite : ∀ m, e.symm (cutoff (fun n => Lp (Sector n) 2 volume) m (e U)) ∈ C := by
    intro m
    rw [cutoff_sum,map_sum]
    exact C.sum_mem (fun n _ => hsector n (e U n))
  have ht := e.symm.continuous.tendsto (e U) |>.comp
    (cutoff_tendsto (fun n => Lp (Sector n) 2 volume) (e U))
  have ht' : Tendsto (fun m => e.symm (cutoff (fun n => Lp (Sector n) 2 volume) m (e U)))
      atTop (𝓝 U) := by
    simpa only [LinearIsometryEquiv.symm_apply_apply,Function.comp_def] using ht
  exact hC.mem_of_tendsto ht' (Eventually.of_forall hfinite)

set_option maxHeartbeats 800000 in
lemma smoothProduct_sumReciprocal_single (n : ℕ)
    (g : Lp (Sector n) 2 (volume : Measure GW.Space)) :
    GW.Spaces.sumReciprocal (F := Sector) (fun _ : ℕ => (volume : Measure GW.Space))
      freeGraphWeight_measurable freeGraphWeight_one (lp.single 2 n g) =
    lp.single 2 n (GW.Spaces.reciprocalMap (freeGraphWeight_measurable n) (freeGraphWeight_one n) g) := by
  apply lp.ext
  funext m
  change GW.Spaces.reciprocalMap (freeGraphWeight_measurable m) (freeGraphWeight_one m)
    ((lp.single (E := fun j => Lp (Sector j) 2 (volume : Measure GW.Space)) 2 n g) m) = _
  by_cases hm : m = n
  · subst m
    rw [lp.single_apply_self,lp.single_apply_self]
  · rw [lp.single_apply_ne _ _ _ hm,lp.single_apply_ne _ _ _ hm,map_zero]

lemma smoothProduct_embedding_single (n : ℕ) (g : GW.OnePhonon) (v : Sector n) :
    physicalWeightEmbedding freeGraphWeight freeGraphWeight_measurable freeGraphWeight_one
      (lp.single 2 n ((ContinuousLinearMap.toSpanSingleton ℂ v).compLp g)) =
    (ContinuousLinearMap.toSpanSingleton ℂ (lp.single 2 n v)).compLp (smoothProductReciprocalScalar n g) := by
  apply freeFourierRepresentation.injective
  rw [physicalWeightEmbedding_fourier,smoothProduct_sumReciprocal_single]
  apply lp.ext
  funext m
  rw [smoothProduct_fourier_coordinates,smoothProductReciprocalScalar_fourier]
  by_cases hm : m = n
  · subst m
    rw [lp.single_apply_self,lp.single_apply_self]
    exact smoothProduct_reciprocal_postcomp volume (freeGraphWeight n)
      (freeGraphWeight_measurable n) (freeGraphWeight_one n) (ContinuousLinearMap.toSpanSingleton ℂ v) g
  · rw [lp.single_apply_ne _ _ _ hm,lp.single_apply_ne _ _ _ hm]
    apply Lp.ext
    filter_upwards [Lp.coeFn_zero (Sector m) 2 (volume : Measure GW.Space), (ContinuousLinearMap.toSpanSingleton ℂ (0 : Sector m)).coeFn_compLp
      (GW.Spaces.reciprocalMap (freeGraphWeight_measurable n) (freeGraphWeight_one n) g)] with q hz hq
    rw [hz,hq]
    simp only [Pi.zero_apply,ContinuousLinearMap.toSpanSingleton_apply,smul_zero]

lemma smoothProduct_single_finite (n : ℕ) (v : Sector n) : lp.single 2 n v ∈ finiteSectorDomain Sector := by
  apply (finiteSectorDomain_iff Sector _).mpr
  exact ⟨n,fun j hj => lp.single_apply_ne 2 n v (ne_of_gt hj)⟩

def smoothProductReciprocalGraph (n : ℕ) (g : GW.OnePhonon) (v : Sector n) : FreeGraphDomain :=
  smoothProductGraphInput ⟨smoothProductReciprocalScalar n g,smoothProductReciprocalScalar_mem n g⟩
    ⟨lp.single 2 n v,(finiteSectorDomain_le Sector (fun n => ((n:ℝ)+1)^(1:ℝ))) (smoothProduct_single_finite n v)⟩

set_option backward.isDefEq.respectTransparency.types false in
lemma smoothProduct_inverse_single (n : ℕ) (g : GW.OnePhonon) (v : Sector n) :
    (GW.Spaces.weightedDomainIsometry freeGraphWeightedGraph).symm
      (lp.single 2 n ((ContinuousLinearMap.toSpanSingleton ℂ v).compLp g)) =
    smoothProductReciprocalGraph n g v := by
  apply Subtype.ext
  have he := GW.Spaces.weightedDomain_embedding freeGraphWeightedGraph
    ((GW.Spaces.weightedDomainIsometry freeGraphWeightedGraph).symm
      (lp.single 2 n ((ContinuousLinearMap.toSpanSingleton ℂ v).compLp g)))
  change freeGraphWeightedGraph.embedding
      ((GW.Spaces.weightedDomainIsometry freeGraphWeightedGraph)
        ((GW.Spaces.weightedDomainIsometry freeGraphWeightedGraph).symm
          (lp.single 2 n ((ContinuousLinearMap.toSpanSingleton ℂ v).compLp g)))) = _ at he
  rw [LinearIsometryEquiv.apply_symm_apply] at he
  exact he.symm.trans (smoothProduct_embedding_single n g v)

lemma smoothFiniteGraphCore_closure : smoothFiniteGraphCore.topologicalClosure = ⊤ := by
  apply smoothProduct_graph_closed_criterion _ smoothFiniteGraphCore.isClosed_topologicalClosure
  intro n A hA hf v
  let g : GW.OnePhonon := indicatorConstLp 2 hA hf (1 : ℂ)
  have hi : (ContinuousLinearMap.toSpanSingleton ℂ v).compLp g = indicatorConstLp 2 hA hf v := by
    simpa only [g,ContinuousLinearMap.toSpanSingleton_apply,one_smul] using
      compLp_indicatorConst volume hA hf (ContinuousLinearMap.toSpanSingleton ℂ v) (1 : ℂ)
  rw [← hi,smoothProduct_inverse_single]
  exact smoothProductGraphInput_mem_closure
    ⟨smoothProductReciprocalScalar n g,smoothProductReciprocalScalar_mem n g⟩
    ⟨lp.single 2 n v,(finiteSectorDomain_le Sector (fun n => ((n:ℝ)+1)^(1:ℝ)))
      (smoothProduct_single_finite n v)⟩ (smoothProduct_single_finite n v)

lemma smoothFiniteGraphCore_dense : Dense (smoothFiniteGraphCore : Set FreeGraphDomain) := by
  intro u
  change u ∈ smoothFiniteGraphCore.topologicalClosure
  rw [smoothFiniteGraphCore_closure]
  trivial

lemma smoothFiniteGraphCore_sequence (u : FreeGraphDomain) :
    ∃ v : ℕ → FreeGraphDomain, (∀ m, v m ∈ smoothFiniteGraphCore) ∧ Tendsto v atTop (𝓝 u) :=
  mem_closure_iff_seq_limit.mp (smoothFiniteGraphCore_dense u)

def smoothProductFormCutoffGraph (m : ℕ) (u : FreeFormDomain) : FreeGraphDomain :=
  show freeGraphOperator.domain from
    ⟨freeCutoff m ((show freeFormOperator.domain from u).val),
      (congrArg (fun V : Submodule ℂ Physical =>
        freeCutoff m ((show freeFormOperator.domain from u).val) ∈ V) freeGraphOperator_domain).mpr
          (freeCutoff_mem_H0 m ((show freeFormOperator.domain from u).val))⟩

lemma smoothProductFormCutoffGraph_form (m : ℕ) (u : FreeFormDomain) :
    smoothProductGraphToFormMap (smoothProductFormCutoffGraph m u) = freeFormCutoff m u := by
  apply Subtype.ext
  rfl

lemma smoothProductGraphToForm_mem (v : FreeGraphDomain) (hv : v ∈ smoothFiniteGraphCore) :
    smoothProductGraphToFormMap v ∈ smoothFiniteFormCore := by
  change freeFormDomainInclusion (smoothProductGraphToFormMap v) ∈ smoothFiniteProductCore
  rw [smoothProductGraphToForm_inclusion]
  exact hv

/-- The source second approximation, with graph error 1/(m+1) after the
particle/momentum cutoff. Both errors are measured in their actual norms. -/
lemma smoothFiniteFormCore_sequence (u : FreeFormDomain) :
    ∃ v : ℕ → FreeFormDomain, (∀ m, v m ∈ smoothFiniteFormCore) ∧ Tendsto v atTop (𝓝 u) := by
  have ha (m : ℕ) : ∃ v : FreeGraphDomain, v ∈ smoothFiniteGraphCore ∧
      ‖v-smoothProductFormCutoffGraph m u‖ < 1/((m:ℝ)+1) := by
    obtain ⟨v,hv,hd⟩ := Metric.mem_closure_iff.mp
      (smoothFiniteGraphCore_dense (smoothProductFormCutoffGraph m u))
      (1/((m:ℝ)+1)) (by positivity)
    refine ⟨v,hv,?_⟩
    rw [dist_eq_norm,norm_sub_rev] at hd
    exact hd
  choose v hv hclose using ha
  let w (m : ℕ) := smoothProductGraphToFormMap (v m)
  refine ⟨w,fun m => smoothProductGraphToForm_mem (v m) (hv m),?_⟩
  have hb (m : ℕ) : ‖w m-freeFormCutoff m u‖ ≤ 1/((m:ℝ)+1) := by
    rw [← smoothProductFormCutoffGraph_form]
    change ‖smoothProductGraphToFormMap (v m)-
      smoothProductGraphToFormMap (smoothProductFormCutoffGraph m u)‖ ≤ _
    rw [← map_sub]
    exact (smoothProductGraphToForm_norm (v m-smoothProductFormCutoffGraph m u)).trans (hclose m).le
  have he : Tendsto (fun m : ℕ => 1/((m:ℝ)+1)) atTop (𝓝 (0:ℝ)) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
      (show Tendsto (fun m : ℕ => (m:ℝ)+1) atTop atTop from
        tendsto_atTop_mono (fun m => le_add_of_nonneg_right (by norm_num : (0:ℝ) ≤ 1)) tendsto_natCast_atTop_atTop)
  have hc : Tendsto (fun m => ‖freeFormCutoff m u-u‖) atTop (𝓝 (0:ℝ)) := by
    simpa only [sub_self,norm_zero] using ((freeFormCutoff_tendsto u).sub (tendsto_const_nhds (x := u))).norm
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun m => norm_nonneg _) _ (by simpa only [zero_add] using he.add hc)
  intro m
  exact (norm_sub_le_norm_sub_add_norm_sub (w m) (freeFormCutoff m u) u).trans
    (add_le_add (hb m) (le_refl ‖freeFormCutoff m u-u‖))

lemma smoothFiniteFormCore_dense : Dense (smoothFiniteFormCore : Set FreeFormDomain) := by
  intro u
  obtain ⟨v,hv,ht⟩ := smoothFiniteFormCore_sequence u
  exact mem_closure_of_tendsto ht (Eventually.of_forall hv)

def smoothProductGraphH0Linear : FreeGraphDomain →ₗ[ℂ] Physical where
  toFun u := freeHamiltonian (freeGraphH0Input u)
  map_add' u v := by
    have he : freeGraphH0Input (u+v) = freeGraphH0Input u+freeGraphH0Input v := Subtype.ext rfl
    exact (congrArg freeHamiltonian.toFun he).trans (freeHamiltonian.toFun.map_add _ _)
  map_smul' c u := by
    have he : freeGraphH0Input (c • u) = c • freeGraphH0Input u := Subtype.ext rfl
    exact (congrArg freeHamiltonian.toFun he).trans (freeHamiltonian.toFun.map_smul _ _)

def smoothProductGraphH0Map : FreeGraphDomain →L[ℂ] Physical :=
  smoothProductGraphH0Linear.mkContinuous 1 (fun u => by
    change ‖freeHamiltonian (freeGraphH0Input u)‖ ≤ 1*‖u‖
    simpa only [one_mul] using (freeGraph_norm_lower u).2)

lemma smoothFiniteGraphCore_graph_sequence (u : freeHamiltonian.domain) :
    ∃ v : ℕ → FreeGraphDomain, (∀ m, v m ∈ smoothFiniteGraphCore) ∧
      Tendsto (fun m => (freeGraphDomainInclusion (v m),freeHamiltonian (freeGraphH0Input (v m))))
        atTop (𝓝 (u.val,freeHamiltonian u)) := by
  let U : FreeGraphDomain := show freeGraphOperator.domain from
    ⟨u.val,(congrArg (fun V : Submodule ℂ Physical => u.val ∈ V) freeGraphOperator_domain).mpr u.property⟩
  obtain ⟨v,hv,ht⟩ := smoothFiniteGraphCore_sequence U
  refine ⟨v,hv,?_⟩
  have h₁ := (freeGraphDomainInclusion.continuous.tendsto U).comp ht
  have h₂ := (smoothProductGraphH0Map.continuous.tendsto U).comp ht
  have hi : freeGraphDomainInclusion U = u.val := by
    rw [freeGraphDomainInclusion_apply]
  have ha (z : FreeGraphDomain) : smoothProductGraphH0Map z = freeHamiltonian (freeGraphH0Input z) := rfl
  have hu : smoothProductGraphH0Map U = freeHamiltonian u := by
    rw [ha]
    apply congrArg freeHamiltonian.toFun
    apply Subtype.ext
    rfl
  simpa only [Function.comp_def,hi,hu,ha] using h₁.prodMk_nhds h₂

lemma smoothFiniteProductCore_operator_core : freeHamiltonian.HasCore smoothFiniteProductCore := by
  have hclosed := GW.Operators.selfadjoint_closed freeHamiltonian freeHamiltonian_selfadjoint
  have hle : freeHamiltonian.domRestrict smoothFiniteProductCore ≤ freeHamiltonian := LinearPMap.domRestrict_le
  have hc := hclosed.isClosable.leIsClosable hle
  refine ⟨smoothFiniteProductCore_le_H0,LinearPMap.eq_of_eq_graph ?_⟩
  rw [← hc.graph_closure_eq_closure_graph]
  apply SetLike.coe_injective
  change closure ((freeHamiltonian.domRestrict smoothFiniteProductCore).graph : Set (Physical × Physical)) =
    (freeHamiltonian.graph : Set (Physical × Physical))
  apply le_antisymm
  · exact closure_minimal (LinearPMap.le_graph_of_le hle) hclosed
  · intro p hp
    obtain ⟨u,hu⟩ := freeHamiltonian.mem_graph_iff'.mp hp
    rw [← hu]
    obtain ⟨v,hv,ht⟩ := smoothFiniteGraphCore_graph_sequence u
    apply mem_closure_of_tendsto ht
    apply Eventually.of_forall
    intro m
    let x := freeGraphH0Input (v m)
    have hx : x.val = freeGraphDomainInclusion (v m) := (freeGraphDomainInclusion_apply (v m)).symm
    have hcore : x.val ∈ smoothFiniteProductCore := hx.symm ▸ (show freeGraphDomainInclusion (v m) ∈ smoothFiniteProductCore from hv m)
    exact (freeHamiltonian.domRestrict smoothFiniteProductCore).mem_graph_iff.mpr
      ⟨⟨x.val,⟨hcore,x.property⟩⟩,hx,LinearPMap.domRestrict_apply rfl⟩

end GW.Fock
