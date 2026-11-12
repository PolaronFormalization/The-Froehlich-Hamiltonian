module
public import GW.Operators.BasicWeakDerivative
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff InnerProductSpace ENNReal BigOperators
namespace GW.Analysis

def smoothCoreTestProduct (χ : GW.Space → ℝ) (hχ : ContDiff ℝ ∞ χ) (φ : SmoothScalarTest) : SmoothScalarTest where
  value x := (χ x : ℂ)*φ.value x
  smooth := (Complex.ofRealCLM.contDiff.comp hχ).mul φ.smooth
  compact := φ.compact.mul_left

lemma smoothCoreTestProduct_derivative (χ : GW.Space → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (φ : SmoothScalarTest) (j : Fin 3) (x : GW.Space) :
    fderiv ℝ (smoothCoreTestProduct χ hχ φ).value x (momentumAxis j) =
      (fderiv ℝ χ x (momentumAxis j) : ℂ)*φ.value x+
        (χ x : ℂ)*fderiv ℝ φ.value x (momentumAxis j) := by
  have h := (Complex.ofRealCLM.hasFDerivAt.comp x ((hχ.differentiable (by simp) x).hasFDerivAt)).mul
    ((φ.smooth.differentiable (by simp) x).hasFDerivAt)
  have he := congrArg (fun L : GW.Space →L[ℝ] ℂ => L (momentumAxis j)) h.fderiv
  have heq : (⇑Complex.ofRealCLM ∘ χ * φ.value : GW.Space → ℂ) = (smoothCoreTestProduct χ hχ φ).value := rfl
  rw [heq] at he
  simpa only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,Function.comp_apply,Complex.ofRealCLM_apply,smul_eq_mul,mul_comm,add_comm] using he

lemma smoothCoreTest_momentum_ae {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (φ : SmoothScalarTest) (j : Fin 3) (e : E) :
    (schwartzMomentumDerivative j (scalarSchwartzVector φ.toSchwartzMap e)).toLp 2 (volume : Measure GW.Space) =ᵐ[volume]
      fun x => ((-Complex.I)*fderiv ℝ φ.value x (momentumAxis j)) • e := by
  filter_upwards [(schwartzMomentumDerivative j (scalarSchwartzVector φ.toSchwartzMap e)).coeFn_toLp 2 (volume : Measure GW.Space)] with x hx
  exact hx.trans (scalarSchwartzVector_momentum_apply j φ.toSchwartzMap e x)

lemma smoothCoreTest_value_ae {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (φ : SmoothScalarTest) (e : E) :
    (scalarSchwartzVector φ.toSchwartzMap e).toLp 2 (volume : Measure GW.Space) =ᵐ[volume]
      fun x => φ.value x • e := by
  filter_upwards [(scalarSchwartzVector φ.toSchwartzMap e).coeFn_toLp 2 (volume : Measure GW.Space)] with x hx
  exact hx

lemma weakMomentumIdentity_integral {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (j : Fin 3) (u v : ElectronHilbertL2 (E := E)) :
    WeakMomentumIdentity j u v ↔ ∀ (φ : SmoothScalarTest) (e : E),
      (∫ x, ⟪((-Complex.I)*fderiv ℝ φ.value x (momentumAxis j)) • e,u x⟫_ℂ ∂(volume : Measure GW.Space)) =
        ∫ x, ⟪φ.value x • e,v x⟫_ℂ ∂(volume : Measure GW.Space) := by
  have hp (φ : SmoothScalarTest) (e : E) :
      ⟪(schwartzMomentumDerivative j (scalarSchwartzVector φ.toSchwartzMap e)).toLp 2,u⟫_ℂ =
        ∫ x, ⟪((-Complex.I)*fderiv ℝ φ.value x (momentumAxis j)) • e,u x⟫_ℂ ∂(volume : Measure GW.Space) := by
    rw [L2.inner_def]
    exact integral_congr_ae ((smoothCoreTest_momentum_ae φ j e).mono (fun x hx => congrArg (fun z : E => ⟪z,u x⟫_ℂ) hx))
  have hq (φ : SmoothScalarTest) (e : E) :
      ⟪(scalarSchwartzVector φ.toSchwartzMap e).toLp 2,v⟫_ℂ =
        ∫ x, ⟪φ.value x • e,v x⟫_ℂ ∂(volume : Measure GW.Space) := by
    rw [L2.inner_def]
    exact integral_congr_ae ((smoothCoreTest_value_ae φ e).mono (fun x hx => congrArg (fun z : E => ⟪z,v x⟫_ℂ) hx))
  simp only [WeakMomentumIdentity,hp,hq]

def smoothCoreBoundedReal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (a : GW.Space → ℝ) (ha : Measurable a) {C : ℝ} (hC : ∀ x, ‖a x‖ ≤ C) :
    ElectronHilbertL2 (E := E) →L[ℂ] ElectronHilbertL2 (E := E) :=
  boundedMultiplier (C := C) (fun x => (a x : ℂ)) (Complex.continuous_ofReal.measurable.comp ha)
    (Eventually.of_forall (fun x => by simpa only [Complex.norm_real] using hC x))

lemma smoothCoreBoundedReal_ae {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (a : GW.Space → ℝ) (ha : Measurable a) {C : ℝ} (hC : ∀ x, ‖a x‖ ≤ C)
    (u : ElectronHilbertL2 (E := E)) :
    smoothCoreBoundedReal a ha hC u =ᵐ[volume] fun x => (a x : ℂ) • u x :=
  (boundedMultiplier_ae (C := C) _ _ _ u).symm

lemma smoothCoreBoundedReal_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (a : GW.Space → ℝ) (ha : Measurable a) {C : ℝ} (hC : ∀ x, ‖a x‖ ≤ C)
    (u v : ElectronHilbertL2 (E := E)) :
    ⟪smoothCoreBoundedReal a ha hC u,v⟫_ℂ = ⟪u,smoothCoreBoundedReal a ha hC v⟫_ℂ := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [smoothCoreBoundedReal_ae a ha hC u,smoothCoreBoundedReal_ae a ha hC v] with x hx hy
  rw [hx,hy,inner_smul_left,inner_smul_right,Complex.conj_ofReal]

lemma smoothCoreTestProduct_toLp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (χ : GW.Space → ℝ) (hχ : ContDiff ℝ ∞ χ) {C : ℝ} (hC : ∀ x, ‖χ x‖ ≤ C)
    (φ : SmoothScalarTest) (e : E) :
    (scalarSchwartzVector (smoothCoreTestProduct χ hχ φ).toSchwartzMap e).toLp 2 volume =
      smoothCoreBoundedReal χ hχ.continuous.measurable hC
        ((scalarSchwartzVector φ.toSchwartzMap e).toLp 2 volume) := by
  apply Lp.ext
  filter_upwards [smoothCoreTest_value_ae (smoothCoreTestProduct χ hχ φ) e,
    smoothCoreBoundedReal_ae χ hχ.continuous.measurable hC ((scalarSchwartzVector φ.toSchwartzMap e).toLp 2 volume),
    smoothCoreTest_value_ae φ e] with x hx hy hz
  rw [hx,hy,hz]
  exact mul_smul _ _ _

def smoothCoreAxisDerivative (χ : GW.Space → ℝ) (j : Fin 3) : GW.Space → ℝ :=
  fun x => fderiv ℝ χ x (momentumAxis j)

lemma smoothCoreAxisDerivative_continuous (χ : GW.Space → ℝ) (hχ : ContDiff ℝ ∞ χ) (j : Fin 3) :
    Continuous (smoothCoreAxisDerivative χ j) :=
  (hχ.continuous_fderiv (by simp : (∞ : ℕ∞ω) ≠ 0)).clm_apply continuous_const

lemma smoothCoreTestProduct_momentum_toLp
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (χ : GW.Space → ℝ) (hχ : ContDiff ℝ ∞ χ) (j : Fin 3)
    {C D : ℝ} (hC : ∀ x, ‖χ x‖ ≤ C) (hD : ∀ x, ‖smoothCoreAxisDerivative χ j x‖ ≤ D)
    (φ : SmoothScalarTest) (e : E) :
    (schwartzMomentumDerivative j (scalarSchwartzVector (smoothCoreTestProduct χ hχ φ).toSchwartzMap e)).toLp 2 volume =
      smoothCoreBoundedReal χ hχ.continuous.measurable hC
        ((schwartzMomentumDerivative j (scalarSchwartzVector φ.toSchwartzMap e)).toLp 2 volume) +
      (-Complex.I) • smoothCoreBoundedReal (smoothCoreAxisDerivative χ j)
        (smoothCoreAxisDerivative_continuous χ hχ j).measurable hD ((scalarSchwartzVector φ.toSchwartzMap e).toLp 2 volume) := by
  let P := (schwartzMomentumDerivative j (scalarSchwartzVector φ.toSchwartzMap e)).toLp 2 volume
  let Q := (scalarSchwartzVector φ.toSchwartzMap e).toLp 2 volume
  let A := smoothCoreBoundedReal χ hχ.continuous.measurable hC P
  let B := smoothCoreBoundedReal (smoothCoreAxisDerivative χ j)
    (smoothCoreAxisDerivative_continuous χ hχ j).measurable hD Q
  apply Lp.ext
  filter_upwards [smoothCoreTest_momentum_ae (smoothCoreTestProduct χ hχ φ) j e,
    Lp.coeFn_add A ((-Complex.I) • B),smoothCoreBoundedReal_ae χ hχ.continuous.measurable hC P,
    smoothCoreTest_momentum_ae φ j e,Lp.coeFn_smul (-Complex.I) B,
    smoothCoreBoundedReal_ae (smoothCoreAxisDerivative χ j) (smoothCoreAxisDerivative_continuous χ hχ j).measurable hD Q,
    smoothCoreTest_value_ae φ e] with x h₁ h₂ h₃ h₄ h₅ h₆ h₇
  simp only [Pi.add_apply,Pi.smul_apply] at h₂ h₅
  change _ = (A+(-Complex.I) • B) x
  rw [h₁,h₂,h₃,h₄,h₅,h₆,h₇,smoothCoreTestProduct_derivative]
  change ((-Complex.I)*((smoothCoreAxisDerivative χ j x : ℂ)*φ.value x+
    (χ x : ℂ)*fderiv ℝ φ.value x (momentumAxis j))) • e = _
  simp only [smul_smul,← add_smul]
  congr 1
  ring

lemma smoothCoreMomentum_product_rule
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (χ : GW.Space → ℝ) (hχ : ContDiff ℝ ∞ χ) (j : Fin 3)
    {C D : ℝ} (hC : ∀ x, ‖χ x‖ ≤ C) (hD : ∀ x, ‖smoothCoreAxisDerivative χ j x‖ ≤ D)
    (u v : ElectronHilbertL2 (E := E)) (hu : (u,v) ∈ (momentumOperator j).graph) :
    (smoothCoreBoundedReal χ hχ.continuous.measurable hC u,
      smoothCoreBoundedReal χ hχ.continuous.measurable hC v+
        (-Complex.I) • smoothCoreBoundedReal (smoothCoreAxisDerivative χ j)
          (smoothCoreAxisDerivative_continuous χ hχ j).measurable hD u) ∈ (momentumOperator j).graph := by
  apply (momentum_graph_iff_weak j _ _).mpr
  intro φ e
  let P := (schwartzMomentumDerivative j (scalarSchwartzVector φ.toSchwartzMap e)).toLp 2 volume
  let Q := (scalarSchwartzVector φ.toSchwartzMap e).toLp 2 volume
  let A := smoothCoreBoundedReal (E := E) χ hχ.continuous.measurable hC
  let B := smoothCoreBoundedReal (E := E) (smoothCoreAxisDerivative χ j)
    (smoothCoreAxisDerivative_continuous χ hχ j).measurable hD
  have hw := momentum_graph_implies_weak j u v hu (smoothCoreTestProduct χ hχ φ) e
  rw [smoothCoreTestProduct_momentum_toLp χ hχ j hC hD φ e,
    smoothCoreTestProduct_toLp χ hχ hC φ e,inner_add_left,inner_smul_left,
    smoothCoreBoundedReal_pair χ hχ.continuous.measurable hC P u,
    smoothCoreBoundedReal_pair (smoothCoreAxisDerivative χ j)
      (smoothCoreAxisDerivative_continuous χ hχ j).measurable hD Q u,
    smoothCoreBoundedReal_pair χ hχ.continuous.measurable hC Q v] at hw
  have hi : starRingEnd ℂ (-Complex.I) = Complex.I := by simp
  rw [hi] at hw
  change ⟪P,A u⟫_ℂ = ⟪Q,A v+(-Complex.I) • B u⟫_ℂ
  rw [inner_add_right,inner_smul_right]
  calc
    _ = ⟪Q,A v⟫_ℂ-Complex.I*⟪Q,B u⟫_ℂ := eq_sub_iff_add_eq.mpr hw
    _ = _ := by ring

lemma smoothCoreAxisDerivative_contDiff (χ : GW.Space → ℝ) (hχ : ContDiff ℝ ∞ χ) (j : Fin 3) :
    ContDiff ℝ ∞ (smoothCoreAxisDerivative χ j) :=
  (hχ.contDiff_fderiv_apply (m := ∞) (by simp)).comp (contDiff_id.prodMk contDiff_const)

lemma smoothCoreMomentum_second_product_rule
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (χ : GW.Space → ℝ) (hχ : ContDiff ℝ ∞ χ) (i j : Fin 3)
    {C Dᵢ Dⱼ Dᵢⱼ : ℝ} (hC : ∀ x, ‖χ x‖ ≤ C)
    (hDᵢ : ∀ x, ‖smoothCoreAxisDerivative χ i x‖ ≤ Dᵢ)
    (hDⱼ : ∀ x, ‖smoothCoreAxisDerivative χ j x‖ ≤ Dⱼ)
    (hDᵢⱼ : ∀ x, ‖smoothCoreAxisDerivative (smoothCoreAxisDerivative χ i) j x‖ ≤ Dᵢⱼ)
    (u vᵢ vⱼ w : ElectronHilbertL2 (E := E))
    (hvi : (vᵢ,w) ∈ (momentumOperator j).graph) (hvj : (u,vⱼ) ∈ (momentumOperator j).graph) :
    let A := smoothCoreBoundedReal (E := E) χ hχ.continuous.measurable hC
    let Aᵢ := smoothCoreBoundedReal (E := E) (smoothCoreAxisDerivative χ i)
      (smoothCoreAxisDerivative_continuous χ hχ i).measurable hDᵢ
    let Aⱼ := smoothCoreBoundedReal (E := E) (smoothCoreAxisDerivative χ j)
      (smoothCoreAxisDerivative_continuous χ hχ j).measurable hDⱼ
    let Aᵢⱼ := smoothCoreBoundedReal (E := E) (smoothCoreAxisDerivative (smoothCoreAxisDerivative χ i) j)
      (smoothCoreAxisDerivative_continuous (smoothCoreAxisDerivative χ i) (smoothCoreAxisDerivative_contDiff χ hχ i) j).measurable hDᵢⱼ
    (A vᵢ+(-Complex.I) • Aᵢ u,
      A w+(-Complex.I) • Aⱼ vᵢ+(-Complex.I) • (Aᵢ vⱼ+(-Complex.I) • Aᵢⱼ u)) ∈ (momentumOperator j).graph := by
  have h₁ := smoothCoreMomentum_product_rule χ hχ j hC hDⱼ vᵢ w hvi
  have h₂ := smoothCoreMomentum_product_rule (smoothCoreAxisDerivative χ i) (smoothCoreAxisDerivative_contDiff χ hχ i) j
    hDᵢ hDᵢⱼ u vⱼ hvj
  exact (momentumOperator j).graph.add_mem h₁ ((momentumOperator j).graph.smul_mem (-Complex.I) h₂)

lemma smoothCoreTranslation_neg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (a : GW.Space) (u : ElectronHilbertL2 (E := E)) : translation a (translation (-a) u) = u := by
  apply Lp.ext
  filter_upwards [translation_ae a (translation (-a) u),
    (measurePreserving_sub_right (volume : Measure GW.Space) a).quasiMeasurePreserving.ae (translation_ae (-a) u)] with x hx hy
  rw [hx,hy]
  simp only [sub_neg_eq_add,sub_add_cancel]

lemma smoothCoreTranslation_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (a : GW.Space) (u v : ElectronHilbertL2 (E := E)) :
    ⟪u,translation a v⟫_ℂ = ⟪translation (-a) u,v⟫_ℂ := by
  have h := (translation (H := E) a).inner_map_map (translation (-a) u) v
  rw [smoothCoreTranslation_neg] at h
  exact h

def smoothCoreTestTranslation (a : GW.Space) (φ : SmoothScalarTest) : SmoothScalarTest where
  value x := φ.value (x+a)
  smooth := φ.smooth.comp (contDiff_id.add contDiff_const)
  compact := φ.compact.comp_homeomorph (Homeomorph.addRight a)

lemma smoothCoreTestTranslation_value_toLp
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (a : GW.Space) (φ : SmoothScalarTest) (e : E) :
    (scalarSchwartzVector (smoothCoreTestTranslation a φ).toSchwartzMap e).toLp 2 volume =
      translation (-a) ((scalarSchwartzVector φ.toSchwartzMap e).toLp 2 volume) := by
  apply Lp.ext
  filter_upwards [smoothCoreTest_value_ae (smoothCoreTestTranslation a φ) e,
    translation_ae (-a) ((scalarSchwartzVector φ.toSchwartzMap e).toLp 2 volume),
    (measurePreserving_sub_right (volume : Measure GW.Space) (-a)).quasiMeasurePreserving.ae (smoothCoreTest_value_ae φ e)] with x hx hy hz
  rw [hx,hy,hz]
  simp only [smoothCoreTestTranslation,sub_neg_eq_add]

lemma smoothCoreTestTranslation_momentum_toLp
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (a : GW.Space) (φ : SmoothScalarTest) (j : Fin 3) (e : E) :
    (schwartzMomentumDerivative j (scalarSchwartzVector (smoothCoreTestTranslation a φ).toSchwartzMap e)).toLp 2 volume =
      translation (-a) ((schwartzMomentumDerivative j (scalarSchwartzVector φ.toSchwartzMap e)).toLp 2 volume) := by
  apply Lp.ext
  filter_upwards [smoothCoreTest_momentum_ae (smoothCoreTestTranslation a φ) j e,
    translation_ae (-a) ((schwartzMomentumDerivative j (scalarSchwartzVector φ.toSchwartzMap e)).toLp 2 volume),
    (measurePreserving_sub_right (volume : Measure GW.Space) (-a)).quasiMeasurePreserving.ae (smoothCoreTest_momentum_ae φ j e)] with x hx hy hz
  rw [hx,hy,hz]
  have hd : fderiv ℝ (smoothCoreTestTranslation a φ).value x = fderiv ℝ φ.value (x+a) := fderiv_comp_add_right a
  rw [hd,sub_neg_eq_add]

lemma smoothCoreWeakMomentum_translation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (a : GW.Space) (j : Fin 3) (u v : ElectronHilbertL2 (E := E)) (hu : WeakMomentumIdentity j u v) :
    WeakMomentumIdentity j (translation a u) (translation a v) := by
  intro φ e
  rw [smoothCoreTranslation_inner,smoothCoreTranslation_inner]
  have h := hu (smoothCoreTestTranslation a φ) e
  rw [smoothCoreTestTranslation_momentum_toLp,smoothCoreTestTranslation_value_toLp] at h
  exact h

lemma smoothCoreWeakMomentum_mollification (ε : ℝ) (j : Fin 3) (u v : GW.OnePhonon)
    (hu : WeakMomentumIdentity j u v) :
    WeakMomentumIdentity j (mollifiedTranslation u ε) (mollifiedTranslation v ε) := by
  intro φ e
  let P := (schwartzMomentumDerivative j (scalarSchwartzVector φ.toSchwartzMap e)).toLp 2 volume
  let Q := (scalarSchwartzVector φ.toSchwartzMap e).toLp 2 volume
  have hp := (innerSL ℂ P).integral_comp_comm (mollifiedTranslationIntegrand_integrable u ε)
  have hq := (innerSL ℂ Q).integral_comp_comm (mollifiedTranslationIntegrand_integrable v ε)
  change ⟪P,∫ y, mollifiedTranslationIntegrand u ε y ∂(volume : Measure GW.Space)⟫_ℂ =
    ⟪Q,∫ y, mollifiedTranslationIntegrand v ε y ∂(volume : Measure GW.Space)⟫_ℂ
  change (innerSL ℂ P) (∫ y, mollifiedTranslationIntegrand u ε y ∂(volume : Measure GW.Space)) =
    (innerSL ℂ Q) (∫ y, mollifiedTranslationIntegrand v ε y ∂(volume : Measure GW.Space))
  rw [← hp,← hq]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  change ⟪P,testMollifier y • translation (ε • y) u⟫_ℂ = ⟪Q,testMollifier y • translation (ε • y) v⟫_ℂ
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) (testMollifier y) (translation (ε • y) u),
    RCLike.real_smul_eq_coe_smul (K := ℂ) (testMollifier y) (translation (ε • y) v),inner_smul_right,inner_smul_right]
  exact congrArg (fun z : ℂ => (testMollifier y : ℂ)*z) (smoothCoreWeakMomentum_translation (ε • y) j u v hu φ e)

lemma smoothCoreBoundedReal_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (a : GW.Space → ℝ) (ha : Measurable a) {C : ℝ} (hC : ∀ x, ‖a x‖ ≤ C)
    (u : ElectronHilbertL2 (E := E)) : ‖smoothCoreBoundedReal a ha hC u‖ ≤ C*‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [smoothCoreBoundedReal_ae a ha hC u] with x hx
  rw [hx,norm_smul,Complex.norm_real]
  exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

lemma smoothCoreMomentumSquare_product_rule
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (χ : GW.Space → ℝ) (hχ : ContDiff ℝ ∞ χ)
    {C : ℝ} {D B : Fin 3 → ℝ} (hC : ∀ x, ‖χ x‖ ≤ C)
    (hD : ∀ i x, ‖smoothCoreAxisDerivative χ i x‖ ≤ D i)
    (hB : ∀ i x, ‖smoothCoreAxisDerivative (smoothCoreAxisDerivative χ i) i x‖ ≤ B i)
    (u : ElectronHilbertL2 (E := E)) (v w : Fin 3 → ElectronHilbertL2 (E := E))
    (hv : ∀ i, (u,v i) ∈ (momentumOperator i).graph)
    (hw : ∀ i, (v i,w i) ∈ (momentumOperator i).graph) :
    let A := smoothCoreBoundedReal (E := E) χ hχ.continuous.measurable hC
    let Aᵢ (i : Fin 3) := smoothCoreBoundedReal (E := E) (smoothCoreAxisDerivative χ i)
      (smoothCoreAxisDerivative_continuous χ hχ i).measurable (hD i)
    let Aᵢᵢ (i : Fin 3) := smoothCoreBoundedReal (E := E) (smoothCoreAxisDerivative (smoothCoreAxisDerivative χ i) i)
      (smoothCoreAxisDerivative_continuous (smoothCoreAxisDerivative χ i) (smoothCoreAxisDerivative_contDiff χ hχ i) i).measurable (hB i)
    (A u,∑ i : Fin 3, (A (w i)+(-Complex.I) • Aᵢ i (v i)+
      (-Complex.I) • (Aᵢ i (v i)+(-Complex.I) • Aᵢᵢ i u))) ∈ (absoluteMomentumPower 2).graph := by
  let A := smoothCoreBoundedReal (E := E) χ hχ.continuous.measurable hC
  let Aᵢ (i : Fin 3) := smoothCoreBoundedReal (E := E) (smoothCoreAxisDerivative χ i)
    (smoothCoreAxisDerivative_continuous χ hχ i).measurable (hD i)
  let Aᵢᵢ (i : Fin 3) := smoothCoreBoundedReal (E := E) (smoothCoreAxisDerivative (smoothCoreAxisDerivative χ i) i)
    (smoothCoreAxisDerivative_continuous (smoothCoreAxisDerivative χ i) (smoothCoreAxisDerivative_contDiff χ hχ i) i).measurable (hB i)
  let v' (i : Fin 3) := A (v i)+(-Complex.I) • Aᵢ i u
  let w' (i : Fin 3) := A (w i)+(-Complex.I) • Aᵢ i (v i)+(-Complex.I) • (Aᵢ i (v i)+(-Complex.I) • Aᵢᵢ i u)
  have hv' (i : Fin 3) : (A u,v' i) ∈ (momentumOperator i).graph :=
    smoothCoreMomentum_product_rule χ hχ i hC (hD i) u (v i) (hv i)
  have hw' (i : Fin 3) : (v' i,w' i) ∈ (momentumOperator i).graph :=
    smoothCoreMomentum_second_product_rule χ hχ i i hC (hD i) (hD i) (hB i) u (v i) (v i) (w i) (hw i) (hv i)
  exact momentum_second_sum_graph (A u) v' w' hv' hw'

lemma smoothCoreAxisDerivative_scale (χ : GW.Space → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (t : ℝ) (i : Fin 3) (x : GW.Space) :
    smoothCoreAxisDerivative (fun x => χ (t • x)) i x = t*smoothCoreAxisDerivative χ i (t • x) := by
  let L : GW.Space →L[ℝ] GW.Space := t • ContinuousLinearMap.id ℝ GW.Space
  have he := ((hχ.differentiable (by simp) (t • x)).hasFDerivAt.comp x L.hasFDerivAt).fderiv
  change fderiv ℝ (fun x => χ (t • x)) x = _ at he
  unfold smoothCoreAxisDerivative
  rw [he]
  change fderiv ℝ χ (t • x) (t • momentumAxis i) = _
  rw [map_smul]
  rfl

lemma smoothCoreAxisDerivative_const_mul (χ : GW.Space → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (t : ℝ) (i : Fin 3) (x : GW.Space) :
    smoothCoreAxisDerivative (fun x => t*χ x) i x = t*smoothCoreAxisDerivative χ i x := by
  have he := ((hχ.differentiable (by simp) x).hasFDerivAt.const_mul t).fderiv
  unfold smoothCoreAxisDerivative
  rw [he]
  rfl

lemma smoothCoreSecondAxisDerivative_scale (χ : GW.Space → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (t : ℝ) (i j : Fin 3) (x : GW.Space) :
    smoothCoreAxisDerivative (smoothCoreAxisDerivative (fun x => χ (t • x)) i) j x =
      t^2*smoothCoreAxisDerivative (smoothCoreAxisDerivative χ i) j (t • x) := by
  have hi : smoothCoreAxisDerivative (fun x => χ (t • x)) i =
      (fun x => t*smoothCoreAxisDerivative χ i (t • x)) := funext (smoothCoreAxisDerivative_scale χ hχ t i)
  rw [hi]
  have hs : ContDiff ℝ ∞ (fun x => smoothCoreAxisDerivative χ i (t • x)) :=
    (smoothCoreAxisDerivative_contDiff χ hχ i).comp ((t • ContinuousLinearMap.id ℝ GW.Space).contDiff)
  rw [smoothCoreAxisDerivative_const_mul _ hs t j x,
    smoothCoreAxisDerivative_scale _ (smoothCoreAxisDerivative_contDiff χ hχ i) t j x]
  ring

lemma smoothCoreAxisDerivative_compact (χ : GW.Space → ℝ) (hχ : HasCompactSupport χ) (i : Fin 3) :
    HasCompactSupport (smoothCoreAxisDerivative χ i) := by
  change HasCompactSupport ((fun L : GW.Space →L[ℝ] ℝ => L (momentumAxis i)) ∘ fderiv ℝ χ)
  exact (hχ.fderiv (𝕜 := ℝ)).comp_left rfl

lemma smoothCorePlateau_second_bound (i j : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ) (hR : 0 < R) (x : GW.Space),
      ‖smoothCoreAxisDerivative (smoothCoreAxisDerivative (weakPlateauScaled R) i) j x‖ ≤ C/R^2 := by
  have hg := smoothCoreAxisDerivative_contDiff weakPlateau weakPlateau_contDiff i
  have hc := (smoothCoreAxisDerivative_compact weakPlateau weakPlateau_hasCompactSupport i).fderiv (𝕜 := ℝ)
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuous (hg.continuous_fderiv (by simp : (∞ : ℕ∞ω) ≠ 0))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨C,hC0,?_⟩
  intro R hR x
  have he := smoothCoreSecondAxisDerivative_scale weakPlateau weakPlateau_contDiff R⁻¹ i j x
  change ‖smoothCoreAxisDerivative (smoothCoreAxisDerivative (fun x => weakPlateau (R⁻¹ • x)) i) j x‖ ≤ _
  rw [he,norm_mul,Real.norm_of_nonneg (sq_nonneg _)]
  have hb : ‖smoothCoreAxisDerivative (smoothCoreAxisDerivative weakPlateau i) j (R⁻¹ • x)‖ ≤ C := by
    exact ((fderiv ℝ (smoothCoreAxisDerivative weakPlateau i) (R⁻¹ • x)).le_opNorm (momentumAxis j)).trans
      (by simpa only [momentumAxis_norm,mul_one] using hC (R⁻¹ • x))
  calc
    _ ≤ R⁻¹^2*C := mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = C/R^2 := by rw [inv_pow,div_eq_mul_inv,mul_comm]

lemma smoothCoreL2_integrable_of_compact_support (u : GW.OnePhonon) (L : Set GW.Space) (hL : IsCompact L)
    (hzero : ∀ᵐ x ∂(volume : Measure GW.Space), x ∉ L → u x = 0) :
    Integrable (u : GW.Space → ℂ) volume := by
  have hf : MemLp (L.indicator (u : GW.Space → ℂ)) 2 (volume : Measure GW.Space) :=
    (Lp.memLp u).indicator hL.measurableSet.nullMeasurableSet
  have hi := hf.mono_exponent_of_measure_support_ne_top (s := L)
    (fun x hx => indicator_of_notMem hx _) hL.measure_lt_top.ne (by norm_num : (1:ℝ≥0∞) ≤ 2)
  apply (memLp_one_iff_integrable.mp hi).congr
  filter_upwards [hzero] with x hx
  by_cases h : x ∈ L
  · simp only [indicator_of_mem h]
  · rw [indicator_of_notMem h,hx h]

def smoothCoreMollifiedTest (u : GW.OnePhonon) (L : Set GW.Space) (hL : IsCompact L)
    (hzero : ∀ᵐ x ∂(volume : Measure GW.Space), x ∉ L → u x = 0)
    (ε : ℝ) (hε : 0 < ε) : SmoothScalarTest where
  value := smoothMollifiedRep u ε
  smooth := smoothMollifiedRep_contDiff u (smoothCoreL2_integrable_of_compact_support u L hL hzero) ε hε
  compact := smoothMollifiedRep_hasCompactSupport u ε hε L hL hzero

lemma smoothCoreMollifiedTest_toL2 (u : GW.OnePhonon) (L : Set GW.Space) (hL : IsCompact L)
    (hzero : ∀ᵐ x ∂(volume : Measure GW.Space), x ∉ L → u x = 0)
    (ε : ℝ) (hε : 0 < ε) :
    (smoothCoreMollifiedTest u L hL hzero ε hε).toL2 = mollifiedTranslation u ε :=
  (smoothMollifiedClass_eq u (smoothCoreL2_integrable_of_compact_support u L hL hzero) ε hε L hL hzero).symm

lemma smoothCoreMollification_momentum_graph (ε : ℝ) (j : Fin 3) (u v : GW.OnePhonon)
    (hu : (u,v) ∈ (momentumOperator j).graph) :
    (mollifiedTranslation u ε,mollifiedTranslation v ε) ∈ (momentumOperator j).graph :=
  (momentum_graph_iff_weak j _ _).mpr
    (smoothCoreWeakMomentum_mollification ε j u v ((momentum_graph_iff_weak j u v).mp hu))

lemma smoothCoreMollification_square_graph (ε : ℝ) (u : GW.OnePhonon) (v w : Fin 3 → GW.OnePhonon)
    (hv : ∀ i, (u,v i) ∈ (momentumOperator i).graph)
    (hw : ∀ i, (v i,w i) ∈ (momentumOperator i).graph) :
    (mollifiedTranslation u ε,∑ i : Fin 3, mollifiedTranslation (w i) ε) ∈ (absoluteMomentumPower 2).graph :=
  momentum_second_sum_graph (mollifiedTranslation u ε)
    (fun i => mollifiedTranslation (v i) ε) (fun i => mollifiedTranslation (w i) ε)
    (fun i => smoothCoreMollification_momentum_graph ε i u (v i) (hv i))
    (fun i => smoothCoreMollification_momentum_graph ε i (v i) (w i) (hw i))

lemma smoothCoreFirst_domain_forward
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (u : ElectronHilbertL2 (E := E)) (hu : u ∈ (absoluteMomentumPower 1).domain) :
    ∃ v : Fin 3 → ElectronHilbertL2 (E := E), ∀ j, (u,v j) ∈ (momentumOperator j).graph := by
  have hr := (absoluteMomentumPower_domain 1 u).mp hu
  simp only [Real.rpow_one] at hr
  have hi (j : Fin 3) : MemLp (fun p : GW.Space => (p j : ℂ) • physicalFourierUnitary u p) 2 volume := by
    apply hr.of_le (((Complex.continuous_ofReal.measurable.comp (electronMomentumCoord_measurable j)).aestronglyMeasurable).smul
      (Lp.aestronglyMeasurable (physicalFourierUnitary u)))
    apply Eventually.of_forall
    intro p
    change ‖(p j : ℂ) • physicalFourierUnitary u p‖ ≤ ‖(‖p‖ : ℂ) • physicalFourierUnitary u p‖
    rw [norm_smul,norm_smul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,
      Real.norm_of_nonneg (norm_nonneg p)]
    exact mul_le_mul_of_nonneg_right (electronMomentumCoord_abs_le p j) (norm_nonneg _)
  exact ⟨fun j => (fourierMultiplier_graph_of_memLp (fun p => p j) u (hi j)).choose,
    fun j => (fourierMultiplier_graph_of_memLp (fun p => p j) u (hi j)).choose_spec⟩

lemma smoothCoreCoordinate_norm_ae
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (u : ElectronHilbertL2 (E := E)) (v : Fin 3 → ElectronHilbertL2 (E := E))
    (hv : ∀ j, (u,v j) ∈ (momentumOperator j).graph) :
    (fun p : GW.Space => ‖(‖p‖ : ℂ) • physicalFourierUnitary u p‖^2) =ᵐ[volume]
      (fun p => ∑ j : Fin 3, ‖physicalFourierUnitary (v j) p‖^2) := by
  have h (j : Fin 3) := (fourierMultiplier_graph_iff_ae (fun p => p j) u (v j)).mp (hv j)
  filter_upwards [ae_all_iff.mpr h] with p hp
  have hn (j : Fin 3) : ‖physicalFourierUnitary (v j) p‖^2 = (p j)^2*‖physicalFourierUnitary u p‖^2 := by
    rw [← hp j,norm_smul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rw [norm_smul,mul_pow,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg p)]
  simp_rw [hn]
  rw [← Finset.sum_mul,← EuclideanSpace.real_norm_sq_eq]

lemma smoothCoreFirst_domain_reverse
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (u : ElectronHilbertL2 (E := E)) (v : Fin 3 → ElectronHilbertL2 (E := E))
    (hv : ∀ j, (u,v j) ∈ (momentumOperator j).graph) :
    u ∈ (absoluteMomentumPower 1).domain := by
  have hm : AEStronglyMeasurable (fun p : GW.Space => (‖p‖ : ℂ) • physicalFourierUnitary u p) volume :=
    (Complex.continuous_ofReal.measurable.comp continuous_norm.measurable).aestronglyMeasurable.smul
      (Lp.aestronglyMeasurable (physicalFourierUnitary u))
  have hi : Integrable (fun p => ∑ j : Fin 3, ‖physicalFourierUnitary (v j) p‖^2) volume :=
    integrable_finsetSum Finset.univ (fun j _ => (Lp.memLp (physicalFourierUnitary (v j))).integrable_norm_pow (p := 2) (by norm_num))
  apply (absoluteMomentumPower_domain 1 u).mpr
  simp only [Real.rpow_one]
  exact (memLp_two_iff_integrable_sq_norm hm).mpr (hi.congr (smoothCoreCoordinate_norm_ae u v hv).symm)

lemma smoothCoreAbsoluteMomentum_norm_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (u a : ElectronHilbertL2 (E := E)) (v : Fin 3 → ElectronHilbertL2 (E := E))
    (ha : (u,a) ∈ (absoluteMomentumPower 1).graph)
    (hv : ∀ j, (u,v j) ∈ (momentumOperator j).graph) : ‖a‖^2 = ∑ j : Fin 3, ‖v j‖^2 := by
  have hrad := (fourierMultiplier_graph_iff_ae (fun p => ‖p‖^(1:ℝ)) u a).mp ha
  have hn (f : ElectronHilbertL2 (E := E)) :
      (∫ p, ‖physicalFourierUnitary f p‖^2 ∂(volume : Measure GW.Space)) = ‖f‖^2 := by
    rw [← l2_norm_sq (𝕜 := ℂ),LinearIsometryEquiv.norm_map]
  calc
    _ = ∫ p, ‖physicalFourierUnitary a p‖^2 ∂(volume : Measure GW.Space) := (hn a).symm
    _ = ∫ p, ∑ j : Fin 3, ‖physicalFourierUnitary (v j) p‖^2 ∂(volume : Measure GW.Space) := by
      apply integral_congr_ae
      filter_upwards [hrad,smoothCoreCoordinate_norm_ae u v hv] with p hp hq
      rw [Real.rpow_one] at hp
      exact (congrArg (fun z : E => ‖z‖^2) hp.symm).trans hq
    _ = ∑ j : Fin 3, ∫ p, ‖physicalFourierUnitary (v j) p‖^2 ∂(volume : Measure GW.Space) :=
      integral_finsetSum Finset.univ (fun j _ => (Lp.memLp (physicalFourierUnitary (v j))).integrable_norm_pow (p := 2) (by norm_num))
    _ = _ := Finset.sum_congr rfl (fun j _ => hn (v j))

def smoothCoreFirstConstant (i : Fin 3) : ℝ := (weakPlateau_axis_bound i).choose

def smoothCoreSecondConstant (i : Fin 3) : ℝ := (smoothCorePlateau_second_bound i i).choose

lemma smoothCorePlateauBound (R : ℝ) (x : GW.Space) : ‖weakPlateauScaled R x‖ ≤ 1 := by
  change ‖weakPlateau (R⁻¹ • x)‖ ≤ 1
  rw [Real.norm_of_nonneg (weakPlateau_range (R⁻¹ • x)).1]
  exact (weakPlateau_range _).2

lemma smoothCoreCutoff_real_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (R : ℝ) : smoothCoreBoundedReal (E := E) (weakPlateauScaled R)
      (weakPlateauScaled_contDiff R).continuous.measurable (smoothCorePlateauBound R) = weakCutoffL2 R := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [smoothCoreBoundedReal_ae (weakPlateauScaled R) (weakPlateauScaled_contDiff R).continuous.measurable
      (smoothCorePlateauBound R) u,weakCutoffL2_ae R u] with x hx hy
  exact hx.trans hy.symm

def smoothCoreCutoffFirst {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (R : ℝ) (hR : 0 < R) (i : Fin 3) : ElectronHilbertL2 (E := E) →L[ℂ] ElectronHilbertL2 (E := E) :=
  smoothCoreBoundedReal (smoothCoreAxisDerivative (weakPlateauScaled R) i)
    (smoothCoreAxisDerivative_continuous (weakPlateauScaled R) (weakPlateauScaled_contDiff R) i).measurable
    (fun x => (weakPlateau_axis_bound i).choose_spec.2 R hR x)

def smoothCoreCutoffSecond {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (R : ℝ) (hR : 0 < R) (i : Fin 3) : ElectronHilbertL2 (E := E) →L[ℂ] ElectronHilbertL2 (E := E) :=
  smoothCoreBoundedReal (smoothCoreAxisDerivative (smoothCoreAxisDerivative (weakPlateauScaled R) i) i)
    (smoothCoreAxisDerivative_continuous (smoothCoreAxisDerivative (weakPlateauScaled R) i)
      (smoothCoreAxisDerivative_contDiff (weakPlateauScaled R) (weakPlateauScaled_contDiff R) i) i).measurable
    (fun x => (smoothCorePlateau_second_bound i i).choose_spec.2 R hR x)

lemma smoothCoreCutoffFirst_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (R : ℝ) (hR : 0 < R) (i : Fin 3) (u : ElectronHilbertL2 (E := E)) :
    ‖smoothCoreCutoffFirst R hR i u‖ ≤ smoothCoreFirstConstant i/R*‖u‖ :=
  smoothCoreBoundedReal_bound _ _ _ u

lemma smoothCoreCutoffSecond_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (R : ℝ) (hR : 0 < R) (i : Fin 3) (u : ElectronHilbertL2 (E := E)) :
    ‖smoothCoreCutoffSecond R hR i u‖ ≤ smoothCoreSecondConstant i/R^2*‖u‖ :=
  smoothCoreBoundedReal_bound _ _ _ u

lemma smoothCoreCutoffFirst_tendsto {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (i : Fin 3) (u : ElectronHilbertL2 (E := E)) :
    Tendsto (fun n => smoothCoreCutoffFirst (weakCutoffStep n) (weakCutoffStep_pos n) i u) atTop (𝓝 0) := by
  have hi := tendsto_inv_atTop_zero.comp weakCutoffStep_tendsto
  have hb : Tendsto (fun n => smoothCoreFirstConstant i/weakCutoffStep n*‖u‖) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (hi.const_mul (smoothCoreFirstConstant i)).mul_const ‖u‖
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_zero] using squeeze_zero (fun _ => norm_nonneg _)
    (fun n => smoothCoreCutoffFirst_bound (weakCutoffStep n) (weakCutoffStep_pos n) i u) hb

lemma smoothCoreCutoffSecond_tendsto {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (i : Fin 3) (u : ElectronHilbertL2 (E := E)) :
    Tendsto (fun n => smoothCoreCutoffSecond (weakCutoffStep n) (weakCutoffStep_pos n) i u) atTop (𝓝 0) := by
  have hi := tendsto_inv_atTop_zero.comp weakCutoffStep_tendsto
  have hb : Tendsto (fun n => smoothCoreSecondConstant i/(weakCutoffStep n)^2*‖u‖) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv,inv_pow] using ((hi.pow 2).const_mul (smoothCoreSecondConstant i)).mul_const ‖u‖
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_zero] using squeeze_zero (fun _ => norm_nonneg _)
    (fun n => smoothCoreCutoffSecond_bound (weakCutoffStep n) (weakCutoffStep_pos n) i u) hb

def smoothCoreFirstOutput {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (R : ℝ) (hR : 0 < R) (i : Fin 3) (u v : ElectronHilbertL2 (E := E)) : ElectronHilbertL2 (E := E) :=
  weakCutoffL2 R v+(-Complex.I) • smoothCoreCutoffFirst R hR i u

def smoothCoreSquareOutput {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (R : ℝ) (hR : 0 < R) (u : ElectronHilbertL2 (E := E))
    (v w : Fin 3 → ElectronHilbertL2 (E := E)) : ElectronHilbertL2 (E := E) :=
  ∑ i : Fin 3, (weakCutoffL2 R (w i)+(-Complex.I) • smoothCoreCutoffFirst R hR i (v i)+
    (-Complex.I) • (smoothCoreCutoffFirst R hR i (v i)+(-Complex.I) • smoothCoreCutoffSecond R hR i u))

lemma smoothCoreCutoff_first_graph {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (R : ℝ) (hR : 0 < R) (i : Fin 3) (u v : ElectronHilbertL2 (E := E))
    (hu : (u,v) ∈ (momentumOperator i).graph) :
    (weakCutoffL2 R u,smoothCoreFirstOutput R hR i u v) ∈ (momentumOperator i).graph := by
  have h := smoothCoreMomentum_product_rule (weakPlateauScaled R) (weakPlateauScaled_contDiff R) i
    (smoothCorePlateauBound R) (fun x => (weakPlateau_axis_bound i).choose_spec.2 R hR x) u v hu
  rw [smoothCoreCutoff_real_eq] at h
  exact h

lemma smoothCoreCutoff_square_graph {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (R : ℝ) (hR : 0 < R) (u : ElectronHilbertL2 (E := E))
    (v w : Fin 3 → ElectronHilbertL2 (E := E))
    (hv : ∀ i, (u,v i) ∈ (momentumOperator i).graph)
    (hw : ∀ i, (v i,w i) ∈ (momentumOperator i).graph) :
    (weakCutoffL2 R u,smoothCoreSquareOutput R hR u v w) ∈ (absoluteMomentumPower 2).graph := by
  have h := smoothCoreMomentumSquare_product_rule (weakPlateauScaled R) (weakPlateauScaled_contDiff R)
    (smoothCorePlateauBound R) (fun i x => (weakPlateau_axis_bound i).choose_spec.2 R hR x)
    (fun i x => (smoothCorePlateau_second_bound i i).choose_spec.2 R hR x) u v w hv hw
  dsimp only at h
  rw [smoothCoreCutoff_real_eq] at h
  exact h

lemma smoothCoreFirstOutput_tendsto {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (i : Fin 3) (u v : ElectronHilbertL2 (E := E)) :
    Tendsto (fun n => smoothCoreFirstOutput (weakCutoffStep n) (weakCutoffStep_pos n) i u v) atTop (𝓝 v) := by
  simpa only [smoothCoreFirstOutput,smul_zero,add_zero] using
    (weakCutoffL2_tendsto v).add ((smoothCoreCutoffFirst_tendsto i u).const_smul (-Complex.I))

lemma smoothCoreSquareOutput_tendsto {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (u : ElectronHilbertL2 (E := E)) (v w : Fin 3 → ElectronHilbertL2 (E := E)) :
    Tendsto (fun n => smoothCoreSquareOutput (weakCutoffStep n) (weakCutoffStep_pos n) u v w) atTop (𝓝 (∑ i, w i)) := by
  unfold smoothCoreSquareOutput
  apply tendsto_finsetSum Finset.univ
  intro i _
  simpa only [smul_zero,add_zero] using
    ((weakCutoffL2_tendsto (w i)).add ((smoothCoreCutoffFirst_tendsto i (v i)).const_smul (-Complex.I))).add
      (((smoothCoreCutoffFirst_tendsto i (v i)).add ((smoothCoreCutoffSecond_tendsto i u).const_smul (-Complex.I))).const_smul (-Complex.I))

lemma smoothCoreCutoff_support {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (R : ℝ) (u : ElectronHilbertL2 (E := E)) :
    ∀ᵐ x ∂(volume : Measure GW.Space), x ∉ tsupport (weakPlateauScaled R) → weakCutoffL2 R u x = 0 := by
  filter_upwards [weakCutoffL2_ae R u] with x hx ho
  have hz : weakPlateauScaled R x = 0 := by
    by_contra hn
    exact ho (subset_closure (show x ∈ Function.support (weakPlateauScaled R) from hn))
  rw [hx,hz,Complex.ofReal_zero,zero_smul]

lemma smoothCoreSquare_compact_graph_approximation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (u : (absoluteMomentumPower (H := E) 2).domain) :
    ∃ (f g : ℕ → ElectronHilbertL2 (E := E)) (L : ℕ → Set GW.Space),
      (∀ n, (f n,g n) ∈ (absoluteMomentumPower 2).graph ∧ IsCompact (L n) ∧
        (∀ᵐ x ∂(volume : Measure GW.Space), x ∉ L n → f n x = 0)) ∧
      Tendsto f atTop (𝓝 u.val) ∧ Tendsto g atTop (𝓝 (absoluteMomentumPower 2 u)) := by
  obtain ⟨v,hv,hw⟩ := momentum_second_domain_forward u.val u.property
  let w (i : Fin 3) := (hw i i).choose
  have hw' (i : Fin 3) : (v i,w i) ∈ (momentumOperator i).graph := (hw i i).choose_spec
  have hz : (∑ i, w i) = absoluteMomentumPower 2 u :=
    (absoluteMomentumPower (H := E) 2).mem_graph_snd_inj (momentum_second_sum_graph u.val v w hv hw')
      ((absoluteMomentumPower 2).mem_graph u) rfl
  let f (n : ℕ) := weakCutoffL2 (weakCutoffStep n) u.val
  let g (n : ℕ) := smoothCoreSquareOutput (weakCutoffStep n) (weakCutoffStep_pos n) u.val v w
  refine ⟨f,g,fun n => tsupport (weakPlateauScaled (weakCutoffStep n)),?_,weakCutoffL2_tendsto u.val,?_⟩
  · intro n
    exact ⟨smoothCoreCutoff_square_graph _ (weakCutoffStep_pos n) u.val v w hv hw',
      weakPlateauScaled_hasCompactSupport _ (weakCutoffStep_pos n),smoothCoreCutoff_support _ u.val⟩
  · rw [← hz]
    exact smoothCoreSquareOutput_tendsto u.val v w

lemma smoothCoreFirst_compact_graph_approximation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (u : (absoluteMomentumPower (H := E) 1).domain) :
    ∃ (f g : ℕ → ElectronHilbertL2 (E := E)) (L : ℕ → Set GW.Space),
      (∀ n, (f n,g n) ∈ (absoluteMomentumPower 1).graph ∧ IsCompact (L n) ∧
        (∀ᵐ x ∂(volume : Measure GW.Space), x ∉ L n → f n x = 0)) ∧
      Tendsto f atTop (𝓝 u.val) ∧ Tendsto g atTop (𝓝 (absoluteMomentumPower 1 u)) := by
  obtain ⟨v,hv⟩ := smoothCoreFirst_domain_forward u.val u.property
  let f (n : ℕ) := weakCutoffL2 (weakCutoffStep n) u.val
  let v' (n : ℕ) (i : Fin 3) := smoothCoreFirstOutput (weakCutoffStep n) (weakCutoffStep_pos n) i u.val (v i)
  have hv' (n : ℕ) (i : Fin 3) : (f n,v' n i) ∈ (momentumOperator i).graph :=
    smoothCoreCutoff_first_graph _ (weakCutoffStep_pos n) i u.val (v i) (hv i)
  have hf (n : ℕ) : f n ∈ (absoluteMomentumPower (H := E) 1).domain := smoothCoreFirst_domain_reverse (f n) (v' n) (hv' n)
  let g (n : ℕ) := absoluteMomentumPower 1 ⟨f n,hf n⟩
  have hg (n : ℕ) : (f n,g n) ∈ (absoluteMomentumPower (H := E) 1).graph :=
    (absoluteMomentumPower 1).mem_graph ⟨f n,hf n⟩
  have hs (n : ℕ) : ‖g n-absoluteMomentumPower 1 u‖^2 = ∑ i : Fin 3, ‖v' n i-v i‖^2 :=
    smoothCoreAbsoluteMomentum_norm_sq (f n-u.val) (g n-absoluteMomentumPower 1 u)
      (fun i => v' n i-v i)
      ((absoluteMomentumPower 1).graph.sub_mem (hg n) ((absoluteMomentumPower 1).mem_graph u))
      (fun i => (momentumOperator i).graph.sub_mem (hv' n i) (hv i))
  have hsum : Tendsto (fun n => ∑ i : Fin 3, ‖v' n i-v i‖^2) atTop (𝓝 0) := by
    have hi (i : Fin 3) : Tendsto (fun n => ‖v' n i-v i‖^2) atTop (𝓝 0) := by
      simpa only [sub_self,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0)] using
        (((smoothCoreFirstOutput_tendsto i u.val (v i)).sub_const (v i)).norm.pow 2)
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _ => hi i)
  have hsq : Tendsto (fun n => ‖g n-absoluteMomentumPower 1 u‖^2) atTop (𝓝 0) :=
    hsum.congr' (Eventually.of_forall (fun n => (hs n).symm))
  have hn : Tendsto (fun n => ‖g n-absoluteMomentumPower 1 u‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp hsq)
  refine ⟨f,g,fun n => tsupport (weakPlateauScaled (weakCutoffStep n)),?_,weakCutoffL2_tendsto u.val,?_⟩
  · intro n
    exact ⟨hg n,weakPlateauScaled_hasCompactSupport _ (weakCutoffStep_pos n),smoothCoreCutoff_support _ u.val⟩
  · exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

lemma smoothCoreTest_toSchwartz_L2 (φ : SmoothScalarTest) :
    φ.toL2 = φ.toSchwartzMap.toLp 2 (volume : Measure GW.Space) := by
  apply Lp.ext
  filter_upwards [φ.toL2_ae,φ.toSchwartzMap.coeFn_toLp 2 (volume : Measure GW.Space)] with x hx hy
  exact hx.trans hy.symm

lemma smoothCoreTest_momentum_graph (φ : SmoothScalarTest) (i : Fin 3) :
    (φ.toL2,(schwartzMomentumDerivative i φ.toSchwartzMap).toLp 2 volume) ∈ (momentumOperator i).graph := by
  rw [smoothCoreTest_toSchwartz_L2]
  exact momentumOperator_schwartz_graph i φ.toSchwartzMap

lemma smoothCoreTest_square_mem (φ : SmoothScalarTest) : φ.toL2 ∈ (absoluteMomentumPower (H := ℂ) 2).domain := by
  let v (i : Fin 3) := (schwartzMomentumDerivative i φ.toSchwartzMap).toLp 2 volume
  let w (i : Fin 3) := (schwartzMomentumDerivative i (schwartzMomentumDerivative i φ.toSchwartzMap)).toLp 2 volume
  exact momentum_second_domain_reverse φ.toL2
    ⟨v,fun i => smoothCoreTest_momentum_graph φ i,
      fun i => ⟨w i,momentumOperator_schwartz_graph i (schwartzMomentumDerivative i φ.toSchwartzMap)⟩⟩

lemma smoothCoreTest_first_mem (φ : SmoothScalarTest) : φ.toL2 ∈ (absoluteMomentumPower (H := ℂ) 1).domain :=
  smoothCoreFirst_domain_reverse φ.toL2 (fun i => (schwartzMomentumDerivative i φ.toSchwartzMap).toLp 2 volume)
    (fun i => smoothCoreTest_momentum_graph φ i)

def smoothCoreGraphError {E : Type*} [NormedAddCommGroup E] (u a f g : E) : ℝ :=
  ‖f-u‖+‖g-a‖

lemma smoothCoreGraphError_tendsto {E : Type*} [NormedAddCommGroup E]
    (u a : E) (f g : ℕ → E) (hf : Tendsto f atTop (𝓝 u)) (hg : Tendsto g atTop (𝓝 a)) :
    Tendsto (fun n => smoothCoreGraphError u a (f n) (g n)) atTop (𝓝 0) := by
  simpa only [smoothCoreGraphError,sub_self,norm_zero,add_zero] using
    ((hf.sub_const u).norm.add (hg.sub_const a).norm)

lemma smoothCorePositiveIndex_exists (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (ℓ : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ R : ℕ, 1 ≤ R ∧ ℓ ≤ R ∧ e (R-1) < δ := by
  have hs : ∀ᶠ n : ℕ in atTop, e n < δ := he.eventually (Iio_mem_nhds hδ)
  obtain ⟨n,hn,herr⟩ := ((eventually_ge_atTop ℓ).and hs).exists
  exact ⟨n+1,by omega,by omega,by simpa only [Nat.add_sub_cancel] using herr⟩

def smoothCoreLeastPositiveIndex (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (ℓ : ℕ) (δ : ℝ) (hδ : 0 < δ) : ℕ :=
  Nat.find (smoothCorePositiveIndex_exists e he ℓ δ hδ)

lemma smoothCoreLeastPositiveIndex_spec (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (ℓ : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    1 ≤ smoothCoreLeastPositiveIndex e he ℓ δ hδ ∧ ℓ ≤ smoothCoreLeastPositiveIndex e he ℓ δ hδ ∧
      e (smoothCoreLeastPositiveIndex e he ℓ δ hδ-1) < δ :=
  Nat.find_spec (smoothCorePositiveIndex_exists e he ℓ δ hδ)

lemma smoothCoreLeastPositiveIndex_min (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (ℓ : ℕ) (δ : ℝ) (hδ : 0 < δ) (R : ℕ) (hR : 1 ≤ R ∧ ℓ ≤ R ∧ e (R-1) < δ) :
    smoothCoreLeastPositiveIndex e he ℓ δ hδ ≤ R :=
  Nat.find_min' (smoothCorePositiveIndex_exists e he ℓ δ hδ) hR

def smoothCoreMollifierStep (n : ℕ) : ℝ := (weakCutoffStep n)⁻¹

lemma smoothCoreMollifierStep_pos (n : ℕ) : 0 < smoothCoreMollifierStep n := inv_pos.mpr (weakCutoffStep_pos n)

lemma smoothCoreMollifierStep_tendsto : Tendsto smoothCoreMollifierStep atTop (𝓝[>] (0:ℝ)) :=
  tendsto_nhdsWithin_iff.mpr ⟨tendsto_inv_atTop_zero.comp weakCutoffStep_tendsto,
    Eventually.of_forall smoothCoreMollifierStep_pos⟩

lemma smoothCoreSquare_mollified_graph_approximation
    (u : (absoluteMomentumPower (H := ℂ) 2).domain) (L : Set GW.Space) (hL : IsCompact L)
    (hzero : ∀ᵐ x ∂(volume : Measure GW.Space), x ∉ L → u.val x = 0) :
    ∃ (φ : ℕ → SmoothScalarTest) (g : ℕ → GW.OnePhonon),
      (∀ n, ((φ n).toL2,g n) ∈ (absoluteMomentumPower 2).graph) ∧
      Tendsto (fun n => (φ n).toL2) atTop (𝓝 u.val) ∧ Tendsto g atTop (𝓝 (absoluteMomentumPower 2 u)) := by
  obtain ⟨v,hv,hw⟩ := momentum_second_domain_forward u.val u.property
  let w (i : Fin 3) := (hw i i).choose
  have hw' (i : Fin 3) : (v i,w i) ∈ (momentumOperator i).graph := (hw i i).choose_spec
  have hz : (∑ i, w i) = absoluteMomentumPower 2 u :=
    (absoluteMomentumPower (H := ℂ) 2).mem_graph_snd_inj (momentum_second_sum_graph u.val v w hv hw')
      ((absoluteMomentumPower 2).mem_graph u) rfl
  let φ (n : ℕ) := smoothCoreMollifiedTest u.val L hL hzero (smoothCoreMollifierStep n) (smoothCoreMollifierStep_pos n)
  let g (n : ℕ) := ∑ i : Fin 3, mollifiedTranslation (w i) (smoothCoreMollifierStep n)
  have hφ (n : ℕ) : (φ n).toL2 = mollifiedTranslation u.val (smoothCoreMollifierStep n) :=
    smoothCoreMollifiedTest_toL2 u.val L hL hzero _ _
  refine ⟨φ,g,?_,?_,?_⟩
  · intro n
    rw [hφ n]
    exact smoothCoreMollification_square_graph _ u.val v w hv hw'
  · exact ((mollifiedTranslation_tendsto u.val).comp smoothCoreMollifierStep_tendsto).congr'
      (Eventually.of_forall (fun n => (hφ n).symm))
  · rw [← hz]
    exact tendsto_finsetSum Finset.univ (fun i _ => (mollifiedTranslation_tendsto (w i)).comp smoothCoreMollifierStep_tendsto)

lemma smoothCoreFirst_graph_tendsto
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (u a : ElectronHilbertL2 (E := E)) (v : Fin 3 → ElectronHilbertL2 (E := E))
    (f g : ℕ → ElectronHilbertL2 (E := E)) (w : ℕ → Fin 3 → ElectronHilbertL2 (E := E))
    (ha : (u,a) ∈ (absoluteMomentumPower 1).graph) (hv : ∀ i, (u,v i) ∈ (momentumOperator i).graph)
    (hf : ∀ n, (f n,g n) ∈ (absoluteMomentumPower 1).graph)
    (hw : ∀ n i, (f n,w n i) ∈ (momentumOperator i).graph)
    (ht : ∀ i, Tendsto (fun n => w n i) atTop (𝓝 (v i))) : Tendsto g atTop (𝓝 a) := by
  have hs (n : ℕ) : ‖g n-a‖^2 = ∑ i : Fin 3, ‖w n i-v i‖^2 :=
    smoothCoreAbsoluteMomentum_norm_sq (f n-u) (g n-a) (fun i => w n i-v i)
      ((absoluteMomentumPower 1).graph.sub_mem (hf n) ha) (fun i => (momentumOperator i).graph.sub_mem (hw n i) (hv i))
  have hsum : Tendsto (fun n => ∑ i : Fin 3, ‖w n i-v i‖^2) atTop (𝓝 0) := by
    have hi (i : Fin 3) : Tendsto (fun n => ‖w n i-v i‖^2) atTop (𝓝 0) := by
      simpa only [sub_self,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0)] using (((ht i).sub_const (v i)).norm.pow 2)
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _ => hi i)
  have hsq : Tendsto (fun n => ‖g n-a‖^2) atTop (𝓝 0) := hsum.congr' (Eventually.of_forall (fun n => (hs n).symm))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using (Real.continuous_sqrt.continuousAt.tendsto.comp hsq)

lemma smoothCoreFirst_mollified_graph_approximation
    (u : (absoluteMomentumPower (H := ℂ) 1).domain) (L : Set GW.Space) (hL : IsCompact L)
    (hzero : ∀ᵐ x ∂(volume : Measure GW.Space), x ∉ L → u.val x = 0) :
    ∃ (φ : ℕ → SmoothScalarTest) (g : ℕ → GW.OnePhonon),
      (∀ n, ((φ n).toL2,g n) ∈ (absoluteMomentumPower 1).graph) ∧
      Tendsto (fun n => (φ n).toL2) atTop (𝓝 u.val) ∧ Tendsto g atTop (𝓝 (absoluteMomentumPower 1 u)) := by
  obtain ⟨v,hv⟩ := smoothCoreFirst_domain_forward u.val u.property
  let f (n : ℕ) := mollifiedTranslation u.val (smoothCoreMollifierStep n)
  let w (n : ℕ) (i : Fin 3) := mollifiedTranslation (v i) (smoothCoreMollifierStep n)
  have hw (n : ℕ) (i : Fin 3) : (f n,w n i) ∈ (momentumOperator i).graph :=
    smoothCoreMollification_momentum_graph _ i u.val (v i) (hv i)
  have hf (n : ℕ) : f n ∈ (absoluteMomentumPower (H := ℂ) 1).domain := smoothCoreFirst_domain_reverse (f n) (w n) (hw n)
  let g (n : ℕ) := absoluteMomentumPower 1 ⟨f n,hf n⟩
  let φ (n : ℕ) := smoothCoreMollifiedTest u.val L hL hzero (smoothCoreMollifierStep n) (smoothCoreMollifierStep_pos n)
  have hφ (n : ℕ) : (φ n).toL2 = f n := smoothCoreMollifiedTest_toL2 u.val L hL hzero _ _
  have hg (n : ℕ) : (f n,g n) ∈ (absoluteMomentumPower (H := ℂ) 1).graph := (absoluteMomentumPower 1).mem_graph ⟨f n,hf n⟩
  refine ⟨φ,g,?_,?_,?_⟩
  · intro n
    rw [hφ n]
    exact hg n
  · exact ((mollifiedTranslation_tendsto u.val).comp smoothCoreMollifierStep_tendsto).congr'
      (Eventually.of_forall (fun n => (hφ n).symm))
  · exact smoothCoreFirst_graph_tendsto u.val (absoluteMomentumPower 1 u) v f g w
      ((absoluteMomentumPower 1).mem_graph u) hv hg hw
      (fun i => (mollifiedTranslation_tendsto (v i)).comp smoothCoreMollifierStep_tendsto)

lemma smoothCore_nested_diagonal
    (A : GW.OnePhonon →ₗ.[ℂ] GW.OnePhonon)
    (hc : ∀ u : A.domain, ∃ (f g : ℕ → GW.OnePhonon) (L : ℕ → Set GW.Space),
      (∀ n, (f n,g n) ∈ A.graph ∧ IsCompact (L n) ∧
        (∀ᵐ x ∂(volume : Measure GW.Space), x ∉ L n → f n x = 0)) ∧
      Tendsto f atTop (𝓝 u.val) ∧ Tendsto g atTop (𝓝 (A u)))
    (hm : ∀ (u : A.domain) (L : Set GW.Space), IsCompact L →
      (∀ᵐ x ∂(volume : Measure GW.Space), x ∉ L → u.val x = 0) →
      ∃ (φ : ℕ → SmoothScalarTest) (g : ℕ → GW.OnePhonon),
        (∀ n, ((φ n).toL2,g n) ∈ A.graph) ∧
        Tendsto (fun n => (φ n).toL2) atTop (𝓝 u.val) ∧ Tendsto g atTop (𝓝 (A u)))
    (u : A.domain) :
    ∃ (φ : ℕ → SmoothScalarTest) (g : ℕ → GW.OnePhonon),
      (∀ n, ((φ n).toL2,g n) ∈ A.graph ∧
        smoothCoreGraphError u.val (A u) ((φ n).toL2) (g n) < 1 / (n+1:ℝ)) := by
  obtain ⟨f,g,L,hfg,hf,hg⟩ := hc u
  have he := smoothCoreGraphError_tendsto u.val (A u) f g hf hg
  have hn (n : ℕ) : 0 < 1 / (2 * (n+1:ℝ)) := by positivity
  let R (n : ℕ) := smoothCoreLeastPositiveIndex _ he (n+1) _ (hn n)
  have hR (n : ℕ) := smoothCoreLeastPositiveIndex_spec _ he (n+1) _ (hn n)
  have hmem (n : ℕ) : f (R n-1) ∈ A.domain := by
    obtain ⟨w,hw,_⟩ := A.mem_graph_iff.mp (hfg (R n-1)).1
    have hw' : w.val = f (R n-1) := hw
    rw [← hw']
    exact w.property
  let v (n : ℕ) : A.domain := ⟨f (R n-1),hmem n⟩
  have hv (n : ℕ) : A (v n) = g (R n-1) :=
    A.mem_graph_snd_inj (A.mem_graph (v n)) (hfg (R n-1)).1 rfl
  have hex (n : ℕ) := hm (v n) (L (R n-1)) (hfg (R n-1)).2.1 (hfg (R n-1)).2.2
  choose φ z hz hφ hzlim using hex
  have hem (n : ℕ) := smoothCoreGraphError_tendsto (v n).val (A (v n)) _ _ (hφ n) (hzlim n)
  let J (n : ℕ) := smoothCoreLeastPositiveIndex _ (hem n) (n+1) _ (hn n)
  have hJ (n : ℕ) := smoothCoreLeastPositiveIndex_spec _ (hem n) (n+1) _ (hn n)
  refine ⟨fun n => φ n (J n-1),fun n => z n (J n-1),fun n => ⟨hz n _,?_⟩⟩
  have hr : smoothCoreGraphError u.val (A u) (f (R n-1)) (g (R n-1)) < 1/(2*(n+1:ℝ)) := (hR n).2.2
  have hj : smoothCoreGraphError (f (R n-1)) (g (R n-1)) ((φ n (J n-1)).toL2) (z n (J n-1)) < 1/(2*(n+1:ℝ)) := by
    have hj0 : smoothCoreGraphError (v n).val (A (v n)) ((φ n (J n-1)).toL2) (z n (J n-1)) < 1/(2*(n+1:ℝ)) := (hJ n).2.2
    rw [hv n] at hj0
    exact hj0
  unfold smoothCoreGraphError at *
  have ha := norm_sub_le_norm_sub_add_norm_sub ((φ n (J n-1)).toL2) (f (R n-1)) u.val
  have hb := norm_sub_le_norm_sub_add_norm_sub (z n (J n-1)) (g (R n-1)) (A u)
  have hd : 1/(2*(n+1:ℝ)) + 1/(2*(n+1:ℝ)) = 1/(n+1:ℝ) := by
    have hn1 : (n+1:ℝ) ≠ 0 := by positivity
    field_simp [hn1]
    <;> ring
  linarith

lemma smoothCore_square_approximation (u : (absoluteMomentumPower (H := ℂ) 2).domain) :
    ∃ (φ : ℕ → SmoothScalarTest) (g : ℕ → GW.OnePhonon),
      ∀ n, ((φ n).toL2,g n) ∈ (absoluteMomentumPower 2).graph ∧
        smoothCoreGraphError u.val (absoluteMomentumPower 2 u) ((φ n).toL2) (g n) < 1/(n+1:ℝ) :=
  smoothCore_nested_diagonal (absoluteMomentumPower 2)
    smoothCoreSquare_compact_graph_approximation smoothCoreSquare_mollified_graph_approximation u

lemma smoothCore_first_approximation (u : (absoluteMomentumPower (H := ℂ) 1).domain) :
    ∃ (φ : ℕ → SmoothScalarTest) (g : ℕ → GW.OnePhonon),
      ∀ n, ((φ n).toL2,g n) ∈ (absoluteMomentumPower 1).graph ∧
        smoothCoreGraphError u.val (absoluteMomentumPower 1 u) ((φ n).toL2) (g n) < 1/(n+1:ℝ) :=
  smoothCore_nested_diagonal (absoluteMomentumPower 1)
    smoothCoreFirst_compact_graph_approximation smoothCoreFirst_mollified_graph_approximation u

lemma smoothCore_graph_dense_of_approximation
    (A : GW.OnePhonon →ₗ.[ℂ] GW.OnePhonon)
    (h : ∀ u : A.domain, ∃ (φ : ℕ → SmoothScalarTest) (g : ℕ → GW.OnePhonon),
      ∀ n, ((φ n).toL2,g n) ∈ A.graph ∧
        smoothCoreGraphError u.val (A u) ((φ n).toL2) (g n) < 1/(n+1:ℝ))
    (u : A.domain) (ε : ℝ) (hε : 0 < ε) :
    ∃ (φ : SmoothScalarTest) (v : A.domain), v.val = φ.toL2 ∧
      ‖v.val-u.val‖+‖A v-A u‖ < ε := by
  obtain ⟨φ,g,hfg⟩ := h u
  have ht : Tendsto (fun n : ℕ => 1/(n+1:ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,one_div,weakCutoffStep] using tendsto_inv_atTop_zero.comp weakCutoffStep_tendsto
  obtain ⟨n,hn⟩ := (ht.eventually (Iio_mem_nhds hε)).exists
  obtain ⟨v,hv,ha⟩ := A.mem_graph_iff.mp (hfg n).1
  refine ⟨φ n,v,hv,?_⟩
  rw [hv,ha]
  exact lt_trans (hfg n).2 hn

lemma smoothCore_square_graph_dense
    (u : (absoluteMomentumPower (H := ℂ) 2).domain) (ε : ℝ) (hε : 0 < ε) :
    ∃ (φ : SmoothScalarTest) (v : (absoluteMomentumPower (H := ℂ) 2).domain),
      v.val = φ.toL2 ∧ ‖v.val-u.val‖+‖absoluteMomentumPower 2 v-absoluteMomentumPower 2 u‖ < ε :=
  smoothCore_graph_dense_of_approximation _ smoothCore_square_approximation u ε hε

lemma smoothCore_first_graph_dense
    (u : (absoluteMomentumPower (H := ℂ) 1).domain) (ε : ℝ) (hε : 0 < ε) :
    ∃ (φ : SmoothScalarTest) (v : (absoluteMomentumPower (H := ℂ) 1).domain),
      v.val = φ.toL2 ∧ ‖v.val-u.val‖+‖absoluteMomentumPower 1 v-absoluteMomentumPower 1 u‖ < ε :=
  smoothCore_graph_dense_of_approximation _ smoothCore_first_approximation u ε hε

end GW.Analysis
