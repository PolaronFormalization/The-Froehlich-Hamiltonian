module
public import GW.Analysis.BridgePhaseDerivative
public import GW.Analysis.BridgeShear
public import GW.Analysis.CutoffExtension
public import GW.Fock.FockFiberFields
public import GW.Fock.FockGeneralizedBounds
public import GW.Fock.FockSmoothProductCore
public import GW.Regularity.RegComponentDomain
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic

/-! Source fock:frank-schlein, manuscript4942–5050.
Sharp exact convolution-supremum annihilation bound on the original joint multiplier
domain, including unrestricted vacuum, by ordered inverse factor and closedness. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Fock


/- Source argument component Core. -/
def frankSchleinIntegrand (f : GW.OnePhonon) (q k : GW.Space) : ℝ :=
  ‖f k‖^2 / (1+‖q-k‖^2)

def frankSchleinIntegral (f : GW.OnePhonon) (q : GW.Space) : ℝ :=
  ∫ k, frankSchleinIntegrand f q k

lemma frankSchleinIntegrand_nonneg (f : GW.OnePhonon) (q k : GW.Space) :
    0 ≤ frankSchleinIntegrand f q k := div_nonneg (sq_nonneg _) (by positivity)

lemma frankSchleinIntegrand_bound (f : GW.OnePhonon) (q k : GW.Space) :
    ‖frankSchleinIntegrand f q k‖ ≤ ‖f k‖^2 := by
  rw [Real.norm_eq_abs,abs_of_nonneg (frankSchleinIntegrand_nonneg f q k)]
  exact div_le_self (sq_nonneg _) (by nlinarith [sq_nonneg ‖q-k‖])

lemma frankSchleinIntegrand_measurable (f : GW.OnePhonon) (q : GW.Space) :
    StronglyMeasurable (frankSchleinIntegrand f q) :=
  ((Lp.stronglyMeasurable f).norm.pow 2).div
    ((continuous_const.add ((continuous_const.sub continuous_id).norm.pow 2)).stronglyMeasurable)

lemma frankSchleinIntegrand_integrable (f : GW.OnePhonon) (q : GW.Space) :
    Integrable (frankSchleinIntegrand f q) :=
  ((Lp.memLp f).integrable_norm_pow (p := 2) (by norm_num)).mono'
    (frankSchleinIntegrand_measurable f q).aestronglyMeasurable
    (Eventually.of_forall (frankSchleinIntegrand_bound f q))

lemma frankSchleinIntegral_nonneg (f : GW.OnePhonon) (q : GW.Space) :
    0 ≤ frankSchleinIntegral f q := integral_nonneg (frankSchleinIntegrand_nonneg f q)

lemma frankSchleinIntegral_le (f : GW.OnePhonon) (q : GW.Space) :
    frankSchleinIntegral f q ≤ ‖f‖^2 := by
  rw [GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
  apply integral_mono (frankSchleinIntegrand_integrable f q)
  · exact (Lp.memLp f).integrable_norm_pow (p := 2) (by norm_num)
  · intro k
    exact le_trans (le_abs_self _) (frankSchleinIntegrand_bound f q k)

lemma frankSchleinIntegral_continuous (f : GW.OnePhonon) : Continuous (frankSchleinIntegral f) := by
  apply continuous_of_dominated
    (fun q => (frankSchleinIntegrand_measurable f q).aestronglyMeasurable)
    (fun q => Eventually.of_forall (frankSchleinIntegrand_bound f q))
    ((Lp.memLp f).integrable_norm_pow (p := 2) (by norm_num))
  exact Eventually.of_forall (fun k => continuous_const.div
    (continuous_const.add ((continuous_id.sub continuous_const).norm.pow 2))
    (fun q => by positivity))

def frankSchleinSup (f : GW.OnePhonon) : ℝ := sSup (Set.range (frankSchleinIntegral f))
def frankSchleinConstant (f : GW.OnePhonon) : ℝ := Real.sqrt (frankSchleinSup f)

lemma frankSchlein_range_bdd (f : GW.OnePhonon) : BddAbove (Set.range (frankSchleinIntegral f)) :=
  ⟨‖f‖^2,by rintro _ ⟨q,rfl⟩; exact frankSchleinIntegral_le f q⟩

lemma frankSchleinIntegral_le_sup (f : GW.OnePhonon) (q : GW.Space) :
    frankSchleinIntegral f q ≤ frankSchleinSup f :=
  le_csSup (frankSchlein_range_bdd f) ⟨q,rfl⟩

lemma frankSchleinSup_nonneg (f : GW.OnePhonon) : 0 ≤ frankSchleinSup f :=
  (frankSchleinIntegral_nonneg f 0).trans (frankSchleinIntegral_le_sup f 0)

lemma frankSchleinSup_le (f : GW.OnePhonon) : frankSchleinSup f ≤ ‖f‖^2 :=
  csSup_le (Set.range_nonempty _) (by rintro _ ⟨q,rfl⟩; exact frankSchleinIntegral_le f q)

lemma frankSchleinConstant_nonneg (f : GW.OnePhonon) : 0 ≤ frankSchleinConstant f := Real.sqrt_nonneg _
lemma frankSchleinConstant_sq (f : GW.OnePhonon) : frankSchleinConstant f ^ 2 = frankSchleinSup f :=
  Real.sq_sqrt (frankSchleinSup_nonneg f)
lemma frankSchleinConstant_le (f : GW.OnePhonon) : frankSchleinConstant f ≤ ‖f‖ := by
  have h := Real.sqrt_le_sqrt (frankSchleinSup_le f)
  simpa only [frankSchleinConstant,Real.sqrt_sq_eq_abs,abs_norm] using h

lemma frankSchleinIntegral_le_constant_sq (f : GW.OnePhonon) (q : GW.Space) :
    frankSchleinIntegral f q ≤ frankSchleinConstant f ^ 2 := by
  rw [frankSchleinConstant_sq]
  exact frankSchleinIntegral_le_sup f q

def frankSchleinElectronWeight (q : GW.Space) : ℝ := Real.sqrt (1+‖q‖^2)
def frankSchleinInverseSymbol (q : GW.Space) : ℂ := ((frankSchleinElectronWeight q)⁻¹ : ℝ)

lemma frankSchleinElectronWeight_one (q : GW.Space) : 1 ≤ frankSchleinElectronWeight q :=
  Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg ‖q‖])

lemma frankSchleinInverseSymbol_continuous : Continuous frankSchleinInverseSymbol := by
  unfold frankSchleinInverseSymbol frankSchleinElectronWeight
  exact Complex.continuous_ofReal.comp ((Real.continuous_sqrt.comp
    (continuous_const.add (continuous_norm.pow 2))).inv₀
      (fun q => ne_of_gt (lt_of_lt_of_le zero_lt_one (frankSchleinElectronWeight_one q))))

lemma frankSchleinInverseSymbol_bound (q : GW.Space) : ‖frankSchleinInverseSymbol q‖ ≤ 1 := by
  unfold frankSchleinInverseSymbol
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr
    (zero_le_one.trans (frankSchleinElectronWeight_one q)))]
  exact inv_le_one_of_one_le₀ (frankSchleinElectronWeight_one q)

def frankSchleinInverseFourier : ElectronL2 →L[ℂ] ElectronL2 :=
  GW.Analysis.boundedMultiplier frankSchleinInverseSymbol frankSchleinInverseSymbol_continuous.measurable
    (C := 1) (Eventually.of_forall frankSchleinInverseSymbol_bound)

def frankSchleinElectronInverse : ElectronL2 →L[ℂ] ElectronL2 :=
  (GW.Analysis.physicalFourierUnitary.symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    (frankSchleinInverseFourier.comp
      GW.Analysis.physicalFourierUnitary.toContinuousLinearEquiv.toContinuousLinearMap)

def frankSchleinRegularizedKernel (f : OneBoson) : BosonKernel ElectronL2 :=
  (amplify (volume : Measure GW.Space) frankSchleinElectronInverse).comp (phaseMultiplicationKernel f)

lemma frankSchleinElectronInverse_norm (u : ElectronL2) : ‖frankSchleinElectronInverse u‖ ≤ ‖u‖ := by
  change ‖GW.Analysis.physicalFourierUnitary.symm
    (frankSchleinInverseFourier (GW.Analysis.physicalFourierUnitary u))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  calc
    _ ≤ 1 * ‖GW.Analysis.physicalFourierUnitary u‖ := by
      apply GW.Analysis.maximalMultiplier_norm_le frankSchleinInverseSymbol
        (Eventually.of_forall frankSchleinInverseSymbol_bound)
    _ = _ := by rw [one_mul,LinearIsometryEquiv.norm_map]

lemma frankSchleinRegularizedKernel_adjoint (f : OneBoson) :
    (frankSchleinRegularizedKernel f).adjoint =
      (phaseMultiplicationKernel f).adjoint.comp
        (amplify (volume : Measure GW.Space) frankSchleinElectronInverse).adjoint := by
  exact ContinuousLinearMap.adjoint_comp _ _

lemma frankSchleinInverseFourier_pairing (u v : ElectronL2) :
    ⟪frankSchleinInverseFourier u,v⟫_ℂ = ⟪u,frankSchleinInverseFourier v⟫_ℂ := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  have hu := GW.Analysis.boundedMultiplier_ae frankSchleinInverseSymbol
    frankSchleinInverseSymbol_continuous.measurable
    (C := 1) (Eventually.of_forall frankSchleinInverseSymbol_bound) u
  have hv := GW.Analysis.boundedMultiplier_ae frankSchleinInverseSymbol
    frankSchleinInverseSymbol_continuous.measurable
    (C := 1) (Eventually.of_forall frankSchleinInverseSymbol_bound) v
  filter_upwards [hu,hv] with q hq hk
  change inner ℂ (frankSchleinInverseFourier u q) (v q) = inner ℂ (u q) (frankSchleinInverseFourier v q)
  change frankSchleinInverseSymbol q • u q = frankSchleinInverseFourier u q at hq
  change frankSchleinInverseSymbol q • v q = frankSchleinInverseFourier v q at hk
  rw [← hq,← hk,inner_smul_left,inner_smul_right]
  simp only [frankSchleinInverseSymbol,Complex.conj_ofReal]

lemma frankSchleinElectronInverse_pairing (u v : ElectronL2) :
    ⟪frankSchleinElectronInverse u,v⟫_ℂ = ⟪u,frankSchleinElectronInverse v⟫_ℂ := by
  rw [← GW.Analysis.physicalFourierUnitary.inner_map_map (frankSchleinElectronInverse u) v,
    ← GW.Analysis.physicalFourierUnitary.inner_map_map u (frankSchleinElectronInverse v)]
  change inner ℂ (GW.Analysis.physicalFourierUnitary
    (GW.Analysis.physicalFourierUnitary.symm (frankSchleinInverseFourier (GW.Analysis.physicalFourierUnitary u))))
    (GW.Analysis.physicalFourierUnitary v) =
    inner ℂ (GW.Analysis.physicalFourierUnitary u) (GW.Analysis.physicalFourierUnitary
    (GW.Analysis.physicalFourierUnitary.symm (frankSchleinInverseFourier (GW.Analysis.physicalFourierUnitary v))))
  rw [LinearIsometryEquiv.apply_symm_apply,LinearIsometryEquiv.apply_symm_apply]
  exact frankSchleinInverseFourier_pairing _ _

lemma frankSchlein_adjoint_of_pairing {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (hp : ∀ u v, ⟪A u,v⟫_ℂ = ⟪u,A v⟫_ℂ) : A.adjoint = A := by
  symm
  exact (ContinuousLinearMap.eq_adjoint_iff _ _).mpr hp

lemma frankSchleinElectronInverse_adjoint : frankSchleinElectronInverse.adjoint = frankSchleinElectronInverse := by
  exact frankSchlein_adjoint_of_pairing frankSchleinElectronInverse frankSchleinElectronInverse_pairing

lemma frankSchlein_adjoint_order_generic
    {Y H E : Type*} [MeasurableSpace Y]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (ν : Measure Y) (T : H →L[ℂ] H) (hT : T.adjoint = T) (F : E →L[ℂ] Lp H 2 ν) :
    ((amplify ν T).comp F).adjoint = F.adjoint.comp (amplify ν T) := by
  rw [ContinuousLinearMap.adjoint_comp,amplify_adjoint,hT]

lemma frankSchleinRegularizedKernel_order (f : OneBoson) :
    (frankSchleinRegularizedKernel f).adjoint = (phaseMultiplicationKernel f).adjoint.comp
      (amplify (volume : Measure GW.Space) frankSchleinElectronInverse) := by
  exact frankSchlein_adjoint_order_generic volume frankSchleinElectronInverse
    frankSchleinElectronInverse_adjoint (phaseMultiplicationKernel f)

/-- The source joint multiplier, including a zero weight on the whole vacuum fiber. -/
def frankSchleinJointOperator : Physical →ₗ.[ℂ] Physical := physicalSectorMultiplier mixedRootNumberSymbol

lemma frankSchleinJointSymbol_sq (n : ℕ) (q : GW.Space) :
    mixedRootNumberSymbol n q ^ 2 = (n:ℝ)*(1+‖q‖^2) := by
  unfold mixedRootNumberSymbol
  rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _),Real.sq_sqrt (by positivity)]

lemma frankSchleinJointSymbol_vacuum (q : GW.Space) : mixedRootNumberSymbol 0 q = 0 := by
  simp [mixedRootNumberSymbol]

def frankSchleinJointCutoff (u : frankSchleinJointOperator.domain) (R : ℕ) : frankSchleinJointOperator.domain :=
  ⟨freeCutoff R u.val,(freeCutoff_weighted mixedRootNumberSymbol R u).choose⟩

lemma frankSchleinJointCutoff_action (u : frankSchleinJointOperator.domain) (R : ℕ) :
    frankSchleinJointOperator (frankSchleinJointCutoff u R) = freeCutoff R (frankSchleinJointOperator u) :=
  (freeCutoff_weighted mixedRootNumberSymbol R u).choose_spec

lemma frankSchleinJointCutoff_input_tendsto (u : frankSchleinJointOperator.domain) :
    Tendsto (fun R => (frankSchleinJointCutoff u R).val) atTop (𝓝 u.val) := freeCutoff_tendsto u.val

lemma frankSchleinJointCutoff_output_tendsto (u : frankSchleinJointOperator.domain) :
    Tendsto (fun R => frankSchleinJointOperator (frankSchleinJointCutoff u R)) atTop
      (𝓝 (frankSchleinJointOperator u)) := by
  have he : (fun R => frankSchleinJointOperator (frankSchleinJointCutoff u R)) =
      (fun R => freeCutoff R (frankSchleinJointOperator u)) := funext (frankSchleinJointCutoff_action u)
  rw [he]
  exact freeCutoff_tendsto _

lemma frankSchleinJointCutoff_mem_H0 (u : frankSchleinJointOperator.domain) (R : ℕ) :
    (frankSchleinJointCutoff u R).val ∈ freeHamiltonian.domain := freeCutoff_mem_H0 R u.val

lemma frankSchlein_H0_mem_joint (u : freeHamiltonian.domain) : u.val ∈ frankSchleinJointOperator.domain := by
  let v : freeGraphOperator.domain := ⟨u.val,by rw [freeGraphOperator_domain];exact u.property⟩
  exact (freeGraph_mixed_rootNumber v).choose


def frankSchleinJointMass (u : Physical) : ℝ≥0∞ :=
  ∑' n : ℕ, ∫⁻ q : GW.Space, ENNReal.ofReal
    ((n:ℝ)*(1+‖q‖^2)*‖freeFourierRepresentation u n q‖^2) ∂volume

lemma frankSchleinJointMass_eq (u : Physical) :
    frankSchleinJointMass u = fourierWeightMass mixedRootNumberSymbol u := by
  unfold frankSchleinJointMass fourierWeightMass fourierWeightSquare
  simp_rw [norm_smul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,frankSchleinJointSymbol_sq]

lemma frankSchleinJoint_domain_iff (u : Physical) :
    u ∈ frankSchleinJointOperator.domain ↔ frankSchleinJointMass u ≠ ∞ := by
  rw [frankSchleinJointMass_eq]
  constructor
  · intro hu
    rw [fourierWeightMass_norm mixedRootNumberSymbol ⟨u,hu⟩]
    exact ENNReal.ofReal_ne_top
  · intro hu
    exact physicalSectorMultiplier_mem_of_mass mixedRootNumberSymbol mixedRootNumber_measurable u hu


/-- The source Fourier-side expression, bundled before identifying it with the actual kernel. -/
def frankSchleinShearedFourier (f : OneBoson) (u : ElectronL2) : ElectronBosonProduct :=
  GW.Analysis.productShearL2 (volume : Measure GW.Space) (fun k : GW.Space => k) measurable_id
    (productFunction volume volume (GW.Analysis.physicalFourierUnitary u) f)

lemma frankSchleinShearedFourier_norm (f : OneBoson) (u : ElectronL2) :
    ‖frankSchleinShearedFourier f u‖ = ‖f‖*‖u‖ := by
  unfold frankSchleinShearedFourier
  rw [LinearIsometryEquiv.norm_map,productFunction_norm,LinearIsometryEquiv.norm_map,mul_comm]

lemma frankSchleinShearedFourier_ae (f : OneBoson) (u : ElectronL2) :
    frankSchleinShearedFourier f u =ᵐ[(volume : Measure GW.Space).prod volume]
      (fun p => f p.2 * GW.Analysis.physicalFourierUnitary u (p.1+p.2)) := by
  have h₁ := GW.Analysis.productShearL2_ae (volume : Measure GW.Space) (fun k : GW.Space => k) measurable_id
    (productFunction volume volume (GW.Analysis.physicalFourierUnitary u) f)
  have h₂ := (GW.Analysis.productShear_preserving (volume : Measure GW.Space) (fun k : GW.Space => k)
    measurable_id).quasiMeasurePreserving.ae
    (productFunction_ae volume volume (GW.Analysis.physicalFourierUnitary u) f)
  filter_upwards [h₁,h₂] with p hp hq
  exact hp.trans (hq.trans (by simp only [GW.Analysis.productShear_apply,smul_eq_mul,mul_comm]))


lemma frankSchlein_phaseAt_modulation (u : ElectronL2) (k : GW.Space) :
    GW.Analysis.phaseAt u k = GW.Analysis.modulation k u := by
  apply Lp.ext
  filter_upwards [GW.Analysis.phaseAt_ae u k,GW.Analysis.modulation_ae k u] with x hx hy
  rw [hx,hy]
  simp only [GW.Analysis.physicalPhase,real_inner_comm,smul_eq_mul]

lemma frankSchleinPhaseSection_memLp (f : OneBoson) (u : ElectronL2) :
    MemLp (fun k => f k • GW.Analysis.phaseAt u k) 2 (volume : Measure GW.Space) := by
  apply (Lp.memLp f).of_le_mul (c := ‖u‖)
    ((Lp.aestronglyMeasurable f).smul (GW.Analysis.phaseAt_continuous u).aestronglyMeasurable)
  exact Eventually.of_forall (fun k => by
    change ‖f k • GW.Analysis.phaseAt u k‖ ≤ ‖u‖*‖f k‖
    rw [norm_smul,GW.Analysis.phaseAt_norm,mul_comm])

def frankSchleinPhaseBochner (f : OneBoson) (u : ElectronL2) : Lp ElectronL2 2 (volume : Measure GW.Space) :=
  (frankSchleinPhaseSection_memLp f u).toLp (fun k => f k • GW.Analysis.phaseAt u k)

lemma frankSchleinPhaseBochner_ae (f : OneBoson) (u : ElectronL2) :
    frankSchleinPhaseBochner f u =ᵐ[volume] (fun k => f k • GW.Analysis.phaseAt u k) := MemLp.coeFn_toLp _

lemma frankSchleinPhaseBochner_norm (f : OneBoson) (u : ElectronL2) :
    ‖frankSchleinPhaseBochner f u‖ = ‖f‖*‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
  calc
    _ = ∫ k, ‖f k‖^2 * ‖u‖^2 := by
      apply integral_congr_ae
      filter_upwards [frankSchleinPhaseBochner_ae f u] with k hk
      rw [hk,norm_smul,GW.Analysis.phaseAt_norm,mul_pow]
    _ = _ := by rw [integral_mul_const,← GW.Analysis.l2_norm_sq (𝕜 := ℂ),mul_pow]


lemma frankSchlein_closed_bound_extension
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B : H →ₗ.[ℂ] H) (hA : A.IsClosed) (u : B.domain) (v : ℕ → B.domain)
    (hm : ∀ n, (v n).val ∈ A.domain)
    (hin : Tendsto (fun n => (v n).val) atTop (𝓝 u.val))
    (hout : Tendsto (fun n => B (v n)) atTop (𝓝 (B u)))
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ n, ‖A ⟨(v n).val,hm n⟩‖ ≤ C*‖B (v n)‖)
    (hd : ∀ n m, ‖A ⟨(v n).val,hm n⟩-A ⟨(v m).val,hm m⟩‖ ≤ C*‖B (v n)-B (v m)‖) :
    ∃ hu : u.val ∈ A.domain, ‖A ⟨u.val,hu⟩‖ ≤ C*‖B u‖ := by
  have hc : CauchySeq (fun n => A ⟨(v n).val,hm n⟩) := by
    apply Metric.cauchySeq_iff.mpr
    intro δ hδ
    have hpos : 0 < C+1 := by linarith
    obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hout.cauchySeq (δ/(C+1)) (div_pos hδ hpos)
    refine ⟨N,fun n hn m hm' => ?_⟩
    rw [dist_eq_norm]
    have ht : ‖B (v n)-B (v m)‖ < δ/(C+1) := by simpa only [dist_eq_norm] using hN n hn m hm'
    calc
      _ ≤ C*‖B (v n)-B (v m)‖ := hd n m
      _ ≤ (C+1)*‖B (v n)-B (v m)‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < (C+1)*(δ/(C+1)) := mul_lt_mul_of_pos_left ht hpos
      _ = δ := by field_simp
  obtain ⟨z,hz⟩ := cauchySeq_tendsto_of_complete hc
  obtain ⟨hu,ha⟩ := GW.Analysis.partial_closed_limit A hA hm hin hz
  refine ⟨hu,?_⟩
  rw [ha]
  exact le_of_tendsto_of_tendsto hz.norm (hout.norm.const_mul C) (Eventually.of_forall hb)


lemma frankSchlein_productUnitary_sections
    {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (u : Lp (Lp E 2 ν) 2 μ) (v : Lp E 2 (μ.prod ν))
    (hs : ∀ᵐ x ∂μ, (fun y => u x y) =ᵐ[ν] (fun y => v (x,y))) :
    productUnitary μ ν u = v := by
  let U := productUnitary (E := E) μ ν
  have hp (η : Lp ℂ 2 μ) (e : Lp E 2 ν) :
      ⟪tensorEmbedding μ η e,u⟫_ℂ = ⟪productFunction μ ν η e,v⟫_ℂ := by
    have hi : Integrable (fun p : X × Y => ⟪η p.1 • e p.2,v p⟫_ℂ) (μ.prod ν) := by
      apply (L2.integrable_inner (𝕜 := ℂ) (productFunction μ ν η e) v).congr
      filter_upwards [productFunction_ae μ ν η e] with p hp
      rw [hp]
    calc
      _ = ∫ x, ⟪η x • e,u x⟫_ℂ ∂μ := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [tensorEmbedding_ae μ η e] with x hx
        rw [hx]
      _ = ∫ x, ∫ y, ⟪η x • e y,v (x,y)⟫_ℂ ∂ν ∂μ := by
        apply integral_congr_ae
        filter_upwards [hs] with x hx
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul (η x) e,hx] with y hy hz
        simp only [Pi.smul_apply] at hy
        rw [hy,hz]
      _ = ∫ p : X × Y, ⟪η p.1 • e p.2,v p⟫_ℂ ∂(μ.prod ν) := (integral_prod _ hi).symm
      _ = _ := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [productFunction_ae μ ν η e] with p hp
        rw [hp]
  have ht (η : Lp ℂ 2 μ) (e : Lp E 2 ν) : ⟪tensorEmbedding μ η e,u-U.symm v⟫_ℂ = 0 := by
    have he := U.inner_map_map (tensorEmbedding μ η e) (U.symm v)
    rw [productUnitary_tensor,LinearIsometryEquiv.apply_symm_apply] at he
    rw [inner_sub_right]
    exact sub_eq_zero.mpr ((hp η e).trans he)
  have hall : ∀ t : Lp (Lp E 2 ν) 2 μ, ⟪t,u-U.symm v⟫_ℂ = 0 := by
    apply Lp.induction (by norm_num : (2:ℝ≥0∞) ≠ ∞) (fun t => ⟪t,u-U.symm v⟫_ℂ = 0)
    · intro e A hA hf
      let η := indicatorConstLp 2 hA hf.ne (1:ℂ)
      have he : tensorEmbedding μ η e = indicatorConstLp 2 hA hf.ne e := by
        rw [tensorEmbedding_apply]
        simpa [η] using compLp_indicatorConst μ hA hf.ne (ContinuousLinearMap.toSpanSingleton ℂ e) 1
      rw [Lp.simpleFunc.coe_indicatorConst]
      simpa only [he] using ht η e
    · intro f g hf hg hd h₁ h₂
      rw [inner_add_left,h₁,h₂,add_zero]
    · exact isClosed_eq (continuous_id.inner continuous_const) continuous_const
  have he : u = U.symm v := sub_eq_zero.mp (inner_self_eq_zero.mp (hall (u-U.symm v)))
  exact (congrArg U he).trans (U.apply_symm_apply v)


lemma frankSchlein_swap_involutive
    {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (v : Lp E 2 (μ.prod ν)) : swapProduct ν μ (swapProduct μ ν v) = v := by
  apply Lp.ext
  filter_upwards [swapProduct_ae ν μ (swapProduct μ ν v),
    (Measure.measurePreserving_swap (μ := μ) (ν := ν)).quasiMeasurePreserving.ae
      (swapProduct_ae μ ν v)] with p hp hq
  exact hp.trans (by simpa only [Prod.swap_swap] using hq)

lemma frankSchlein_phaseKernel_Bochner (f : OneBoson) (u : ElectronL2) :
    phaseMultiplicationKernel f u = frankSchleinPhaseBochner f u := by
  let μ : Measure GW.Space := volume
  let P := kernelProductClass (phaseKernelRep f) (phaseKernelRep_measurable f) (phaseKernelRep_bound f) u
  let v := swapProduct μ μ P
  have hv : v =ᵐ[μ.prod μ] (fun p => GW.Analysis.physicalPhase p.1 p.2 * f p.1 * u p.2) := by
    filter_upwards [swapProduct_ae μ μ P,
      (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
        (kernelProductClass_ae (phaseKernelRep f) (phaseKernelRep_measurable f) (phaseKernelRep_bound f) u)] with p hp hq
    exact hp.trans hq
  have hs : ∀ᵐ k ∂μ, (fun x => frankSchleinPhaseBochner f u k x) =ᵐ[μ] (fun x => v (k,x)) := by
    filter_upwards [frankSchleinPhaseBochner_ae f u,Measure.ae_ae_of_ae_prod hv] with k hk hvk
    rw [hk,frankSchlein_phaseAt_modulation]
    filter_upwards [Lp.coeFn_smul (f k) (GW.Analysis.modulation k u),
      GW.Analysis.modulation_ae k u,hvk] with x h₁ h₂ h₃
    simp only [Pi.smul_apply] at h₁ h₂
    rw [h₁,h₂,h₃]
    simp only [smul_eq_mul]
    ring
  have hU := frankSchlein_productUnitary_sections μ μ (frankSchleinPhaseBochner f u) v hs
  apply kernelProductIdentification.injective
  change kernelProductIdentification (multiplicationKernel (phaseKernelRep f) (phaseKernelRep_measurable f)
    (norm_nonneg f) (phaseKernelRep_bound f) u) = _
  rw [multiplicationKernel_product]
  change P = swapProduct μ μ (productUnitary μ μ (frankSchleinPhaseBochner f u))
  rw [hU]
  exact (frankSchlein_swap_involutive μ μ P).symm


lemma frankSchlein_phaseKernel_fourier (f : OneBoson) (u : ElectronL2) :
    kernelProductIdentification
      (amplify (volume : Measure GW.Space)
        GW.Analysis.physicalFourierUnitary.toContinuousLinearEquiv.toContinuousLinearMap
        (phaseMultiplicationKernel f u)) = frankSchleinShearedFourier f u := by
  let μ : Measure GW.Space := volume
  let T : ElectronL2 →L[ℂ] ElectronL2 :=
    GW.Analysis.physicalFourierUnitary.toContinuousLinearEquiv.toContinuousLinearMap
  let z := amplify μ T (phaseMultiplicationKernel f u)
  let v := swapProduct μ μ (frankSchleinShearedFourier f u)
  have hz : z =ᵐ[μ] (fun k => f k • GW.Analysis.translation (-k) (GW.Analysis.physicalFourierUnitary u)) := by
    dsimp [z]
    rw [frankSchlein_phaseKernel_Bochner]
    filter_upwards [amplify_ae μ T (frankSchleinPhaseBochner f u),frankSchleinPhaseBochner_ae f u] with k hk hp
    rw [hk,hp]
    change GW.Analysis.physicalFourierUnitary (f k • GW.Analysis.phaseAt u k) = _
    rw [map_smul,frankSchlein_phaseAt_modulation,GW.Analysis.physicalFourier_modulation]
  have hv : v =ᵐ[μ.prod μ] (fun p => f p.1 * GW.Analysis.physicalFourierUnitary u (p.2+p.1)) := by
    filter_upwards [swapProduct_ae μ μ (frankSchleinShearedFourier f u),
      (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
        (frankSchleinShearedFourier_ae f u)] with p hp hq
    exact hp.trans hq
  have hs : ∀ᵐ k ∂μ, (fun q => z k q) =ᵐ[μ] (fun q => v (k,q)) := by
    filter_upwards [hz,Measure.ae_ae_of_ae_prod hv] with k hk hvk
    rw [hk]
    filter_upwards [Lp.coeFn_smul (f k) (GW.Analysis.translation (-k) (GW.Analysis.physicalFourierUnitary u)),
      GW.Analysis.translation_ae (-k) (GW.Analysis.physicalFourierUnitary u),hvk] with q h₁ h₂ h₃
    simp only [Pi.smul_apply,sub_neg_eq_add] at h₁ h₂
    rw [h₁,h₂,h₃]
    rfl
  have hU := frankSchlein_productUnitary_sections μ μ z v hs
  change swapProduct μ μ (productUnitary μ μ z) = frankSchleinShearedFourier f u
  rw [hU]
  exact frankSchlein_swap_involutive μ μ _

lemma frankSchleinInverseSymbol_sq (q : GW.Space) :
    ‖frankSchleinInverseSymbol q‖^2 = (1+‖q‖^2)⁻¹ := by
  unfold frankSchleinInverseSymbol frankSchleinElectronWeight
  rw [Complex.norm_real,Real.norm_eq_abs,sq_abs,inv_pow,
    Real.sq_sqrt (by positivity : 0 ≤ 1+‖q‖^2)]

def frankSchleinShiftedKernel (f : OneBoson) (p : GW.Space × GW.Space) : ℂ :=
  frankSchleinInverseSymbol (p.1-p.2) * f p.2

lemma frankSchleinShiftedKernel_measurable (f : OneBoson) :
    Measurable (frankSchleinShiftedKernel f) :=
  (frankSchleinInverseSymbol_continuous.measurable.comp
    (measurable_fst.sub measurable_snd)).mul ((Lp.stronglyMeasurable f).measurable.comp measurable_snd)

lemma frankSchleinShiftedKernel_section (f : OneBoson) (q : GW.Space) :
    kernelSectionSq (frankSchleinShiftedKernel f) q = ENNReal.ofReal (frankSchleinIntegral f q) := by
  unfold kernelSectionSq
  have he (k : GW.Space) : ‖frankSchleinShiftedKernel f (q,k)‖^2 = frankSchleinIntegrand f q k := by
    simp only [frankSchleinShiftedKernel,norm_mul,mul_pow,frankSchleinInverseSymbol_sq,
      frankSchleinIntegrand,div_eq_mul_inv]
    ring
  simp_rw [he]
  exact (ofReal_integral_eq_lintegral_ofReal (frankSchleinIntegrand_integrable f q)
    (Eventually.of_forall (frankSchleinIntegrand_nonneg f q))).symm

lemma frankSchleinShiftedKernel_bound (f : OneBoson) :
    ∀ᵐ q ∂(volume : Measure GW.Space), kernelSectionSq (frankSchleinShiftedKernel f) q ≤
      ENNReal.ofReal (frankSchleinConstant f ^ 2) :=
  Eventually.of_forall (fun q => by
    rw [frankSchleinShiftedKernel_section]
    exact ENNReal.ofReal_le_ofReal (frankSchleinIntegral_le_constant_sq f q))

/-- The translated product class in the source Tonelli estimate. Its equality
with the Fourier transform of the actual regularized kernel is proved separately. -/
def frankSchleinWeightedShear (f : OneBoson) (u : ElectronL2) : ElectronBosonProduct :=
  GW.Analysis.productShearL2 volume (fun k : GW.Space => k) measurable_id
    (kernelProductClass (frankSchleinShiftedKernel f) (frankSchleinShiftedKernel_measurable f)
      (frankSchleinShiftedKernel_bound f) (GW.Analysis.physicalFourierUnitary u))

lemma frankSchleinWeightedShear_norm (f : OneBoson) (u : ElectronL2) :
    ‖frankSchleinWeightedShear f u‖ ≤ frankSchleinConstant f * ‖u‖ := by
  unfold frankSchleinWeightedShear
  rw [LinearIsometryEquiv.norm_map]
  simpa only [LinearIsometryEquiv.norm_map] using
    kernelProductClass_norm (frankSchleinShiftedKernel f) (frankSchleinShiftedKernel_measurable f)
      (frankSchleinConstant_nonneg f) (frankSchleinShiftedKernel_bound f)
      (GW.Analysis.physicalFourierUnitary u)

lemma frankSchleinWeightedShear_ae (f : OneBoson) (u : ElectronL2) :
    frankSchleinWeightedShear f u =ᵐ[(volume : Measure GW.Space).prod volume]
      (fun p => frankSchleinInverseSymbol p.1 * f p.2 *
        GW.Analysis.physicalFourierUnitary u (p.1+p.2)) := by
  filter_upwards [GW.Analysis.productShearL2_ae volume (fun k : GW.Space => k) measurable_id
      (kernelProductClass (frankSchleinShiftedKernel f) (frankSchleinShiftedKernel_measurable f)
        (frankSchleinShiftedKernel_bound f) (GW.Analysis.physicalFourierUnitary u)),
    (GW.Analysis.productShear_preserving volume (fun k : GW.Space => k) measurable_id).quasiMeasurePreserving.ae
      (kernelProductClass_ae (frankSchleinShiftedKernel f) (frankSchleinShiftedKernel_measurable f)
        (frankSchleinShiftedKernel_bound f) (GW.Analysis.physicalFourierUnitary u))] with p hp hq
  exact hp.trans (by simpa [GW.Analysis.productShear,kernelRep,frankSchleinShiftedKernel] using hq)

lemma frankSchleinRegularizedKernel_fourier (f : OneBoson) (u : ElectronL2) :
    kernelProductIdentification
      (amplify (volume : Measure GW.Space)
        GW.Analysis.physicalFourierUnitary.toContinuousLinearEquiv.toContinuousLinearMap
        (frankSchleinRegularizedKernel f u)) = frankSchleinWeightedShear f u := by
  let μ : Measure GW.Space := volume
  let T : ElectronL2 →L[ℂ] ElectronL2 :=
    GW.Analysis.physicalFourierUnitary.toContinuousLinearEquiv.toContinuousLinearMap
  let F := phaseMultiplicationKernel f u
  let B := frankSchleinRegularizedKernel f u
  let z := amplify μ T B
  let v := swapProduct μ μ (frankSchleinWeightedShear f u)
  have hB : B =ᵐ[μ] (fun k => frankSchleinElectronInverse (F k)) :=
    amplify_ae μ frankSchleinElectronInverse F
  have hF : F =ᵐ[μ] (fun k => f k • GW.Analysis.phaseAt u k) := by
    simpa only [F,frankSchlein_phaseKernel_Bochner] using frankSchleinPhaseBochner_ae f u
  have hz : z =ᵐ[μ] (fun k => frankSchleinInverseFourier
      (f k • GW.Analysis.translation (-k) (GW.Analysis.physicalFourierUnitary u))) := by
    filter_upwards [amplify_ae μ T B,hB,
      hF] with k hk hb hf
    rw [hk,hb]
    change GW.Analysis.physicalFourierUnitary
      (GW.Analysis.physicalFourierUnitary.symm
        (frankSchleinInverseFourier (GW.Analysis.physicalFourierUnitary (F k)))) = _
    rw [LinearIsometryEquiv.apply_symm_apply]
    change F k = _ at hf
    rw [hf,map_smul,frankSchlein_phaseAt_modulation,GW.Analysis.physicalFourier_modulation]
  have hv : v =ᵐ[μ.prod μ] (fun p => frankSchleinInverseSymbol p.2 * f p.1 *
      GW.Analysis.physicalFourierUnitary u (p.2+p.1)) := by
    filter_upwards [swapProduct_ae μ μ (frankSchleinWeightedShear f u),
      (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
        (frankSchleinWeightedShear_ae f u)] with p hp hq
    exact hp.trans hq
  have hs : ∀ᵐ k ∂μ, (fun q => z k q) =ᵐ[μ] (fun q => v (k,q)) := by
    filter_upwards [hz,Measure.ae_ae_of_ae_prod hv] with k hk hvk
    rw [hk]
    let a := f k • GW.Analysis.translation (-k) (GW.Analysis.physicalFourierUnitary u)
    filter_upwards [GW.Analysis.boundedMultiplier_ae frankSchleinInverseSymbol
        frankSchleinInverseSymbol_continuous.measurable
        (C := 1) (Eventually.of_forall frankSchleinInverseSymbol_bound) a,
      Lp.coeFn_smul (f k) (GW.Analysis.translation (-k) (GW.Analysis.physicalFourierUnitary u)),
      GW.Analysis.translation_ae (-k) (GW.Analysis.physicalFourierUnitary u),hvk] with q h₀ h₁ h₂ h₃
    change frankSchleinInverseSymbol q • a q = frankSchleinInverseFourier a q at h₀
    simp only [Pi.smul_apply,sub_neg_eq_add] at h₁ h₂
    rw [← h₀,h₃]
    change frankSchleinInverseSymbol q * a q = _
    dsimp only [a]
    rw [h₁,h₂]
    simp only [smul_eq_mul]
    ring
  have hU := frankSchlein_productUnitary_sections μ μ z v hs
  change swapProduct μ μ (productUnitary μ μ z) = frankSchleinWeightedShear f u
  rw [hU]
  exact frankSchlein_swap_involutive μ μ _

lemma frankSchlein_amplified_fourier_norm
    (v : Lp ElectronL2 2 (volume : Measure GW.Space)) :
    ‖amplify (volume : Measure GW.Space)
      GW.Analysis.physicalFourierUnitary.toContinuousLinearEquiv.toContinuousLinearMap v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [GW.Analysis.l2_norm_sq (𝕜 := ℂ),GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
  apply integral_congr_ae
  filter_upwards [amplify_ae (volume : Measure GW.Space)
    GW.Analysis.physicalFourierUnitary.toContinuousLinearEquiv.toContinuousLinearMap v] with k hk
  rw [hk]
  exact congrArg (fun t : ℝ => t^2) (GW.Analysis.physicalFourierUnitary.norm_map (v k))

lemma frankSchleinRegularizedKernel_norm (f : OneBoson) (u : ElectronL2) :
    ‖frankSchleinRegularizedKernel f u‖ ≤ frankSchleinConstant f * ‖u‖ := by
  have he := congrArg norm (frankSchleinRegularizedKernel_fourier f u)
  rw [LinearIsometryEquiv.norm_map,frankSchlein_amplified_fourier_norm] at he
  rw [he]
  exact frankSchleinWeightedShear_norm f u

lemma frankSchleinRegularizedKernel_opNorm (f : OneBoson) :
    ‖frankSchleinRegularizedKernel f‖ ≤ frankSchleinConstant f :=
  ContinuousLinearMap.opNorm_le_bound _ (frankSchleinConstant_nonneg f)
    (frankSchleinRegularizedKernel_norm f)

/- Source argument component Tail04. -/
lemma frankSchlein_swap_natural
    {X Y E G : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (T : E →L[ℂ] G) (u : Lp E 2 (μ.prod ν)) :
    swapProduct μ ν (amplify (μ.prod ν) T u) =
      amplify (ν.prod μ) T (swapProduct μ ν u) := by
  apply Lp.ext
  filter_upwards [swapProduct_ae μ ν (amplify (μ.prod ν) T u),
    (Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae
      (amplify_ae (μ.prod ν) T u),
    amplify_ae (ν.prod μ) T (swapProduct μ ν u),swapProduct_ae μ ν u] with p h₁ h₂ h₃ h₄
  rw [h₁,h₂,h₃,h₄]

lemma frankSchlein_kernelSplit_natural
    {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (T : E →L[ℂ] G) (n : ℕ) (u : KernelSector E (n+1)) :
    kernelSplit n (amplify (sectorMeasure (n+1)) T u) =
      amplify (sectorMeasure n) (amplify (volume : Measure GW.Space) T) (kernelSplit n u) := by
  let v := vectorPullback (splitCoordinates n 0).symm (splitCoordinates_inverse_preserving n 0) u
  have hb : productUnitary (sectorMeasure n) volume (kernelSplit n u) =
      swapProduct volume (sectorMeasure n) v :=
    (productUnitary (sectorMeasure n) volume).apply_symm_apply _
  have hl : productUnitary (sectorMeasure n) volume
      (kernelSplit n (amplify (sectorMeasure (n+1)) T u)) =
      swapProduct volume (sectorMeasure n)
        (vectorPullback (splitCoordinates n 0).symm (splitCoordinates_inverse_preserving n 0)
          (amplify (sectorMeasure (n+1)) T u)) :=
    (productUnitary (sectorMeasure n) volume).apply_symm_apply _
  apply (productUnitary (sectorMeasure n) volume).injective
  exact hl.trans ((congrArg (swapProduct volume (sectorMeasure n))
    (vectorPullback_amplify (splitCoordinates n 0).symm
      (splitCoordinates_inverse_preserving n 0) T u)).trans
    ((frankSchlein_swap_natural volume (sectorMeasure n) T v).trans
      ((congrArg (amplify ((sectorMeasure n).prod volume) T) hb.symm).trans
        (productUnitary_natural (sectorMeasure n) volume T (kernelSplit n u)).symm)))

lemma frankSchlein_amplify_comp
    {X E G H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (μ : Measure X) (S : G →L[ℂ] H) (T : E →L[ℂ] G) (u : Lp E 2 μ) :
    amplify μ (S.comp T) u = amplify μ S (amplify μ T u) := by
  apply Lp.ext
  filter_upwards [amplify_ae μ (S.comp T) u,amplify_ae μ S (amplify μ T u),
    amplify_ae μ T u] with x h₁ h₂ h₃
  rw [h₁,h₂,h₃]
  rfl

/-- The inverse electron map acts before F*, exactly as in the source. -/
lemma frankSchlein_kernelAnnihilation_factor
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (F : BosonKernel E) (T : E →L[ℂ] E) (n : ℕ) (u : KernelSector E (n+1)) :
    kernelAnnihilationRaw ((amplify volume T).comp F) n u =
      kernelAnnihilationRaw F n (amplify (sectorMeasure (n+1)) T.adjoint u) := by
  change amplify (sectorMeasure n) (((amplify volume T).comp F).adjoint) (kernelSplit n u) = _
  rw [ContinuousLinearMap.adjoint_comp,amplify_adjoint,frankSchlein_amplify_comp]
  exact congrArg (amplify (sectorMeasure n) F.adjoint)
    (frankSchlein_kernelSplit_natural T.adjoint n u).symm

def frankSchleinElectronOperator : ElectronL2 →ₗ.[ℂ] ElectronL2 :=
  GW.Analysis.fourierMultiplier frankSchleinElectronWeight

lemma frankSchleinInverseFourier_cancel
    (u : (GW.Analysis.realMultiplier frankSchleinElectronWeight (volume : Measure GW.Space)).domain) :
    frankSchleinInverseFourier (GW.Analysis.realMultiplier frankSchleinElectronWeight volume u) = u.val := by
  apply Lp.ext
  filter_upwards [GW.Analysis.boundedMultiplier_ae frankSchleinInverseSymbol
      frankSchleinInverseSymbol_continuous.measurable
      (C := 1) (Eventually.of_forall frankSchleinInverseSymbol_bound)
      (GW.Analysis.realMultiplier frankSchleinElectronWeight volume u),
    GW.Analysis.realMultiplier_ae frankSchleinElectronWeight u] with q h₁ h₂
  change frankSchleinInverseSymbol q • (GW.Analysis.realMultiplier frankSchleinElectronWeight volume u q) =
    frankSchleinInverseFourier (GW.Analysis.realMultiplier frankSchleinElectronWeight volume u) q at h₁
  rw [← h₁,← h₂,smul_smul]
  have hw : frankSchleinElectronWeight q ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (frankSchleinElectronWeight_one q))
  have hc : frankSchleinInverseSymbol q * (frankSchleinElectronWeight q : ℂ) = 1 := by
    unfold frankSchleinInverseSymbol
    rw [← Complex.ofReal_mul,inv_mul_cancel₀ hw,Complex.ofReal_one]
  rw [hc,one_smul]

lemma frankSchleinElectronInverse_cancel (u : frankSchleinElectronOperator.domain) :
    frankSchleinElectronInverse (frankSchleinElectronOperator u) = u.val := by
  let v : (GW.Analysis.fourierMultiplier frankSchleinElectronWeight).domain := ⟨u.val,u.property⟩
  have hv : frankSchleinElectronOperator u = GW.Analysis.fourierMultiplier frankSchleinElectronWeight v := rfl
  rw [hv]
  apply GW.Analysis.physicalFourierUnitary.injective
  dsimp only [frankSchleinElectronInverse,ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,ContinuousLinearEquiv.coe_coe]
  rw [LinearIsometryEquiv.apply_symm_apply,GW.Analysis.fourierMultiplier_action]
  exact frankSchleinInverseFourier_cancel _

lemma frankSchlein_amplify_fixed
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (n : ℕ) (u : kernelFixed (E := E) n) :
    amplify (sectorMeasure n) T u.val ∈ kernelFixed n := by
  apply (mem_kernelFixed n _).mpr
  intro τ
  have hp := vectorPullback_amplify (coordinatePermutation n τ)
    (coordinatePermutation_preserving n τ) T u.val
  change kernelPermutation n τ (amplify (sectorMeasure n) T u.val) =
    amplify (sectorMeasure n) T (kernelPermutation n τ u.val) at hp
  exact hp.trans (congrArg (amplify (sectorMeasure n) T) ((mem_kernelFixed n u.val).mp u.property τ))

def frankSchleinFixedAmplify
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (n : ℕ) : kernelFixed (E := E) n →L[ℂ] kernelFixed (E := E) n :=
  (((amplify (sectorMeasure n) T).comp (kernelFixedInclusion n).toContinuousLinearMap).codRestrict
    (kernelFixed n).toSubmodule (frankSchlein_amplify_fixed T n))

lemma frankSchlein_kernelAnnihilation_fixed_factor
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (F : BosonKernel E) (T : E →L[ℂ] E) (n : ℕ) (u : kernelFixed (E := E) (n+1)) :
    kernelAnnihilation ((amplify volume T).comp F) n u =
      kernelAnnihilation F n (frankSchleinFixedAmplify T.adjoint (n+1) u) := by
  apply Subtype.ext
  simp only [kernelAnnihilation_value]
  rw [frankSchlein_kernelAnnihilation_factor]
  rfl

lemma frankSchleinRegularizedKernel_sector_factor (f : OneBoson) (n : ℕ)
    (u : ElectronSector (n+1)) :
    generalizedAnnihilationSector (frankSchleinRegularizedKernel f) n u =
      generalizedAnnihilationSector (phaseMultiplicationKernel f) n
        ((physicalSectorKernel (n+1)).symm
          (frankSchleinFixedAmplify frankSchleinElectronInverse (n+1) (physicalSectorKernel (n+1) u))) := by
  have h := frankSchlein_kernelAnnihilation_fixed_factor
    (phaseMultiplicationKernel f) frankSchleinElectronInverse n (physicalSectorKernel (n+1) u)
  have hself := congrArg (fun T : ElectronL2 →L[ℂ] ElectronL2 =>
    kernelAnnihilation (phaseMultiplicationKernel f) n
      (frankSchleinFixedAmplify T (n+1) (physicalSectorKernel (n+1) u)))
    frankSchleinElectronInverse_adjoint
  have hc := congrArg (physicalSectorKernel n).symm (h.trans hself)
  have hi := (physicalSectorKernel (n+1)).apply_symm_apply
    (frankSchleinFixedAmplify frankSchleinElectronInverse (n+1) (physicalSectorKernel (n+1) u))
  exact hc.trans (congrArg (fun z => (physicalSectorKernel n).symm
    (kernelAnnihilation (phaseMultiplicationKernel f) n z)) hi.symm)

/- Source argument component Physical04. -/
def frankSchleinVectorInverseFourier (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] : Lp E 2 (volume : Measure GW.Space) →L[ℂ] Lp E 2 (volume : Measure GW.Space) :=
  GW.Analysis.boundedMultiplier frankSchleinInverseSymbol frankSchleinInverseSymbol_continuous.measurable
    (C := 1) (Eventually.of_forall frankSchleinInverseSymbol_bound)

def frankSchleinVectorInverse (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] : Lp E 2 (volume : Measure GW.Space) →L[ℂ] Lp E 2 (volume : Measure GW.Space) :=
  GW.Analysis.physicalFourierUnitary.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((frankSchleinVectorInverseFourier E).comp
      GW.Analysis.physicalFourierUnitary.toContinuousLinearEquiv.toContinuousLinearMap)

lemma frankSchleinVectorInverseFourier_tensor {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (γ : ElectronL2) (v : E) :
    frankSchleinVectorInverseFourier E ((ContinuousLinearMap.toSpanSingleton ℂ v).compLp γ) =
      (ContinuousLinearMap.toSpanSingleton ℂ v).compLp (frankSchleinInverseFourier γ) := by
  apply Lp.ext
  filter_upwards [GW.Analysis.boundedMultiplier_ae frankSchleinInverseSymbol
      frankSchleinInverseSymbol_continuous.measurable
      (C := 1) (Eventually.of_forall frankSchleinInverseSymbol_bound)
      ((ContinuousLinearMap.toSpanSingleton ℂ v).compLp γ),
    GW.Analysis.boundedMultiplier_ae frankSchleinInverseSymbol
      frankSchleinInverseSymbol_continuous.measurable
      (C := 1) (Eventually.of_forall frankSchleinInverseSymbol_bound) γ,
    (ContinuousLinearMap.toSpanSingleton ℂ v).coeFn_compLp γ,
    (ContinuousLinearMap.toSpanSingleton ℂ v).coeFn_compLp (frankSchleinInverseFourier γ)] with q h₁ h₂ h₃ h₄
  change frankSchleinInverseSymbol q • _ = frankSchleinVectorInverseFourier E _ q at h₁
  change frankSchleinInverseSymbol q • γ q = frankSchleinInverseFourier γ q at h₂
  rw [← h₁,h₃,h₄,← h₂]
  exact smul_smul _ _ _

lemma frankSchleinVectorInverse_tensor {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (γ : ElectronL2) (v : E) :
    frankSchleinVectorInverse E ((ContinuousLinearMap.toSpanSingleton ℂ v).compLp γ) =
      (ContinuousLinearMap.toSpanSingleton ℂ v).compLp (frankSchleinElectronInverse γ) := by
  apply GW.Analysis.physicalFourierUnitary.injective
  change GW.Analysis.physicalFourierUnitary
    (GW.Analysis.physicalFourierUnitary.symm
      (frankSchleinVectorInverseFourier E (GW.Analysis.physicalFourierUnitary _))) = _
  rw [LinearIsometryEquiv.apply_symm_apply,smoothProduct_fourier_postcomp,
    frankSchleinVectorInverseFourier_tensor,smoothProduct_fourier_postcomp]
  congr 1
  exact (GW.Analysis.physicalFourierUnitary.apply_symm_apply _).symm

lemma frankSchleinPhysicalInverse_tensor (n : ℕ) (γ : ElectronL2) (v : Sector n) :
    physicalSectorKernel n
      (frankSchleinVectorInverse (Sector n) ((ContinuousLinearMap.toSpanSingleton ℂ v).compLp γ)) =
    frankSchleinFixedAmplify frankSchleinElectronInverse n
      (physicalSectorKernel n ((ContinuousLinearMap.toSpanSingleton ℂ v).compLp γ)) := by
  apply Subtype.ext
  have hl := congrArg (fun z : ElectronSector n => (physicalSectorKernel n z : KernelSector ElectronL2 n))
    (frankSchleinVectorInverse_tensor γ v)
  have hnew := fiberPhysicalSectorKernel_tensor n (frankSchleinElectronInverse γ) v
  have hold := congrArg (amplify (sectorMeasure n) frankSchleinElectronInverse)
    (fiberPhysicalSectorKernel_tensor n γ v)
  exact hl.trans (hnew.trans ((amplify_tensor (sectorMeasure n) frankSchleinElectronInverse
    ((ordinarySectorKernel n v : kernelFixed (E := ℂ) n) : AmbientSector n) γ).symm.trans hold.symm))

lemma frankSchleinPhysicalInverse (n : ℕ) (u : ElectronSector n) :
    physicalSectorKernel n (frankSchleinVectorInverse (Sector n) u) =
      frankSchleinFixedAmplify frankSchleinElectronInverse n (physicalSectorKernel n u) := by
  let A := (physicalSectorKernel n).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (frankSchleinVectorInverse (Sector n))
  let B := (frankSchleinFixedAmplify frankSchleinElectronInverse n).comp
    (physicalSectorKernel n).toContinuousLinearEquiv.toContinuousLinearMap
  change A u = B u
  apply Lp.induction (p := 2) (μ := (volume : Measure GW.Space)) (by norm_num)
    (fun u => A u = B u) ?_ ?_ (isClosed_eq A.continuous B.continuous) u
  · intro v S hS hfinite
    have h := frankSchleinPhysicalInverse_tensor n (indicatorConstLp 2 hS hfinite.ne (1 : ℂ)) v
    simpa only [A,B,ContinuousLinearMap.comp_apply,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv,ContinuousLinearEquiv.coe_coe,
      compLp_indicatorConst,ContinuousLinearMap.toSpanSingleton_apply,one_smul,
      Lp.simpleFunc.coe_indicatorConst] using h
  · intro f g hfm hgm _ hf hg
    exact (A.map_add (hfm.toLp f) (hgm.toLp g)).trans
      ((congrArg₂ (fun x y => x+y) hf hg).trans (B.map_add (hfm.toLp f) (hgm.toLp g)).symm)

lemma frankSchleinVectorInverse_cancel {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (u : (GW.Analysis.fourierMultiplier (H := E) frankSchleinElectronWeight).domain) :
    frankSchleinVectorInverse E (GW.Analysis.fourierMultiplier frankSchleinElectronWeight u) = u.val := by
  apply GW.Analysis.physicalFourierUnitary.injective
  dsimp only [frankSchleinVectorInverse,ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,ContinuousLinearEquiv.coe_coe]
  rw [LinearIsometryEquiv.apply_symm_apply,GW.Analysis.fourierMultiplier_action]
  apply Lp.ext
  filter_upwards [GW.Analysis.boundedMultiplier_ae frankSchleinInverseSymbol
      frankSchleinInverseSymbol_continuous.measurable
      (C := 1) (Eventually.of_forall frankSchleinInverseSymbol_bound)
      (GW.Analysis.realMultiplier frankSchleinElectronWeight volume
        ⟨GW.Analysis.physicalFourierUnitary u.val,u.property⟩),
    GW.Analysis.realMultiplier_ae frankSchleinElectronWeight
      (⟨GW.Analysis.physicalFourierUnitary u.val,u.property⟩ :
        (GW.Analysis.realMultiplier (H := E) frankSchleinElectronWeight volume).domain)] with q h₁ h₂
  change frankSchleinInverseSymbol q • _ = frankSchleinVectorInverseFourier E _ q at h₁
  rw [← h₁,← h₂,smul_smul]
  have hw : frankSchleinElectronWeight q ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (frankSchleinElectronWeight_one q))
  have hc : frankSchleinInverseSymbol q * (frankSchleinElectronWeight q : ℂ) = 1 := by
    unfold frankSchleinInverseSymbol
    rw [← Complex.ofReal_mul,inv_mul_cancel₀ hw,Complex.ofReal_one]
  rw [hc,one_smul]

/- Source argument component Estimate03. -/
def frankSchleinPhysicalElectron : Physical →ₗ.[ℂ] Physical :=
  physicalSectorMultiplier (fun _ q => frankSchleinElectronWeight q)

lemma frankSchleinElectronWeight_measurable : Measurable frankSchleinElectronWeight :=
  Real.continuous_sqrt.measurable.comp (measurable_const.add (measurable_norm.pow_const 2))

lemma frankSchlein_H0_mem_electron (u : freeHamiltonian.domain) :
    u.val ∈ frankSchleinPhysicalElectron.domain := by
  let v : freeGraphOperator.domain := ⟨u.val,by rw [freeGraphOperator_domain];exact u.property⟩
  apply (physicalSectorMultiplier_domination (fun _ q => frankSchleinElectronWeight q)
    freeGraphWeight (fun _ => frankSchleinElectronWeight_measurable) (C := 1)
    (by norm_num) ?_ v).choose
  intro n q
  rw [one_mul,abs_of_nonneg (zero_le_one.trans (frankSchleinElectronWeight_one q)),
    abs_of_nonneg (zero_le_one.trans (freeGraphWeight_one n q))]
  have hs := Real.sq_sqrt (show 0 ≤ 1+‖q‖^2 by positivity)
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hw := frankSchleinElectronWeight_one q
  dsimp only [frankSchleinElectronWeight,freeGraphWeight,freeEnergySymbol] at *
  nlinarith [sq_nonneg ‖q‖]

lemma frankSchlein_electron_root (u : frankSchleinPhysicalElectron.domain)
    (hj : u.val ∈ frankSchleinJointOperator.domain) :
    ∃ hv : frankSchleinPhysicalElectron u ∈ (physicalNumberPower (1/2)).domain,
      physicalNumberPower (1/2) ⟨frankSchleinPhysicalElectron u,hv⟩ =
        frankSchleinJointOperator ⟨u.val,hj⟩ := by
  have hprod : u.val ∈ (physicalSectorMultiplier
      (fun n q => Real.sqrt (n : ℝ) * frankSchleinElectronWeight q)).domain := hj
  obtain ⟨hv,he⟩ := physicalSectorMultiplier_composition
    (fun _ q => frankSchleinElectronWeight q) (fun n _ => Real.sqrt (n : ℝ)) u.val u.property hprod
  let z := physicalSectorMultiplier (fun n _ => Real.sqrt (n : ℝ))
    ⟨frankSchleinPhysicalElectron u,hv⟩
  have hg : (frankSchleinPhysicalElectron u,z) ∈
      (physicalSectorMultiplier (fun n _ => Real.sqrt (n : ℝ))).graph :=
    (physicalSectorMultiplier (fun n _ => Real.sqrt (n : ℝ))).mem_graph
      ⟨frankSchleinPhysicalElectron u,hv⟩
  have hgN : (frankSchleinPhysicalElectron u,z) ∈ (physicalNumberPower (1/2)).graph :=
    (congrArg (fun T : Physical →ₗ.[ℂ] Physical => (frankSchleinPhysicalElectron u,z) ∈ T.graph)
      physicalNumberHalf_eq_sectorMultiplier).mpr hg
  have hm := (physicalNumberPower (1/2)).mem_domain_of_mem_graph hgN
  refine ⟨hm,?_⟩
  exact ((physicalNumberPower (1/2)).mem_graph_snd_inj
    ((physicalNumberPower (1/2)).mem_graph ⟨frankSchleinPhysicalElectron u,hm⟩) hgN rfl).trans he

lemma frankSchlein_joint_mem_root (u : frankSchleinJointOperator.domain) :
    u.val ∈ (physicalNumberPower (1/2)).domain := by
  rw [physicalNumberHalf_eq_sectorMultiplier]
  apply (physicalSectorMultiplier_domination (fun n _ => Real.sqrt (n : ℝ))
    mixedRootNumberSymbol (fun _ => measurable_const) (C := 1) (by norm_num) ?_ u).choose
  intro n q
  change |Real.sqrt (n : ℝ)| ≤ 1 * |Real.sqrt (n : ℝ) * frankSchleinElectronWeight q|
  rw [one_mul,abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (zero_le_one.trans (frankSchleinElectronWeight_one q)))]
  exact le_mul_of_one_le_right (Real.sqrt_nonneg _) (frankSchleinElectronWeight_one q)

lemma frankSchleinPhysicalInverse_cancel (u : frankSchleinPhysicalElectron.domain) (n : ℕ) :
    frankSchleinVectorInverse (Sector n)
      (electronBosonUnitary.symm (frankSchleinPhysicalElectron u) n) =
        electronBosonUnitary.symm u.val n := by
  apply GW.Analysis.physicalFourierUnitary.injective
  dsimp only [frankSchleinVectorInverse,ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,ContinuousLinearEquiv.coe_coe]
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply Lp.ext
  filter_upwards [GW.Analysis.boundedMultiplier_ae frankSchleinInverseSymbol
      frankSchleinInverseSymbol_continuous.measurable
      (C := 1) (Eventually.of_forall frankSchleinInverseSymbol_bound)
      (freeFourierRepresentation (frankSchleinPhysicalElectron u) n),
    physicalSectorMultiplier_action (fun _ q => frankSchleinElectronWeight q) u n] with q h₁ h₂
  change frankSchleinInverseSymbol q • _ = frankSchleinVectorInverseFourier (Sector n) _ q at h₁
  change (frankSchleinElectronWeight q : ℂ) • freeFourierRepresentation u.val n q =
    freeFourierRepresentation (frankSchleinPhysicalElectron u) n q at h₂
  change frankSchleinVectorInverseFourier (Sector n)
    (freeFourierRepresentation (frankSchleinPhysicalElectron u) n) q = freeFourierRepresentation u.val n q
  rw [← h₁,← h₂,smul_smul]
  have hw : frankSchleinElectronWeight q ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (frankSchleinElectronWeight_one q))
  have hc : frankSchleinInverseSymbol q * (frankSchleinElectronWeight q : ℂ) = 1 := by
    unfold frankSchleinInverseSymbol
    rw [← Complex.ofReal_mul,inv_mul_cancel₀ hw,Complex.ofReal_one]
  rw [hc,one_smul]

lemma frankSchlein_ordered_factor (f : OneBoson)
    (u : frankSchleinPhysicalElectron.domain)
    (hr : u.val ∈ (physicalNumberPower (1/2)).domain)
    (hlr : frankSchleinPhysicalElectron u ∈ (physicalNumberPower (1/2)).domain) :
    generalizedAnnihilation (phaseMultiplicationKernel f)
      ⟨u.val,generalizedAnnihilation_mem_root _ ⟨u.val,hr⟩⟩ =
    generalizedAnnihilation (frankSchleinRegularizedKernel f)
      ⟨frankSchleinPhysicalElectron u,generalizedAnnihilation_mem_root _
        ⟨frankSchleinPhysicalElectron u,hlr⟩⟩ := by
  apply electronBosonUnitary.symm.injective
  apply lp.ext
  funext n
  rw [generalizedAnnihilation_apply,generalizedAnnihilation_apply]
  have hi := frankSchleinPhysicalInverse (n+1)
    (electronBosonUnitary.symm (frankSchleinPhysicalElectron u) (n+1))
  have hs := congrArg (physicalSectorKernel (n+1)).symm hi
  have he := (physicalSectorKernel (n+1)).symm_apply_apply
    (frankSchleinVectorInverse (Sector (n+1))
      (electronBosonUnitary.symm (frankSchleinPhysicalElectron u) (n+1)))
  have hc := he.symm.trans hs
  have hz := (frankSchleinPhysicalInverse_cancel u (n+1)).symm.trans hc
  exact (congrArg (generalizedAnnihilationSector (phaseMultiplicationKernel f) n) hz).trans
    (frankSchleinRegularizedKernel_sector_factor f n
      (electronBosonUnitary.symm (frankSchleinPhysicalElectron u) (n+1))).symm

lemma frankSchlein_H0_bound (f : OneBoson) (u : freeHamiltonian.domain) :
    ∃ ha : u.val ∈ (generalizedAnnihilation (phaseMultiplicationKernel f)).domain,
      ‖generalizedAnnihilation (phaseMultiplicationKernel f) ⟨u.val,ha⟩‖ ≤
        frankSchleinConstant f *
          ‖frankSchleinJointOperator ⟨u.val,frankSchlein_H0_mem_joint u⟩‖ := by
  let j : frankSchleinJointOperator.domain := ⟨u.val,frankSchlein_H0_mem_joint u⟩
  let l : frankSchleinPhysicalElectron.domain := ⟨u.val,frankSchlein_H0_mem_electron u⟩
  have hr := frankSchlein_joint_mem_root j
  obtain ⟨hlr,he⟩ := frankSchlein_electron_root l j.property
  let a : (generalizedAnnihilation (phaseMultiplicationKernel f)).domain :=
    ⟨u.val,generalizedAnnihilation_mem_root _ ⟨u.val,hr⟩⟩
  let b : (generalizedAnnihilation (frankSchleinRegularizedKernel f)).domain :=
    ⟨frankSchleinPhysicalElectron l,generalizedAnnihilation_mem_root _
      ⟨frankSchleinPhysicalElectron l,hlr⟩⟩
  refine ⟨a.property,?_⟩
  have hf : generalizedAnnihilation (phaseMultiplicationKernel f) a =
      generalizedAnnihilation (frankSchleinRegularizedKernel f) b :=
    frankSchlein_ordered_factor f l hr hlr
  calc
    _ = ‖generalizedAnnihilation (frankSchleinRegularizedKernel f) b‖ := congrArg norm hf
    _ ≤ ‖frankSchleinRegularizedKernel f‖ *
        ‖physicalNumberPower (1/2) ⟨frankSchleinPhysicalElectron l,hlr⟩‖ :=
      generalizedAnnihilation_root_norm (frankSchleinRegularizedKernel f)
        ⟨frankSchleinPhysicalElectron l,hlr⟩
    _ ≤ frankSchleinConstant f *
        ‖physicalNumberPower (1/2) ⟨frankSchleinPhysicalElectron l,hlr⟩‖ :=
      mul_le_mul_of_nonneg_right (frankSchleinRegularizedKernel_opNorm f) (norm_nonneg _)
    _ = frankSchleinConstant f * ‖frankSchleinJointOperator j‖ := by rw [he]

/- Source argument component Closed01. -/
lemma frankSchlein_H0_bound_inputs (f : OneBoson) (u : freeHamiltonian.domain)
    (a : (generalizedAnnihilation (phaseMultiplicationKernel f)).domain)
    (j : frankSchleinJointOperator.domain) (ha : a.val = u.val) (hj : j.val = u.val) :
    ‖generalizedAnnihilation (phaseMultiplicationKernel f) a‖ ≤
      frankSchleinConstant f * ‖frankSchleinJointOperator j‖ := by
  obtain ⟨hm,hb⟩ := frankSchlein_H0_bound f u
  have heA : a = ⟨u.val,hm⟩ := Subtype.ext ha
  have heJ : j = ⟨u.val,frankSchlein_H0_mem_joint u⟩ := Subtype.ext hj
  exact (congrArg (fun z => ‖generalizedAnnihilation (phaseMultiplicationKernel f) z‖) heA).trans_le
    (hb.trans_eq (congrArg (fun z => frankSchleinConstant f * ‖frankSchleinJointOperator z‖) heJ).symm)

lemma frankSchlein_joint_bound (f : OneBoson) (u : frankSchleinJointOperator.domain) :
    ∃ ha : u.val ∈ (generalizedAnnihilation (phaseMultiplicationKernel f)).domain,
      ‖generalizedAnnihilation (phaseMultiplicationKernel f) ⟨u.val,ha⟩‖ ≤
        frankSchleinConstant f * ‖frankSchleinJointOperator u‖ := by
  let A := generalizedAnnihilation (phaseMultiplicationKernel f)
  let v := frankSchleinJointCutoff u
  let h0 (n : ℕ) : freeHamiltonian.domain := ⟨(v n).val,frankSchleinJointCutoff_mem_H0 u n⟩
  have hm (n : ℕ) : (v n).val ∈ A.domain := (frankSchlein_H0_bound f (h0 n)).choose
  let a (n : ℕ) : A.domain := ⟨(v n).val,hm n⟩
  have hb (n : ℕ) : ‖A (a n)‖ ≤ frankSchleinConstant f * ‖frankSchleinJointOperator (v n)‖ :=
    frankSchlein_H0_bound_inputs f (h0 n) (a n) (v n) rfl rfl
  have hd (n m : ℕ) : ‖A (a n)-A (a m)‖ ≤
      frankSchleinConstant f * ‖frankSchleinJointOperator (v n)-frankSchleinJointOperator (v m)‖ := by
    have hs := frankSchlein_H0_bound_inputs f (h0 n-h0 m) (a n-a m) (v n-v m) rfl rfl
    have hA := A.toFun.map_sub (a n) (a m)
    have hJ := frankSchleinJointOperator.toFun.map_sub (v n) (v m)
    exact (congrArg norm hA).symm.trans_le
      (hs.trans_eq (congrArg (fun z => frankSchleinConstant f * ‖z‖) hJ))
  exact frankSchlein_closed_bound_extension A frankSchleinJointOperator
    (generalizedAnnihilation_closed (phaseMultiplicationKernel f)) u v hm
    (frankSchleinJointCutoff_input_tendsto u) (frankSchleinJointCutoff_output_tendsto u)
    (frankSchleinConstant f) (frankSchleinConstant_nonneg f) hb hd

/- Source argument component Public01. -/
theorem frankSchlein (f : OneBoson) :
    0 ≤ frankSchleinConstant f ∧
    frankSchleinConstant f ^ 2 = sSup (Set.range (frankSchleinIntegral f)) ∧
    frankSchleinConstant f ≤ ‖f‖ ∧
    (∀ u : frankSchleinJointOperator.domain,
      ∃ ha : u.val ∈ (generalizedAnnihilation (phaseMultiplicationKernel f)).domain,
        ‖generalizedAnnihilation (phaseMultiplicationKernel f) ⟨u.val,ha⟩‖ ≤
          frankSchleinConstant f * ‖frankSchleinJointOperator u‖) ∧
    (∀ u : freeHamiltonian.domain,
      ∃ ha : u.val ∈ (generalizedAnnihilation (phaseMultiplicationKernel f)).domain,
        ‖generalizedAnnihilation (phaseMultiplicationKernel f) ⟨u.val,ha⟩‖ ≤
          frankSchleinConstant f *
            ‖frankSchleinJointOperator ⟨u.val,frankSchlein_H0_mem_joint u⟩‖) :=
  ⟨frankSchleinConstant_nonneg f,frankSchleinConstant_sq f,frankSchleinConstant_le f,
    frankSchlein_joint_bound f,frankSchlein_H0_bound f⟩

end GW.Fock
