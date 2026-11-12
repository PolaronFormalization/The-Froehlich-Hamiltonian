module
public import GW.Analysis.CutoffExtension
public import GW.Fock.FockFiberFields
public import GW.Fock.FockFrankSchlein
public import GW.Gross.MainFSInterface

/-! Source fock:convolution-use, manuscript5052–5115.
Original annihilation cutoff restrictions on the complete free graph carrier,
extended uniform convolution tail and unique full real operator norm limit. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Fock


/- Source argument component Maps02. -/
lemma convolutionGraphInput_value (u : FreeGraphDomain) :
    freeGraphDomainInclusion u = (freeGraphH0Input u).val := by
  simpa only [freeGraphH0Input] using freeGraphDomainInclusion_apply u

lemma convolutionAnnihilation_mem (f : OneBoson) (u : FreeGraphDomain) :
    freeGraphDomainInclusion u ∈ (generalizedAnnihilation (phaseMultiplicationKernel f)).domain :=
by
  rw [convolutionGraphInput_value]
  exact (frankSchlein_H0_bound f (freeGraphH0Input u)).choose

def convolutionAnnihilationRestriction (f : OneBoson) : FreeGraphDomain →ₗ[ℂ] Physical :=
  (generalizedAnnihilation (phaseMultiplicationKernel f)).toFun.comp
    (freeGraphDomainInclusion.toLinearMap.codRestrict
      (generalizedAnnihilation (phaseMultiplicationKernel f)).domain (convolutionAnnihilation_mem f))

lemma convolutionAnnihilation_graph (f : OneBoson) (u : FreeGraphDomain) :
    (freeGraphDomainInclusion u,convolutionAnnihilationRestriction f u) ∈
      (generalizedAnnihilation (phaseMultiplicationKernel f)).graph :=
  (generalizedAnnihilation (phaseMultiplicationKernel f)).mem_graph
    ⟨freeGraphDomainInclusion u,convolutionAnnihilation_mem f u⟩

lemma convolutionAnnihilation_norm (f : OneBoson) (u : FreeGraphDomain) :
    ‖convolutionAnnihilationRestriction f u‖ ≤ (1/2 : ℝ)*frankSchleinConstant f*‖u‖ := by
  obtain ⟨ha,hb,hc⟩ := GW.Gross.main_FS_interface f (freeGraphH0Input u)
  have hg := (generalizedAnnihilation (phaseMultiplicationKernel f)).mem_graph
    (⟨(freeGraphH0Input u).val,ha⟩ : (generalizedAnnihilation (phaseMultiplicationKernel f)).domain)
  have he := (generalizedAnnihilation (phaseMultiplicationKernel f)).mem_graph_snd_inj
    (convolutionAnnihilation_graph f u) hg (convolutionGraphInput_value u)
  have hn : ‖freeHamiltonian (freeGraphH0Input u)+(freeGraphH0Input u).val‖ = ‖u‖ :=
    (congrArg (fun v : Physical => ‖freeHamiltonian (freeGraphH0Input u)+v‖)
      (convolutionGraphInput_value u)).symm.trans (freeGraph_norm_identity u).symm
  exact (congrArg norm he).trans_le ((hb.trans hc).trans_eq
    (congrArg (fun x : ℝ => (1/2 : ℝ)*frankSchleinConstant f*x) hn))

def convolutionAnnihilationMap (f : OneBoson) : FreeGraphDomain →L[ℂ] Physical :=
  (convolutionAnnihilationRestriction f).mkContinuous ((1/2 : ℝ)*frankSchleinConstant f)
    (convolutionAnnihilation_norm f)

/- Source argument component Addition02. -/
lemma convolutionPhaseKernel_sub (f g : OneBoson) :
    phaseMultiplicationKernel (f-g) = phaseMultiplicationKernel f-phaseMultiplicationKernel g := by
  apply ContinuousLinearMap.ext
  intro γ
  change phaseMultiplicationKernel (f-g) γ = phaseMultiplicationKernel f γ-phaseMultiplicationKernel g γ
  rw [frankSchlein_phaseKernel_Bochner,frankSchlein_phaseKernel_Bochner,frankSchlein_phaseKernel_Bochner]
  apply Lp.ext
  filter_upwards [frankSchleinPhaseBochner_ae (f-g) γ,
    frankSchleinPhaseBochner_ae f γ,frankSchleinPhaseBochner_ae g γ,
    Lp.coeFn_sub f g,Lp.coeFn_sub (frankSchleinPhaseBochner f γ) (frankSchleinPhaseBochner g γ)] with k h₀ h₁ h₂ hfg hsub
  rw [h₀,hsub]
  simp only [Pi.sub_apply]
  rw [h₁,h₂,hfg]
  simp only [Pi.sub_apply]
  exact sub_smul _ _ _

lemma convolutionSectorAnnihilation_sub
    (F G : BosonKernel ElectronL2) (n : ℕ) (u : ElectronSector (n+1)) :
    generalizedAnnihilationSector (F-G) n u =
      generalizedAnnihilationSector F n u-generalizedAnnihilationSector G n u := by
  have h := fiberSectorAnnihilation_add physicalSectorKernel (F-G) G n u
  have he : (F-G)+G = F := sub_add_cancel F G
  exact eq_sub_iff_add_eq.mpr (h.symm.trans
    (congrArg (fun K : BosonKernel ElectronL2 => sectorAnnihilation physicalSectorKernel K n u) he))

lemma convolutionAnnihilation_component (f : OneBoson) (u : FreeGraphDomain) (n : ℕ) :
    electronBosonUnitary.symm (convolutionAnnihilationRestriction f u) n =
      generalizedAnnihilationSector (phaseMultiplicationKernel f) n
        (electronBosonUnitary.symm (freeGraphDomainInclusion u) (n+1)) :=
  generalizedAnnihilation_apply (phaseMultiplicationKernel f)
    ⟨freeGraphDomainInclusion u,convolutionAnnihilation_mem f u⟩ n

lemma convolutionAnnihilationMap_sub (f g : OneBoson) :
    convolutionAnnihilationMap (f-g) = convolutionAnnihilationMap f-convolutionAnnihilationMap g := by
  apply ContinuousLinearMap.ext
  intro u
  apply electronBosonUnitary.symm.injective
  apply lp.ext
  funext n
  have h₀ := convolutionAnnihilation_component (f-g) u n
  have h₁ := convolutionAnnihilation_component f u n
  have h₂ := convolutionAnnihilation_component g u n
  have hk := congrArg (fun K : BosonKernel ElectronL2 =>
      generalizedAnnihilationSector K n (electronBosonUnitary.symm (freeGraphDomainInclusion u) (n+1)))
    (convolutionPhaseKernel_sub f g)
  have hsector := convolutionSectorAnnihilation_sub (phaseMultiplicationKernel f) (phaseMultiplicationKernel g)
    n (electronBosonUnitary.symm (freeGraphDomainInclusion u) (n+1))
  have hout := congrArg (fun z : ElectronBosonSum => z n)
    (electronBosonUnitary.symm.map_sub (convolutionAnnihilationRestriction f u) (convolutionAnnihilationRestriction g u))
  exact h₀.trans (hk.trans (hsector.trans
    ((congrArg₂ (fun x y => x-y) h₁ h₂).symm.trans hout.symm)))

/- Source argument component Coefficient02. -/
/-- Exactly the measurable cutoff and extended uniform-tail hypotheses of source5052–5115. -/
structure ConvolutionTailData where
  coefficient : GW.Space → ℂ
  measurable : Measurable coefficient
  lowerCutoff : ℝ
  lowerCutoff_nonneg : 0 ≤ lowerCutoff
  cutoff_memLp : ∀ R : ℝ, lowerCutoff ≤ R →
    MemLp (({k : GW.Space | ‖k‖ ≤ R} : Set GW.Space).indicator coefficient) 2 (volume : Measure GW.Space)
  error : ℝ → ℝ
  error_nonneg : ∀ R : ℝ, lowerCutoff ≤ R → 0 ≤ error R
  error_tendsto : Tendsto error atTop (𝓝 0)
  tail_bound : ∀ R : ℝ, lowerCutoff ≤ R → ∀ q : GW.Space,
    (∫⁻ k : GW.Space in {k | R < ‖k‖}, ENNReal.ofReal (‖coefficient k‖^2/(1+‖q-k‖^2))) ≤
      ENNReal.ofReal (error R ^ 2)

def convolutionCutoff (d : ConvolutionTailData) (R : ℝ) : OneBoson :=
  (d.cutoff_memLp (max d.lowerCutoff R) (le_max_left _ _)).toLp
    (({k : GW.Space | ‖k‖ ≤ max d.lowerCutoff R} : Set GW.Space).indicator d.coefficient)

lemma convolutionCutoff_ae (d : ConvolutionTailData) (R : ℝ) (hR : d.lowerCutoff ≤ R) :
    (convolutionCutoff d R : GW.Space → ℂ) =ᵐ[volume]
      (({k : GW.Space | ‖k‖ ≤ R} : Set GW.Space).indicator d.coefficient) := by
  have h := MemLp.coeFn_toLp (d.cutoff_memLp (max d.lowerCutoff R) (le_max_left _ _))
  simpa only [convolutionCutoff,max_eq_right hR] using h

lemma convolutionShell_ae (d : ConvolutionTailData) (R S : ℝ)
    (hR : d.lowerCutoff ≤ R) (hRS : R ≤ S) :
    ((convolutionCutoff d S-convolutionCutoff d R : OneBoson) : GW.Space → ℂ) =ᵐ[volume]
      fun k => if R < ‖k‖ ∧ ‖k‖ ≤ S then d.coefficient k else 0 := by
  filter_upwards [Lp.coeFn_sub (convolutionCutoff d S) (convolutionCutoff d R),
    convolutionCutoff_ae d S (hR.trans hRS),convolutionCutoff_ae d R hR] with k hk hS hR'
  rw [hk]
  simp only [Pi.sub_apply]
  rw [hS,hR']
  by_cases ha : ‖k‖ ≤ R
  · have hb : ‖k‖ ≤ S := ha.trans hRS
    simp [ha,hb,not_lt.mpr ha]
  · by_cases hb : ‖k‖ ≤ S
    · simp [ha,hb,lt_of_not_ge ha]
    · simp [ha,hb]

lemma convolutionConstant_le (f : OneBoson) (η : ℝ) (hη : 0 ≤ η)
    (h : ∀ q : GW.Space,
      (∫⁻ k : GW.Space, ENNReal.ofReal (frankSchleinIntegrand f q k)) ≤ ENNReal.ofReal (η^2)) :
    frankSchleinConstant f ≤ η := by
  have hs : frankSchleinSup f ≤ η^2 := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨q,rfl⟩
    have hi := ofReal_integral_eq_lintegral_ofReal (frankSchleinIntegrand_integrable f q)
      (Eventually.of_forall (frankSchleinIntegrand_nonneg f q))
    have he : ENNReal.ofReal (frankSchleinIntegral f q) ≤ ENNReal.ofReal (η^2) :=
      hi.trans_le (h q)
    exact (ENNReal.ofReal_le_ofReal_iff (sq_nonneg η)).mp he
  have hsq := frankSchleinConstant_sq f
  nlinarith [frankSchleinConstant_nonneg f]

/- Source argument component Shell01. -/
lemma convolutionShellConstant_bound (d : ConvolutionTailData) (L R S : ℝ)
    (hL : d.lowerCutoff ≤ L) (hLR : L ≤ R) (hRS : R ≤ S) :
    frankSchleinConstant (convolutionCutoff d S-convolutionCutoff d R) ≤ d.error L := by
  apply convolutionConstant_le _ _ (d.error_nonneg L hL)
  intro q
  let g : GW.Space → ℝ≥0∞ := fun k => ENNReal.ofReal (‖d.coefficient k‖^2/(1+‖q-k‖^2))
  have hs : MeasurableSet {k : GW.Space | L < ‖k‖} := measurableSet_lt measurable_const measurable_norm
  calc
    _ ≤ ∫⁻ k : GW.Space, ({k : GW.Space | L < ‖k‖} : Set GW.Space).indicator g k := by
      apply lintegral_mono_ae
      filter_upwards [convolutionShell_ae d R S (hL.trans hLR) hRS] with k hk
      unfold frankSchleinIntegrand
      rw [hk]
      by_cases hp : R < ‖k‖ ∧ ‖k‖ ≤ S
      · have hpk : k ∈ {k : GW.Space | L < ‖k‖} := lt_of_le_of_lt hLR hp.1
        simp only [if_pos hp,Set.indicator_of_mem hpk,g]
        exact le_rfl
      · simp only [if_neg hp,norm_zero,zero_pow (by norm_num : 2 ≠ 0),zero_div,ENNReal.ofReal_zero]
        exact bot_le
    _ = ∫⁻ k : GW.Space in {k : GW.Space | L < ‖k‖}, g k := lintegral_indicator hs g
    _ ≤ ENNReal.ofReal (d.error L ^ 2) := d.tail_bound L hL q

/- Source argument component Limit03. -/
def convolutionCutoffMap (d : ConvolutionTailData) (R : ℝ) : FreeGraphDomain →L[ℂ] Physical :=
  convolutionAnnihilationMap (convolutionCutoff d R)

lemma convolutionAnnihilationMap_opNorm (f : OneBoson) :
    ‖convolutionAnnihilationMap f‖ ≤ (1/2 : ℝ)*frankSchleinConstant f :=
  ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) (frankSchleinConstant_nonneg f))
    (convolutionAnnihilation_norm f)

lemma convolutionCutoffMap_ordered_sharp (d : ConvolutionTailData) (L R S : ℝ)
    (hL : d.lowerCutoff ≤ L) (hLR : L ≤ R) (hRS : R ≤ S) :
    ‖convolutionCutoffMap d S-convolutionCutoffMap d R‖ ≤ (1/2 : ℝ)*d.error L := by
  have he := convolutionAnnihilationMap_sub (convolutionCutoff d S) (convolutionCutoff d R)
  have hc := convolutionShellConstant_bound d L R S hL hLR hRS
  calc
    _ = ‖convolutionAnnihilationMap (convolutionCutoff d S-convolutionCutoff d R)‖ :=
      (congrArg norm he).symm
    _ ≤ (1/2 : ℝ)*frankSchleinConstant (convolutionCutoff d S-convolutionCutoff d R) :=
      convolutionAnnihilationMap_opNorm _
    _ ≤ (1/2 : ℝ)*d.error L := mul_le_mul_of_nonneg_left hc (by norm_num)

lemma convolutionCutoffMap_ordered (d : ConvolutionTailData) (L R S : ℝ)
    (hL : d.lowerCutoff ≤ L) (hLR : L ≤ R) (hRS : R ≤ S) :
    ‖convolutionCutoffMap d S-convolutionCutoffMap d R‖ ≤ d.error L := by
  exact (convolutionCutoffMap_ordered_sharp d L R S hL hLR hRS).trans
    (by nlinarith [d.error_nonneg L hL])

lemma convolutionCutoffMap_cauchy_sharp (d : ConvolutionTailData) (L : ℝ)
    (hL : d.lowerCutoff ≤ L) (R : ℝ) (hR : L ≤ R) (S : ℝ) (hS : L ≤ S) :
    ‖convolutionCutoffMap d R-convolutionCutoffMap d S‖ ≤ (1/2 : ℝ)*d.error L := by
  rcases le_total R S with hRS | hSR
  · exact (norm_sub_rev (convolutionCutoffMap d R) (convolutionCutoffMap d S)).trans_le (convolutionCutoffMap_ordered_sharp d L R S hL hR hRS)
  · exact convolutionCutoffMap_ordered_sharp d L S R hL hS hSR

lemma convolutionCutoffMap_cauchy (d : ConvolutionTailData) (L : ℝ)
    (hL : d.lowerCutoff ≤ L) (R : ℝ) (hR : L ≤ R) (S : ℝ) (hS : L ≤ S) :
    ‖convolutionCutoffMap d R-convolutionCutoffMap d S‖ ≤ d.error L := by
  rcases le_total R S with hRS | hSR
  · exact (norm_sub_rev (convolutionCutoffMap d R) (convolutionCutoffMap d S)).trans_le (convolutionCutoffMap_ordered d L R S hL hR hRS)
  · exact convolutionCutoffMap_ordered d L S R hL hS hSR

lemma convolutionLimit_exists (d : ConvolutionTailData) :
    ∃! T : FreeGraphDomain →L[ℂ] Physical,
      ∀ L ≥ d.lowerCutoff, ∀ R ≥ L, ‖convolutionCutoffMap d R-T‖ ≤ (1/2 : ℝ)*d.error L := by
  have hε : Tendsto (fun R => (1/2 : ℝ)*d.error R) atTop (𝓝 0) := by
    simpa only [mul_zero] using d.error_tendsto.const_mul (1/2 : ℝ)
  exact GW.Analysis.cutoff_extension (convolutionCutoffMap d) d.lowerCutoff
    (fun R => (1/2 : ℝ)*d.error R) hε (convolutionCutoffMap_cauchy_sharp d)

def convolutionLimit (d : ConvolutionTailData) : FreeGraphDomain →L[ℂ] Physical :=
  (convolutionLimit_exists d).exists.choose

lemma convolutionLimit_sharp_bound (d : ConvolutionTailData) :
    ∀ L ≥ d.lowerCutoff, ∀ R ≥ L, ‖convolutionCutoffMap d R-convolutionLimit d‖ ≤ (1/2 : ℝ)*d.error L :=
  (convolutionLimit_exists d).exists.choose_spec

lemma convolutionLimit_bound (d : ConvolutionTailData) :
    ∀ L ≥ d.lowerCutoff, ∀ R ≥ L, ‖convolutionCutoffMap d R-convolutionLimit d‖ ≤ d.error L := by
  intro L hL R hR
  exact (convolutionLimit_sharp_bound d L hL R hR).trans (by nlinarith [d.error_nonneg L hL])

lemma convolutionLimit_sharp_error (d : ConvolutionTailData) (R : ℝ) (hR : d.lowerCutoff ≤ R) :
    ‖convolutionLimit d-convolutionCutoffMap d R‖ ≤ (1/2 : ℝ)*d.error R :=
  (norm_sub_rev (convolutionLimit d) (convolutionCutoffMap d R)).trans_le (convolutionLimit_sharp_bound d R hR R le_rfl)

lemma convolutionLimit_error (d : ConvolutionTailData) (R : ℝ) (hR : d.lowerCutoff ≤ R) :
    ‖convolutionLimit d-convolutionCutoffMap d R‖ ≤ d.error R :=
  (norm_sub_rev (convolutionLimit d) (convolutionCutoffMap d R)).trans_le (convolutionLimit_bound d R hR R le_rfl)

lemma convolutionLimit_tendsto (d : ConvolutionTailData) :
    Tendsto (convolutionCutoffMap d) atTop (𝓝 (convolutionLimit d)) :=
  GW.Analysis.cutoff_extension_tendsto d.error_tendsto (convolutionLimit_bound d)

lemma convolutionLimit_unique (d : ConvolutionTailData) (T : FreeGraphDomain →L[ℂ] Physical)
    (hT : ∀ R ≥ d.lowerCutoff, ‖T-convolutionCutoffMap d R‖ ≤ d.error R) :
    T = convolutionLimit d := by
  have hzero : ‖T-convolutionLimit d‖ = 0 := by
    apply le_antisymm ?_ (norm_nonneg (T-convolutionLimit d))
    have hlim : Tendsto (fun R : ℝ => 2*d.error R) atTop (𝓝 0) := by
      simpa only [mul_zero] using d.error_tendsto.const_mul 2
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    filter_upwards [eventually_ge_atTop d.lowerCutoff] with R hR
    calc
      _ = ‖(T-convolutionCutoffMap d R)+(convolutionCutoffMap d R-convolutionLimit d)‖ := by congr 1;abel
      _ ≤ ‖T-convolutionCutoffMap d R‖+‖convolutionCutoffMap d R-convolutionLimit d‖ := norm_add_le (T-convolutionCutoffMap d R) (convolutionCutoffMap d R-convolutionLimit d)
      _ ≤ d.error R+d.error R := add_le_add (hT R hR) (convolutionLimit_bound d R hR R le_rfl)
      _ = 2*d.error R := by ring
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

theorem convolutionUse (d : ConvolutionTailData) :
    ∃! T : FreeGraphDomain →L[ℂ] Physical,
      (∀ R ≥ d.lowerCutoff, ‖T-convolutionCutoffMap d R‖ ≤ d.error R) ∧
      Tendsto (convolutionCutoffMap d) atTop (𝓝 T) := by
  refine ⟨convolutionLimit d,⟨convolutionLimit_error d,convolutionLimit_tendsto d⟩,?_⟩
  intro T hT
  exact convolutionLimit_unique d T hT.1

/- Source argument component Public01. -/
lemma convolutionCutoffMap_original_graph (d : ConvolutionTailData) (R : ℝ) (u : FreeGraphDomain) :
    (freeGraphDomainInclusion u,convolutionCutoffMap d R u) ∈
      (generalizedAnnihilation (phaseMultiplicationKernel (convolutionCutoff d R))).graph :=
  convolutionAnnihilation_graph (convolutionCutoff d R) u

lemma convolutionCutoffMap_coefficient (d : ConvolutionTailData) (R : ℝ) (hR : d.lowerCutoff ≤ R) :
    (convolutionCutoff d R : GW.Space → ℂ) =ᵐ[volume]
      (({k : GW.Space | ‖k‖ ≤ R} : Set GW.Space).indicator d.coefficient) :=
  convolutionCutoff_ae d R hR

lemma convolutionUse_source (d : ConvolutionTailData) :
    (∀ R ≥ d.lowerCutoff, ∀ S ≥ R, ‖convolutionCutoffMap d S-convolutionCutoffMap d R‖ ≤ d.error R) ∧
    ∃! T : FreeGraphDomain →L[ℂ] Physical,
      (∀ R ≥ d.lowerCutoff, ‖T-convolutionCutoffMap d R‖ ≤ d.error R) ∧
      Tendsto (convolutionCutoffMap d) atTop (𝓝 T) := by
  refine ⟨?_,convolutionUse d⟩
  intro R hR S hRS
  exact convolutionCutoffMap_ordered d R R S hR le_rfl hRS

end GW.Fock
