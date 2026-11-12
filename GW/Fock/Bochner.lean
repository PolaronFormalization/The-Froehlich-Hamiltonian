module
public import GW.Fock.NumberCore
public import GW.Analysis.SeriesDomination
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ENNReal
namespace GW.Fock
section BochnerSum
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
variable (E : ℕ → Type*) [∀ n, NormedAddCommGroup (E n)]
  [∀ n, InnerProductSpace ℂ (E n)]

abbrev BochnerSectorSum : Type _ := lp (fun n => Lp (E n) 2 μ) 2
abbrev BochnerFock : Type _ := Lp (lp E 2) 2 μ

omit [∀ n, InnerProductSpace ℂ (E n)] in
lemma sectorRepresentatives_square_integrable (u : BochnerSectorSum μ E) (n : ℕ) :
    Integrable (fun x => ‖u n x‖^2) μ := by
  have h := (Lp.memLp (u n)).norm_rpow two_ne_zero ENNReal.ofNat_ne_top
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,memLp_one_iff_integrable] using h

lemma sectorRepresentatives_square_summable (u : BochnerSectorSum μ E) :
    Summable (fun n => ∫ x, ‖u n x‖^2 ∂μ) := by
  have h := (GW.Analysis.memℓp_two_iff_sq (fun n => u n)).mp (lp.memℓp u)
  simpa only [GW.Analysis.l2_norm_sq (𝕜 := ℂ)] using h

lemma bochnerReconstruction_exists (u : BochnerSectorSum μ E) :
    ∃ U : BochnerFock μ E, (∀ᵐ x ∂μ, ∀ n, U x n = u n x) ∧
      ‖U‖^2 = ‖u‖^2 := by
  obtain ⟨U,hU,hN⟩ := GW.Analysis.reconstruction_from_real_integrals
    (fun n => (Lp.stronglyMeasurable (u n)).aestronglyMeasurable)
    (sectorRepresentatives_square_integrable μ E u)
    (sectorRepresentatives_square_summable μ E u)
  refine ⟨U,hU,?_⟩
  rw [GW.Analysis.l2_norm_sq (𝕜 := ℂ),hN,GW.Analysis.lp_norm_sq]
  apply tsum_congr
  intro n
  exact (GW.Analysis.l2_norm_sq (𝕜 := ℂ) (u n)).symm

def bochnerCoordinate (n : ℕ) : BochnerFock μ E →L[ℂ] Lp (E n) 2 μ :=
  (lp.evalCLM ℂ E 2 n).compLpL (p := 2) (μ := μ)

lemma bochnerCoordinate_ae (U : BochnerFock μ E) :
    ∀ᵐ x ∂μ, ∀ n, bochnerCoordinate μ E n U x = U x n :=
  ae_all_iff.mpr (fun n => (lp.evalCLM ℂ E 2 n).coeFn_compLp U)

lemma bochnerCoordinate_ext {U V : BochnerFock μ E}
    (h : ∀ n, bochnerCoordinate μ E n U = bochnerCoordinate μ E n V) : U = V := by
  apply Lp.ext
  filter_upwards [bochnerCoordinate_ae μ E U,bochnerCoordinate_ae μ E V] with x hx hy
  apply lp.ext
  funext n
  rw [← hx n,← hy n,h n]

def bochnerReconstruct (u : BochnerSectorSum μ E) : BochnerFock μ E :=
  (bochnerReconstruction_exists μ E u).choose
lemma bochnerReconstruct_ae (u : BochnerSectorSum μ E) :
    ∀ᵐ x ∂μ, ∀ n, bochnerReconstruct μ E u x n = u n x :=
  (bochnerReconstruction_exists μ E u).choose_spec.1
lemma bochnerReconstruct_norm_sq (u : BochnerSectorSum μ E) :
    ‖bochnerReconstruct μ E u‖^2 = ‖u‖^2 :=
  (bochnerReconstruction_exists μ E u).choose_spec.2

lemma bochnerCoordinate_reconstruct (u : BochnerSectorSum μ E) (n : ℕ) :
    bochnerCoordinate μ E n (bochnerReconstruct μ E u) = u n := by
  apply Lp.ext
  filter_upwards [bochnerCoordinate_ae μ E (bochnerReconstruct μ E u),
    bochnerReconstruct_ae μ E u] with x hx hy
  exact (hx n).trans (hy n)

def bochnerReconstructLinear : BochnerSectorSum μ E →ₗ[ℂ] BochnerFock μ E where
  toFun := bochnerReconstruct μ E
  map_add' u v := by
    apply bochnerCoordinate_ext μ E
    intro n
    rw [map_add,bochnerCoordinate_reconstruct,bochnerCoordinate_reconstruct,bochnerCoordinate_reconstruct]
    rfl
  map_smul' c u := by
    apply bochnerCoordinate_ext μ E
    intro n
    rw [map_smul,bochnerCoordinate_reconstruct,bochnerCoordinate_reconstruct]
    rfl

def bochnerReconstructIsometry : BochnerSectorSum μ E →ₗᵢ[ℂ] BochnerFock μ E where
  toLinearMap := bochnerReconstructLinear μ E
  norm_map' u := by
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (bochnerReconstruct_norm_sq μ E u)

lemma bochnerCoordinate_norm_integral (U : BochnerFock μ E) (n : ℕ) :
    ENNReal.ofReal (‖bochnerCoordinate μ E n U‖^2) =
      ∫⁻ x, ENNReal.ofReal (‖bochnerCoordinate μ E n U x‖^2) ∂μ := by
  rw [GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
  apply ofReal_integral_eq_lintegral_ofReal
  · have h := (Lp.memLp (bochnerCoordinate μ E n U)).norm_rpow two_ne_zero ENNReal.ofNat_ne_top
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,memLp_one_iff_integrable] using h
  · exact Eventually.of_forall (fun _ => sq_nonneg _)

lemma bochnerCoordinates_square_lintegral (U : BochnerFock μ E) :
    (∑' n, ENNReal.ofReal (‖bochnerCoordinate μ E n U‖^2)) =
      ∫⁻ x, ENNReal.ofReal (‖U x‖^2) ∂μ := by
  simp_rw [bochnerCoordinate_norm_integral]
  have ht : (∫⁻ x, ∑' n, ENNReal.ofReal (‖bochnerCoordinate μ E n U x‖^2) ∂μ) =
      ∑' n, ∫⁻ x, ENNReal.ofReal (‖bochnerCoordinate μ E n U x‖^2) ∂μ :=
    lintegral_tsum (fun n => ((Lp.stronglyMeasurable
      (bochnerCoordinate μ E n U)).norm.pow 2).aemeasurable.ennreal_ofReal)
  rw [← ht]
  apply lintegral_congr_ae
  filter_upwards [bochnerCoordinate_ae μ E U] with x hx
  simp_rw [hx]
  rw [GW.Analysis.lp_norm_sq]
  exact (ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _)
    ((GW.Analysis.memℓp_two_iff_sq _).mp (lp.memℓp (U x)))).symm

lemma bochnerCoordinates_memℓp (U : BochnerFock μ E) :
    Memℓp (fun n => bochnerCoordinate μ E n U) 2 := by
  have hi : Integrable (fun x => ‖U x‖^2) μ := by
    have h := (Lp.memLp U).norm_rpow two_ne_zero ENNReal.ofNat_ne_top
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,memLp_one_iff_integrable] using h
  have hf : (∫⁻ x, ENNReal.ofReal (‖U x‖^2) ∂μ) < ∞ :=
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun _ => sq_nonneg _))).mp hi.2
  have hs := ENNReal.summable_toReal (by
    rw [bochnerCoordinates_square_lintegral μ E U]
    exact ne_of_lt hf)
  apply (GW.Analysis.memℓp_two_iff_sq _).mpr
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using hs

def bochnerDecompose (U : BochnerFock μ E) : BochnerSectorSum μ E :=
  ⟨fun n => bochnerCoordinate μ E n U,bochnerCoordinates_memℓp μ E U⟩

lemma bochnerReconstruct_decompose (U : BochnerFock μ E) :
    bochnerReconstruct μ E (bochnerDecompose μ E U) = U := by
  apply bochnerCoordinate_ext μ E
  intro n
  exact bochnerCoordinate_reconstruct μ E (bochnerDecompose μ E U) n

lemma bochnerDecompose_reconstruct (u : BochnerSectorSum μ E) :
    bochnerDecompose μ E (bochnerReconstruct μ E u) = u := by
  apply lp.ext
  funext n
  exact bochnerCoordinate_reconstruct μ E u n

def bochnerUnitary : BochnerSectorSum μ E ≃ₗᵢ[ℂ] BochnerFock μ E :=
  LinearIsometryEquiv.ofSurjective (bochnerReconstructIsometry μ E)
    (fun U => ⟨bochnerDecompose μ E U,bochnerReconstruct_decompose μ E U⟩)

lemma bochnerCoordinate_simpleTensor (γ : Lp ℂ 2 μ) (u : lp E 2) (n : ℕ) :
    bochnerCoordinate μ E n ((ContinuousLinearMap.toSpanSingleton ℂ u).compLp γ) =
      (ContinuousLinearMap.toSpanSingleton ℂ (u n)).compLp γ := by
  apply Lp.ext
  filter_upwards [bochnerCoordinate_ae μ E ((ContinuousLinearMap.toSpanSingleton ℂ u).compLp γ),
    (ContinuousLinearMap.toSpanSingleton ℂ u).coeFn_compLp γ,
    (ContinuousLinearMap.toSpanSingleton ℂ (u n)).coeFn_compLp γ] with x hx hy hz
  rw [hx n,hy,hz]
  rfl

lemma simpleTensor_memℓp (γ : Lp ℂ 2 μ) (u : lp E 2) :
    Memℓp (fun n => (ContinuousLinearMap.toSpanSingleton ℂ (u n)).compLp γ) 2 := by
  convert bochnerCoordinates_memℓp μ E ((ContinuousLinearMap.toSpanSingleton ℂ u).compLp γ) using 1
  funext n
  exact (bochnerCoordinate_simpleTensor μ E γ u n).symm

def electronSimpleTensor (γ : Lp ℂ 2 μ) (u : lp E 2) : BochnerSectorSum μ E :=
  ⟨fun n => (ContinuousLinearMap.toSpanSingleton ℂ (u n)).compLp γ,simpleTensor_memℓp μ E γ u⟩

lemma bochnerUnitary_simpleTensor (γ : Lp ℂ 2 μ) (u : lp E 2) :
    bochnerUnitary μ E (electronSimpleTensor μ E γ u) =
      (ContinuousLinearMap.toSpanSingleton ℂ u).compLp γ := by
  apply bochnerCoordinate_ext μ E
  intro n
  change bochnerCoordinate μ E n (bochnerReconstruct μ E (electronSimpleTensor μ E γ u)) = _
  rw [bochnerCoordinate_reconstruct,bochnerCoordinate_simpleTensor]
  rfl

lemma bochnerCoordinate_single (n j : ℕ) (f : Lp (E n) 2 μ) :
    bochnerCoordinate μ E j ((lp.singleContinuousLinearMap ℂ E 2 n).compLp f) =
      (lp.single 2 n f : BochnerSectorSum μ E) j := by
  apply Lp.ext
  by_cases hj : j = n
  · subst j
    filter_upwards [bochnerCoordinate_ae μ E ((lp.singleContinuousLinearMap ℂ E 2 n).compLp f),
      (lp.singleContinuousLinearMap ℂ E 2 n).coeFn_compLp f] with x hx hy
    rw [hx n,hy,lp.single_apply_self]
    exact lp.single_apply_self 2 n (f x)
  · filter_upwards [bochnerCoordinate_ae μ E ((lp.singleContinuousLinearMap ℂ E 2 n).compLp f),
      (lp.singleContinuousLinearMap ℂ E 2 n).coeFn_compLp f,
      (Lp.coeFn_zero (E := E j) (p := 2) (μ := μ))] with x hx hy hz
    rw [hx j,hy,lp.single_apply_ne _ _ _ hj]
    change lp.single 2 n (f x) j = (0 : Lp (E j) 2 μ) x
    rw [lp.single_apply_ne _ _ _ hj,hz]
    rfl

lemma bochnerUnitary_single (n : ℕ) (f : Lp (E n) 2 μ) :
    bochnerUnitary μ E (lp.single 2 n f) =
      (lp.singleContinuousLinearMap ℂ E 2 n).compLp f := by
  apply bochnerCoordinate_ext μ E
  intro j
  change bochnerCoordinate μ E j (bochnerReconstruct μ E (lp.single 2 n f)) = _
  rw [bochnerCoordinate_reconstruct,bochnerCoordinate_single]

def physicalSectorProjection (n : ℕ) : BochnerFock μ E →L[ℂ] BochnerFock μ E :=
  ((lp.singleContinuousLinearMap ℂ E 2 n).comp (lp.evalCLM ℂ E 2 n)).compLpL 2 μ

set_option backward.isDefEq.respectTransparency.types false in
lemma bochnerUnitary_sectorProjection (n : ℕ) (u : BochnerSectorSum μ E) :
    bochnerUnitary μ E (lp.single 2 n (u n)) =
      physicalSectorProjection μ E n (bochnerUnitary μ E u) := by
  rw [bochnerUnitary_single]
  apply Lp.ext
  filter_upwards [(lp.singleContinuousLinearMap ℂ E 2 n).coeFn_compLp (u n),
    (((lp.singleContinuousLinearMap ℂ E 2 n).comp (lp.evalCLM ℂ E 2 n)).coeFn_compLp
      (bochnerUnitary μ E u)),bochnerReconstruct_ae μ E u] with x hx hy hc
  exact hx.trans ((congrArg (lp.singleContinuousLinearMap ℂ E 2 n) (hc n).symm).trans hy.symm)

lemma bochnerCoordinate_unitary (u : BochnerSectorSum μ E) (n : ℕ) :
    bochnerCoordinate μ E n (bochnerUnitary μ E u) = u n :=
  bochnerCoordinate_reconstruct μ E u n

lemma bochnerCoordinate_cutoff (m n : ℕ) (U : BochnerFock μ E) :
    bochnerCoordinate μ E n ((cutoff E m).compLp U) =
      if n ≤ m then bochnerCoordinate μ E n U else 0 := by
  apply Lp.ext
  filter_upwards [bochnerCoordinate_ae μ E ((cutoff E m).compLp U),
    (cutoff E m).coeFn_compLp U,bochnerCoordinate_ae μ E U,
    (Lp.coeFn_zero (E := E n) (p := 2) (μ := μ))] with x hx hy hu hz
  rw [hx n,hy,cutoff_apply]
  by_cases hn : n ≤ m
  · simp only [ite_eq_left hn]
    exact (hu n).symm
  · simp only [ite_eq_right hn]
    exact hz.symm

lemma bochnerUnitary_cutoff (m : ℕ) (u : BochnerSectorSum μ E) :
    bochnerUnitary μ E (cutoff (fun n => Lp (E n) 2 μ) m u) =
      (cutoff E m).compLp (bochnerUnitary μ E u) := by
  apply bochnerCoordinate_ext μ E
  intro n
  rw [bochnerCoordinate_unitary,cutoff_apply,bochnerCoordinate_cutoff,bochnerCoordinate_unitary]

lemma bochnerUnitary_symm_coordinate (U : BochnerFock μ E) (n : ℕ) :
    (bochnerUnitary μ E).symm U n = bochnerCoordinate μ E n U := by
  have h := bochnerCoordinate_reconstruct μ E ((bochnerUnitary μ E).symm U) n
  change bochnerCoordinate μ E n (bochnerUnitary μ E ((bochnerUnitary μ E).symm U)) = _ at h
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h.symm

def bochnerDiagonalDomain (a : ℕ → ℝ) : Submodule ℂ (BochnerFock μ E) :=
  (scalarDiagonal (fun n => Lp (E n) 2 μ) a).domain.comap (bochnerUnitary μ E).symm.toLinearMap

def bochnerDiagonalInput (a : ℕ → ℝ) : bochnerDiagonalDomain μ E a →ₗ[ℂ]
    (scalarDiagonal (fun n => Lp (E n) 2 μ) a).domain where
  toFun u := ⟨(bochnerUnitary μ E).symm u,u.property⟩
  map_add' u v := by apply Subtype.ext;exact map_add _ _ _
  map_smul' c u := by apply Subtype.ext;exact map_smul _ _ _

def bochnerDiagonal (a : ℕ → ℝ) : BochnerFock μ E →ₗ.[ℂ] BochnerFock μ E where
  domain := bochnerDiagonalDomain μ E a
  toFun := (bochnerUnitary μ E).toLinearMap.comp
    ((scalarDiagonal (fun n => Lp (E n) 2 μ) a).toFun.comp (bochnerDiagonalInput μ E a))

lemma bochnerDiagonal_coordinates (a : ℕ → ℝ) (u : (bochnerDiagonal μ E a).domain) :
    ∀ᵐ x ∂μ, ∀ n, bochnerDiagonal μ E a u x n = (a n : ℂ) • (u : BochnerFock μ E) x n := by
  let v := (bochnerUnitary μ E).symm (u : BochnerFock μ E)
  have hin := bochnerReconstruct_ae μ E v
  have hb : bochnerReconstruct μ E v = (u : BochnerFock μ E) :=
    (bochnerUnitary μ E).apply_symm_apply (u : BochnerFock μ E)
  rw [hb] at hin
  have hout := bochnerReconstruct_ae μ E
    (scalarDiagonal (fun n => Lp (E n) 2 μ) a (bochnerDiagonalInput μ E a u))
  have hsmul := ae_all_iff.mpr (fun n => Lp.coeFn_smul (a n : ℂ) (v n))
  filter_upwards [hin,hout,hsmul] with x hx hy hz
  intro n
  change bochnerReconstruct μ E
    (scalarDiagonal (fun n => Lp (E n) 2 μ) a (bochnerDiagonalInput μ E a u)) x n = _
  rw [hy n,scalarDiagonal_apply]
  exact (hz n).trans (congrArg (fun z : E n => (a n : ℂ) • z) (hx n).symm)

lemma bochnerDiagonal_domain_iff_coordinates (a : ℕ → ℝ) (U : BochnerFock μ E) :
    U ∈ (bochnerDiagonal μ E a).domain ↔
      ∃ V : BochnerFock μ E, ∀ᵐ x ∂μ, ∀ n, V x n = (a n : ℂ) • U x n := by
  constructor
  · intro hU
    exact ⟨bochnerDiagonal μ E a ⟨U,hU⟩,bochnerDiagonal_coordinates μ E a ⟨U,hU⟩⟩
  · rintro ⟨V,hV⟩
    have hcoord : ∀ n, bochnerCoordinate μ E n V = (a n : ℂ) • bochnerCoordinate μ E n U := by
      intro n
      apply Lp.ext
      filter_upwards [bochnerCoordinate_ae μ E U,bochnerCoordinate_ae μ E V,hV,
        Lp.coeFn_smul (a n : ℂ) (bochnerCoordinate μ E n U)] with x hu hv h hx
      exact (hv n).trans ((h n).trans ((congrArg (fun z : E n => (a n : ℂ) • z) (hu n).symm).trans hx.symm))
    change Memℓp (fun n => (a n : ℂ) • ((bochnerUnitary μ E).symm U) n) 2
    have he : (fun n => (a n : ℂ) • ((bochnerUnitary μ E).symm U) n) =
        fun n => ((bochnerUnitary μ E).symm V) n := by
      funext n
      rw [bochnerUnitary_symm_coordinate,bochnerUnitary_symm_coordinate]
      exact (hcoord n).symm
    rw [he]
    exact lp.memℓp ((bochnerUnitary μ E).symm V)

lemma bochnerDiagonal_domain_iff_graph (a : ℕ → ℝ) (U : BochnerFock μ E) :
    U ∈ (bochnerDiagonal μ E a).domain ↔
      ∃ V : BochnerFock μ E, ∀ᵐ x ∂μ, (U x,V x) ∈ (scalarDiagonal E a).graph := by
  rw [bochnerDiagonal_domain_iff_coordinates]
  constructor
  · rintro ⟨V,hV⟩
    exact ⟨V,hV.mono (fun x hx => (scalarDiagonal_graph_iff E a (U x,V x)).mpr hx)⟩
  · rintro ⟨V,hV⟩
    exact ⟨V,hV.mono (fun x hx => (scalarDiagonal_graph_iff E a (U x,V x)).mp hx)⟩

lemma bochnerDiagonal_domain_map (a : ℕ → ℝ) :
    (bochnerDiagonal μ E a).domain =
      (scalarDiagonal (fun n => Lp (E n) 2 μ) a).domain.map (bochnerUnitary μ E).toLinearMap := by
  apply Submodule.ext
  intro U
  constructor
  · intro hU
    exact ⟨(bochnerUnitary μ E).symm U,hU,(bochnerUnitary μ E).apply_symm_apply U⟩
  · rintro ⟨u,hu,rfl⟩
    change (bochnerUnitary μ E).symm (bochnerUnitary μ E u) ∈ (scalarDiagonal (fun n => Lp (E n) 2 μ) a).domain
    rw [LinearIsometryEquiv.symm_apply_apply]
    exact hu

lemma bochnerDiagonal_unitary_mem (a : ℕ → ℝ)
    (u : (scalarDiagonal (fun n => Lp (E n) 2 μ) a).domain) :
    bochnerUnitary μ E (u : BochnerSectorSum μ E) ∈ (bochnerDiagonal μ E a).domain := by
  change (bochnerUnitary μ E).symm (bochnerUnitary μ E (u : BochnerSectorSum μ E)) ∈ (scalarDiagonal (fun n => Lp (E n) 2 μ) a).domain
  rw [LinearIsometryEquiv.symm_apply_apply]
  exact u.property

lemma bochnerDiagonal_intertwines (a : ℕ → ℝ)
    (u : (scalarDiagonal (fun n => Lp (E n) 2 μ) a).domain) :
    bochnerDiagonal μ E a ⟨bochnerUnitary μ E u,bochnerDiagonal_unitary_mem μ E a u⟩ =
      bochnerUnitary μ E (scalarDiagonal (fun n => Lp (E n) 2 μ) a u) := by
  apply (bochnerUnitary μ E).symm.injective
  change (bochnerUnitary μ E).symm (bochnerUnitary μ E
    (scalarDiagonal (fun n => Lp (E n) 2 μ) a
      (bochnerDiagonalInput μ E a ⟨bochnerUnitary μ E u,bochnerDiagonal_unitary_mem μ E a u⟩))) = _
  simp only [LinearIsometryEquiv.symm_apply_apply]
  congr 1
  apply Subtype.ext
  exact (bochnerUnitary μ E).symm_apply_apply (u : BochnerSectorSum μ E)

lemma bochnerDiagonal_one : bochnerDiagonal μ E (fun _ => 1) =
    (LinearMap.id : BochnerFock μ E →ₗ[ℂ] BochnerFock μ E).toPMap ⊤ := by
  apply LinearPMap.ext
  · apply top_unique
    intro U _
    change Memℓp (fun n => (1 : ℂ) • ((bochnerUnitary μ E).symm U) n) 2
    simpa only [one_smul] using lp.memℓp ((bochnerUnitary μ E).symm U)
  · intro U hU ht
    change bochnerDiagonal μ E (fun _ => 1) ⟨U,hU⟩ = U
    apply Lp.ext
    filter_upwards [bochnerDiagonal_coordinates μ E (fun _ => 1) ⟨U,hU⟩] with x hx
    apply lp.ext
    funext n
    simpa only [Complex.ofReal_one,one_smul] using hx n

/-- Physical maximal number power, with the same explicit vacuum-zero endpoint convention. -/
def bochnerNumberPower (r : ℝ) : BochnerFock μ E →ₗ.[ℂ] BochnerFock μ E :=
  bochnerDiagonal μ E (numberPowerCoefficient r)
def bochnerShiftedNumberPower (r : ℝ) : BochnerFock μ E →ₗ.[ℂ] BochnerFock μ E :=
  bochnerDiagonal μ E (fun n => ((n : ℝ)+1)^r)

lemma bochnerNumberPower_zero : bochnerNumberPower μ E 0 =
    (LinearMap.id : BochnerFock μ E →ₗ[ℂ] BochnerFock μ E).toPMap ⊤ := by
  unfold bochnerNumberPower
  have h : numberPowerCoefficient 0 = fun _ => 1 := by funext n; simp [numberPowerCoefficient]
  rw [h]
  exact bochnerDiagonal_one μ E

lemma bochnerNumberPower_domain (r : ℝ) (hr : 0 < r) (U : BochnerFock μ E) :
    U ∈ (bochnerNumberPower μ E r).domain ↔
      ∃ V : BochnerFock μ E, ∀ᵐ x ∂μ, ∀ n : ℕ,
        V x n = (↑((n : ℝ)^r) : ℂ) • U x n := by
  change U ∈ (bochnerDiagonal μ E (numberPowerCoefficient r)).domain ↔ _
  rw [bochnerDiagonal_domain_iff_coordinates]
  simp only [numberPowerCoefficient,ite_eq_right (ne_of_gt hr)]

lemma bochnerNumberPower_domain_map (r : ℝ) :
    (bochnerNumberPower μ E r).domain =
      (numberPower (fun n => Lp (E n) 2 μ) r).domain.map (bochnerUnitary μ E).toLinearMap :=
  bochnerDiagonal_domain_map μ E (numberPowerCoefficient r)

lemma bochnerShiftedNumberPower_domain_map (r : ℝ) :
    (bochnerShiftedNumberPower μ E r).domain =
      (shiftedNumberPower (fun n => Lp (E n) 2 μ) r).domain.map (bochnerUnitary μ E).toLinearMap :=
  bochnerDiagonal_domain_map μ E (fun n => ((n : ℝ)+1)^r)

lemma bochnerNumberPower_unitary_mem (r : ℝ)
    (u : (numberPower (fun n => Lp (E n) 2 μ) r).domain) :
    bochnerUnitary μ E (u : BochnerSectorSum μ E) ∈ (bochnerNumberPower μ E r).domain :=
  bochnerDiagonal_unitary_mem μ E (numberPowerCoefficient r) u

lemma bochnerNumberPower_intertwines (r : ℝ)
    (u : (numberPower (fun n => Lp (E n) 2 μ) r).domain) :
    bochnerNumberPower μ E r ⟨bochnerUnitary μ E u,bochnerNumberPower_unitary_mem μ E r u⟩ =
      bochnerUnitary μ E (numberPower (fun n => Lp (E n) 2 μ) r u) :=
  bochnerDiagonal_intertwines μ E (numberPowerCoefficient r) u

lemma bochnerShiftedNumberPower_unitary_mem (r : ℝ)
    (u : (shiftedNumberPower (fun n => Lp (E n) 2 μ) r).domain) :
    bochnerUnitary μ E (u : BochnerSectorSum μ E) ∈ (bochnerShiftedNumberPower μ E r).domain :=
  bochnerDiagonal_unitary_mem μ E (fun n => ((n : ℝ)+1)^r) u

lemma bochnerShiftedNumberPower_intertwines (r : ℝ)
    (u : (shiftedNumberPower (fun n => Lp (E n) 2 μ) r).domain) :
    bochnerShiftedNumberPower μ E r
      ⟨bochnerUnitary μ E u,bochnerShiftedNumberPower_unitary_mem μ E r u⟩ =
      bochnerUnitary μ E (shiftedNumberPower (fun n => Lp (E n) 2 μ) r u) :=
  bochnerDiagonal_intertwines μ E (fun n => ((n : ℝ)+1)^r) u

lemma bochnerNumberPower_domain_iff_graph (r : ℝ) (U : BochnerFock μ E) :
    U ∈ (bochnerNumberPower μ E r).domain ↔
      ∃ V : BochnerFock μ E, ∀ᵐ x ∂μ, (U x,V x) ∈ (numberPower E r).graph :=
  bochnerDiagonal_domain_iff_graph μ E (numberPowerCoefficient r) U

lemma bochnerNumberPower_one : bochnerNumberPower μ E 1 =
    bochnerDiagonal μ E (fun n => (n : ℝ)) := by
  unfold bochnerNumberPower
  congr 1
  funext n
  simp [numberPowerCoefficient]

end BochnerSum
/-- The canonical unitary into the project's fixed physical Hilbert space. -/
abbrev electronBosonUnitary : ElectronBosonSum ≃ₗᵢ[ℂ] Physical :=
  bochnerUnitary (volume : Measure GW.Space) Sector
abbrev physicalNumberPower (r : ℝ) : Physical →ₗ.[ℂ] Physical :=
  bochnerNumberPower (volume : Measure GW.Space) Sector r
abbrev physicalShiftedNumberPower (r : ℝ) : Physical →ₗ.[ℂ] Physical :=
  bochnerShiftedNumberPower (volume : Measure GW.Space) Sector r

abbrev physicalNumberOperator : Physical →ₗ.[ℂ] Physical :=
  bochnerDiagonal (volume : Measure GW.Space) Sector (fun n => (n : ℝ))

lemma physicalNumberPower_domain_map (r : ℝ) :
    (physicalNumberPower r).domain =
      (electronNumberPower r).domain.map electronBosonUnitary.toLinearMap :=
  bochnerNumberPower_domain_map (volume : Measure GW.Space) Sector r

lemma physicalShiftedNumberPower_domain_map (r : ℝ) :
    (physicalShiftedNumberPower r).domain =
      (electronShiftedNumberPower r).domain.map electronBosonUnitary.toLinearMap :=
  bochnerShiftedNumberPower_domain_map (volume : Measure GW.Space) Sector r

lemma physicalNumberPower_zero : physicalNumberPower 0 =
    (LinearMap.id : Physical →ₗ[ℂ] Physical).toPMap ⊤ :=
  bochnerNumberPower_zero (volume : Measure GW.Space) Sector

lemma physicalNumberPower_one : physicalNumberPower 1 = physicalNumberOperator :=
  bochnerNumberPower_one (volume : Measure GW.Space) Sector

end GW.Fock
