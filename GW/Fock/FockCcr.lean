module
public import GW.Fock.FockTwoFields
public import GW.Analysis.BridgeSymmetrizer
public import GW.Fock.CreationSymmetrization
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal
namespace GW.Fock

lemma ccr_kernel_vacuum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (F G : BosonKernel E) (u : E) :
    kernelAnnihilation F 0 (kernelCreation G 0 (kernelFixedVacuum u)) =
      kernelFixedVacuum (F.adjoint (G u)) := by
  rw [kernelCreation_vacuum,kernelAnnihilation_vacuum]

lemma ccr_ordinary_kernel_adjoint (f : OneBoson) : (ordinaryKernel f).adjoint = innerSL ℂ f :=
  ContinuousLinearMap.adjoint_toSpanSingleton f

lemma ccr_ordinary_vacuum (f g : OneBoson) (u : ℂ) :
    sectorAnnihilation ordinarySectorKernel (ordinaryKernel f) 0
      (sectorCreation ordinarySectorKernel (ordinaryKernel g) 0 u) = ⟪f,g⟫_ℂ • u := by
  change (ordinarySectorKernel 0).symm
    (kernelAnnihilation (ordinaryKernel f) 0 ((ordinarySectorKernel 1)
      ((ordinarySectorKernel 1).symm (kernelCreation (ordinaryKernel g) 0 (ordinarySectorKernel 0 u))))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  change kernelFixedVacuum.symm
    (kernelAnnihilation (ordinaryKernel f) 0 (kernelCreation (ordinaryKernel g) 0 (kernelFixedVacuum u))) = _
  rw [ccr_kernel_vacuum,LinearIsometryEquiv.symm_apply_apply,ccr_ordinary_kernel_adjoint]
  change ⟪f,u • g⟫_ℂ = ⟪f,g⟫_ℂ * u
  rw [inner_smul_right,mul_comm]

lemma ccr_closed_norm_completion
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (C : H →ₗ.[ℂ] H) (hC : C.IsClosed) (x y z : ℕ → H) (u a : H)
    (hx : Tendsto x atTop (𝓝 u)) (hz : Tendsto z atTop (𝓝 a))
    (hgraph : ∀ n, (x n,y n) ∈ C.graph) (c : ℝ) (hc : 0 ≤ c)
    (hdiff : ∀ n m, ‖y n-y m‖^2 = ‖z n-z m‖^2+c^2*‖x n-x m‖^2)
    (hnorm : ∀ n, ‖y n‖^2 = ‖z n‖^2+c^2*‖x n‖^2) :
    ∃ b, Tendsto y atTop (𝓝 b) ∧ (u,b) ∈ C.graph ∧ ‖b‖^2 = ‖a‖^2+c^2*‖u‖^2 := by
  have hbound (n m : ℕ) : ‖y n-y m‖ ≤ ‖z n-z m‖+c*‖x n-x m‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (mul_nonneg hc (norm_nonneg _)))).mp
    rw [hdiff]
    nlinarith [mul_nonneg (norm_nonneg (z n-z m)) (mul_nonneg hc (norm_nonneg (x n-x m)))]
  have hyc : CauchySeq y := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    have hc1 : 0 < c+1 := by linarith
    obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hx.cauchySeq (ε/(2*(c+1))) (by positivity)
    obtain ⟨M,hM⟩ := Metric.cauchySeq_iff.mp hz.cauchySeq (ε/2) (by positivity)
    refine ⟨max N M,fun n hn m hm => ?_⟩
    have h₁ : ‖x n-x m‖ < ε/(2*(c+1)) := by
      simpa only [dist_eq_norm] using hN n ((le_max_left _ _).trans hn) m ((le_max_left _ _).trans hm)
    have h₂ : ‖z n-z m‖ < ε/2 := by
      simpa only [dist_eq_norm] using hM n ((le_max_right _ _).trans hn) m ((le_max_right _ _).trans hm)
    rw [dist_eq_norm]
    have h₃ := mul_lt_mul_of_pos_left h₁ hc1
    have h₄ : (c+1)*(ε/(2*(c+1))) = ε/2 := by
      field_simp
      <;> ring
    rw [h₄] at h₃
    have h₅ : c*‖x n-x m‖ ≤ (c+1)*‖x n-x m‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    linarith [hbound n m]
  obtain ⟨b,hy⟩ := cauchySeq_tendsto_of_complete hyc
  have hg : (u,b) ∈ C.graph := hC.mem_of_tendsto (hx.prodMk_nhds hy)
    (Eventually.of_forall hgraph)
  have hlim : Tendsto (fun n => ‖y n‖^2) atTop (𝓝 (‖a‖^2+c^2*‖u‖^2)) :=
    ((hz.norm.pow 2).add ((hx.norm.pow 2).const_mul (c^2))).congr'
      (Eventually.of_forall (fun n => (hnorm n).symm))
  exact ⟨b,hy,hg,tendsto_nhds_unique (hy.norm.pow 2) hlim⟩

lemma ccr_creation_vacuum_norm (f : OneBoson) (u : ℂ) :
    ‖sectorCreation ordinarySectorKernel (ordinaryKernel f) 0 u‖ = ‖f‖*‖u‖ := by
  have he : ordinarySectorKernel 1 (sectorCreation ordinarySectorKernel (ordinaryKernel f) 0 u) =
      kernelOneBoson (ordinaryKernel f u) := by
    change ordinarySectorKernel 1 ((ordinarySectorKernel 1).symm
      (kernelCreation (ordinaryKernel f) 0 (kernelFixedVacuum u))) = _
    rw [LinearIsometryEquiv.apply_symm_apply,kernelCreation_vacuum]
  calc
    _ = ‖ordinarySectorKernel 1 (sectorCreation ordinarySectorKernel (ordinaryKernel f) 0 u)‖ :=
      ((ordinarySectorKernel 1).norm_map _).symm
    _ = ‖kernelOneBoson (ordinaryKernel f u)‖ := congrArg norm he
    _ = ‖ordinaryKernel f u‖ := kernelOneBoson.norm_map _
    _ = ‖f‖*‖u‖ := by change ‖u • f‖ = _; rw [norm_smul,mul_comm]

lemma ccr_contraction_tensor
    {X H : Type*} [MeasurableSpace X] (μ : Measure X)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (f g : Lp ℂ 2 μ) (u : H) :
    contraction μ f (tensorEmbedding μ g u) = ⟪f,g⟫_ℂ • u := by
  change (∫ x, (starRingEnd ℂ) (f x) • tensorEmbedding μ g u x ∂μ) = _
  rw [L2.inner_def]
  calc
    _ = ∫ x, ⟪f x,g x⟫_ℂ • u ∂μ := by
      apply integral_congr_ae
      filter_upwards [tensorEmbedding_ae μ g u] with x hx
      rw [hx]
      simp only [smul_smul,RCLike.inner_apply,mul_comm]
    _ = _ := integral_smul_const _ _

lemma ccr_prepend_inner (n : ℕ) (f g : OneBoson) (u v : AmbientSector n) :
    ⟪prependProduct n f u,prependProduct n g v⟫_ℂ = ⟪f,g⟫_ℂ*⟪u,v⟫_ℂ := by
  calc
    _ = ⟪productFunction volume (sectorMeasure n) f u,productFunction volume (sectorMeasure n) g v⟫_ℂ :=
      (splitUnitary n 0).symm.inner_map_map _ _
    _ = ⟪tensorEmbedding volume f u,tensorEmbedding volume g v⟫_ℂ := by
      rw [← productUnitary_tensor,← productUnitary_tensor,LinearIsometryEquiv.inner_map_map]
    _ = _ := by rw [← contraction_pairing,ccr_contraction_tensor,inner_smul_right]

lemma ccr_raw_annihilation_prepend (n : ℕ) (f g : OneBoson) (u : AmbientSector n) :
    kernelAnnihilationRaw (ordinaryKernel f) n (prependProduct n g u) = ⟪f,g⟫_ℂ • u := by
  apply ext_inner_left ℂ
  intro v
  rw [← kernelRaw_pairing,ordinaryKernelCreationRaw,ccr_prepend_inner,inner_smul_right]

def ccrCreationCutoffInput (f : OneBoson) (m : ℕ) (u : Carrier) : (ordinaryCreation f).domain :=
  ⟨cutoff Sector (m+1) u,finiteSector_le_creation
    (sectorCreation ordinarySectorKernel (ordinaryKernel f)) (cutoff_mem_finiteSectorDomain Sector (m+1) u)⟩

def ccrAnnihilationCutoffInput (f : OneBoson) (m : ℕ) (u : Carrier) : (ordinaryAnnihilation f).domain :=
  ⟨cutoff Sector (m+1) u,finiteSector_le_annihilation
    (sectorAnnihilation ordinarySectorKernel (ordinaryKernel f)) (cutoff_mem_finiteSectorDomain Sector (m+1) u)⟩

lemma ccrCreationCutoff_value (f : OneBoson) (m : ℕ) (u : (ordinaryCreation f).domain) :
    ordinaryCreation f (ccrCreationCutoffInput f m u.val) = cutoff Sector (m+2) (ordinaryCreation f u) :=
  maximalSectorCreation_cutoff (sectorCreation ordinarySectorKernel (ordinaryKernel f)) (m+1) u

lemma ccrAnnihilationCutoff_value (f : OneBoson) (m : ℕ) (u : (ordinaryAnnihilation f).domain) :
    ordinaryAnnihilation f (ccrAnnihilationCutoffInput f m u.val) = cutoff Sector m (ordinaryAnnihilation f u) :=
  maximalSectorAnnihilation_cutoff_succ (sectorAnnihilation ordinarySectorKernel (ordinaryKernel f)) m u

lemma ccrCreationCutoff_graph_tendsto (f : OneBoson) (u : (ordinaryCreation f).domain) :
    Tendsto (fun m => ((ccrCreationCutoffInput f m u.val).val,
      ordinaryCreation f (ccrCreationCutoffInput f m u.val))) atTop (𝓝 (u.val,ordinaryCreation f u)) := by
  have hx : Tendsto (fun m => (ccrCreationCutoffInput f m u.val).val) atTop (𝓝 u.val) :=
    (cutoff_tendsto Sector u.val).comp (tendsto_add_atTop_nat 1)
  have hy : Tendsto (fun m => ordinaryCreation f (ccrCreationCutoffInput f m u.val)) atTop
      (𝓝 (ordinaryCreation f u)) := by
    simp_rw [ccrCreationCutoff_value]
    exact (cutoff_tendsto Sector (ordinaryCreation f u)).comp (tendsto_add_atTop_nat 2)
  exact hx.prodMk_nhds hy

lemma ccrAnnihilationCutoff_graph_tendsto (f : OneBoson) (u : (ordinaryAnnihilation f).domain) :
    Tendsto (fun m => ((ccrAnnihilationCutoffInput f m u.val).val,
      ordinaryAnnihilation f (ccrAnnihilationCutoffInput f m u.val))) atTop (𝓝 (u.val,ordinaryAnnihilation f u)) := by
  have hx : Tendsto (fun m => (ccrAnnihilationCutoffInput f m u.val).val) atTop (𝓝 u.val) :=
    (cutoff_tendsto Sector u.val).comp (tendsto_add_atTop_nat 1)
  have hy : Tendsto (fun m => ordinaryAnnihilation f (ccrAnnihilationCutoffInput f m u.val)) atTop
      (𝓝 (ordinaryAnnihilation f u)) := by
    simp_rw [ccrAnnihilationCutoff_value]
    exact cutoff_tendsto Sector _
  exact hx.prodMk_nhds hy

def ccrTwoOutput (b c : Bool) (f g : OneBoson) (u : (shiftedNumberPower Sector 1).domain) : Carrier :=
  (ordinaryWeightedChoice b f 0 le_rfl (ordinaryRootToZero (ordinaryTwoMiddle c g u))).val

lemma ccrTwoOutput_graph (b c : Bool) (f g : OneBoson) (u : (shiftedNumberPower Sector 1).domain) :
    ∃ w : Carrier, (u.val,w) ∈ (sectorFieldChoice ordinarySectorKernel c (ordinaryKernel g)).graph ∧
      (w,ccrTwoOutput b c f g u) ∈ (sectorFieldChoice ordinarySectorKernel b (ordinaryKernel f)).graph := by
  refine ⟨(ordinaryTwoMiddle c g u).val,?_,?_⟩
  · exact sectorWeightedChoice_graph ordinarySectorKernel c (ordinaryKernel g) (1/2) (by norm_num) (ordinaryTwoInput u)
  · exact sectorWeightedChoice_graph ordinarySectorKernel b (ordinaryKernel f) 0 le_rfl
      (ordinaryRootToZero (ordinaryTwoMiddle c g u))

lemma ccrTwoOutput_norm (b c : Bool) (f g : OneBoson) (u : (shiftedNumberPower Sector 1).domain) :
    ‖ccrTwoOutput b c f g u‖ ≤ Real.sqrt 2*‖f‖*‖g‖*‖shiftedNumberPower Sector 1 u‖ :=
  ordinaryTwoTerm_norm b c f g u

lemma ccr_two_graph_unique
    {H : Type*} [AddCommGroup H] [Module ℂ H]
    (A B : H →ₗ.[ℂ] H) (x w w' z z' : H)
    (ha : (x,w) ∈ A.graph) (ha' : (x,w') ∈ A.graph)
    (hb : (w,z) ∈ B.graph) (hb' : (w',z') ∈ B.graph) : z = z' := by
  have hw : w = w' := A.mem_graph_snd_inj ha ha' rfl
  subst w'
  exact B.mem_graph_snd_inj hb hb' rfl

lemma ccrTwoOutput_sub (b c : Bool) (f g : OneBoson)
    (u v : (shiftedNumberPower Sector 1).domain) :
    ccrTwoOutput b c f g (u-v) = ccrTwoOutput b c f g u-ccrTwoOutput b c f g v := by
  obtain ⟨w,hw,hz⟩ := ccrTwoOutput_graph b c f g u
  obtain ⟨w',hw',hz'⟩ := ccrTwoOutput_graph b c f g v
  obtain ⟨d,hd,he⟩ := ccrTwoOutput_graph b c f g (u-v)
  exact ccr_two_graph_unique _ _ (u.val-v.val) d (w-w') _ _ hd
    ((sectorFieldChoice ordinarySectorKernel c (ordinaryKernel g)).graph.sub_mem hw hw') he
    ((sectorFieldChoice ordinarySectorKernel b (ordinaryKernel f)).graph.sub_mem hz hz')

def ccrNumberInput (u : numberOperator.domain) : (shiftedNumberPower Sector 1).domain :=
  ⟨u.val,ordinaryNumber_shiftedOne_domain ▸ u.property⟩

lemma ccr_tensor_prepend (n : ℕ) (h : Fin (n+1) → OneBoson) :
    prependProduct n (h 0) (rawTensor n (fun i => h i.succ)) = rawTensor (n+1) h := by
  apply (splitUnitary n 0).injective
  change splitUnitary n 0 ((splitUnitary n 0).symm
    (productFunction volume (sectorMeasure n) (h 0) (rawTensor n (fun i => h i.succ)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply,rawTensor_split]

lemma ccr_raw_annihilation_tensor (n : ℕ) (f : OneBoson) (h : Fin (n+1) → OneBoson) :
    kernelAnnihilationRaw (ordinaryKernel f) n (rawTensor (n+1) h) =
      ⟪f,h 0⟫_ℂ • rawTensor n (fun i => h i.succ) := by
  rw [← ccr_tensor_prepend,ccr_raw_annihilation_prepend]

lemma ccr_raw_annihilation_tensor_swap (n : ℕ) (f g : OneBoson) (h : Fin (n+2) → OneBoson) :
    kernelAnnihilationRaw (ordinaryKernel f) n
      (kernelAnnihilationRaw (ordinaryKernel g) (n+1) (rawTensor (n+2) h)) =
    kernelAnnihilationRaw (ordinaryKernel g) n
      (kernelAnnihilationRaw (ordinaryKernel f) (n+1)
        (rawTensor (n+2) (Fin.cons (h 1) (Fin.cons (h 0) (fun i => h i.succ.succ))))) := by
  simp only [ccr_raw_annihilation_tensor,map_smul,Fin.cons_zero,Fin.cons_succ]
  rw [smul_smul,smul_smul,mul_comm]
  rfl

lemma ccr_rawTensor_permutation (n : ℕ) (f : Fin n → OneBoson) (τ : Equiv.Perm (Fin n)) :
    permutationL2 n τ (rawTensor n f) = rawTensor n (fun i => f (τ.symm i)) := by
  apply Lp.ext
  filter_upwards [permutationL2_ae n τ (rawTensor n f),
    (coordinatePermutation_preserving n τ).quasiMeasurePreserving.ae (rawTensor_ae n f),
    rawTensor_ae n (fun i => f (τ.symm i))] with k h₁ h₂ h₃
  rw [h₁,h₂,h₃]
  simp only [rawTensorRep,coordinatePermutation_apply]
  exact Fintype.prod_equiv τ _ _ (fun i => by simp)

lemma ccr_raw_annihilation_swap_map (n : ℕ) (f g : OneBoson) (u : AmbientSector (n+2)) :
    kernelAnnihilationRaw (ordinaryKernel f) n (kernelAnnihilationRaw (ordinaryKernel g) (n+1) u) =
      kernelAnnihilationRaw (ordinaryKernel g) n (kernelAnnihilationRaw (ordinaryKernel f) (n+1)
        (permutationL2 (n+2) (Equiv.swap 0 1) u)) := by
  let A := (kernelAnnihilationRaw (ordinaryKernel f) n).comp
    (kernelAnnihilationRaw (ordinaryKernel g) (n+1))
  let B := ((kernelAnnihilationRaw (ordinaryKernel g) n).comp
    (kernelAnnihilationRaw (ordinaryKernel f) (n+1))).comp
      (permutationL2 (n+2) (Equiv.swap 0 1)).toContinuousLinearMap
  have hker : LinearMap.ker (A-B).toLinearMap = ⊤ := by
    apply rawTensor_dense_criterion (n+2) _ (A-B).isClosed_ker
    intro h
    change A (rawTensor (n+2) h)-B (rawTensor (n+2) h) = 0
    apply sub_eq_zero.mpr
    change kernelAnnihilationRaw (ordinaryKernel f) n
      (kernelAnnihilationRaw (ordinaryKernel g) (n+1) (rawTensor (n+2) h)) =
      kernelAnnihilationRaw (ordinaryKernel g) n
      (kernelAnnihilationRaw (ordinaryKernel f) (n+1)
        (permutationL2 (n+2) (Equiv.swap 0 1) (rawTensor (n+2) h)))
    rw [ccr_rawTensor_permutation]
    have he : (fun i => h ((Equiv.swap (0 : Fin (n+2)) 1).symm i)) =
        Fin.cons (h 1) (Fin.cons (h 0) (fun i => h i.succ.succ)) := by
      funext i
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
      · simp
      · simp
      · simp only [Equiv.symm_swap,Equiv.swap_apply_of_ne_of_ne
          (Fin.succ_ne_zero _ : k.succ.succ ≠ (0 : Fin (n+2)))
          (by intro he; exact Fin.succ_ne_zero k ((Fin.succ_injective (n+1)) (he.trans (by rfl))) : k.succ.succ ≠ (1 : Fin (n+2))),Fin.cons_succ]
    rw [he]
    exact ccr_raw_annihilation_tensor_swap n f g h
  have hu : u ∈ LinearMap.ker (A-B).toLinearMap := by rw [hker]; trivial
  exact sub_eq_zero.mp hu

lemma ccr_raw_annihilation_commute_fixed (n : ℕ) (f g : OneBoson)
    (u : kernelFixed (E := ℂ) (n+2)) :
    kernelAnnihilationRaw (ordinaryKernel f) n
      (kernelAnnihilationRaw (ordinaryKernel g) (n+1) u) =
    kernelAnnihilationRaw (ordinaryKernel g) n
      (kernelAnnihilationRaw (ordinaryKernel f) (n+1) u) := by
  have h := ccr_raw_annihilation_swap_map n f g u
  have hu := (mem_kernelFixed (n+2) u.val).mp u.property (Equiv.swap 0 1)
  rw [ordinaryKernelPermutation] at hu
  rw [hu] at h
  exact h

lemma ccr_kernel_annihilation_commute (n : ℕ) (f g : OneBoson)
    (u : kernelFixed (E := ℂ) (n+2)) :
    kernelAnnihilation (ordinaryKernel f) n (kernelAnnihilation (ordinaryKernel g) (n+1) u) =
    kernelAnnihilation (ordinaryKernel g) n (kernelAnnihilation (ordinaryKernel f) (n+1) u) := by
  apply Subtype.ext
  simp only [kernelAnnihilation_value,map_smul]
  rw [ccr_raw_annihilation_commute_fixed]

lemma ccr_sector_annihilation_commute (n : ℕ) (f g : OneBoson) (u : Sector (n+2)) :
    sectorAnnihilation ordinarySectorKernel (ordinaryKernel f) n
      (sectorAnnihilation ordinarySectorKernel (ordinaryKernel g) (n+1) u) =
    sectorAnnihilation ordinarySectorKernel (ordinaryKernel g) n
      (sectorAnnihilation ordinarySectorKernel (ordinaryKernel f) (n+1) u) := by
  apply (ordinarySectorKernel n).injective
  simp only [sectorAnnihilation,ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.apply_symm_apply]
  exact ccr_kernel_annihilation_commute n f g (ordinarySectorKernel (n+2) u)

lemma ccr_annihilation_graph_coordinate (f : OneBoson) (x y : Carrier)
    (hg : (x,y) ∈ (ordinaryAnnihilation f).graph) (n : ℕ) :
    y n = sectorAnnihilation ordinarySectorKernel (ordinaryKernel f) n (x (n+1)) := by
  obtain ⟨u,hu,hy⟩ := (ordinaryAnnihilation f).mem_graph_iff.mp hg
  have hx : u.val = x := hu
  calc
    y n = ordinaryAnnihilation f u n := congrArg (fun z : Carrier => z n) hy.symm
    _ = _ := by rw [ordinaryAnnihilation_apply,hx]

lemma ccrTwoOutput_annihilation_coordinate (f g : OneBoson)
    (u : (shiftedNumberPower Sector 1).domain) (n : ℕ) :
    ccrTwoOutput false false f g u n =
      sectorAnnihilation ordinarySectorKernel (ordinaryKernel f) n
        (sectorAnnihilation ordinarySectorKernel (ordinaryKernel g) (n+1) (u.val (n+2))) := by
  obtain ⟨w,hw,hz⟩ := ccrTwoOutput_graph false false f g u
  change (u.val,w) ∈ (ordinaryAnnihilation g).graph at hw
  change (w,ccrTwoOutput false false f g u) ∈ (ordinaryAnnihilation f).graph at hz
  rw [ccr_annihilation_graph_coordinate f _ _ hz n,
    ccr_annihilation_graph_coordinate g _ _ hw (n+1)]

set_option backward.isDefEq.respectTransparency.types false in
lemma ccrTwoOutput_annihilation_commute (f g : OneBoson)
    (u : (shiftedNumberPower Sector 1).domain) :
    ccrTwoOutput false false f g u = ccrTwoOutput false false g f u := by
  apply lp.ext
  funext n
  rw [ccrTwoOutput_annihilation_coordinate,ccrTwoOutput_annihilation_coordinate]
  exact ccr_sector_annihilation_commute n f g (u.val (n+2))

lemma ccr_closed_norm_reverse_completion
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) (hA : A.IsClosed) (x y z : ℕ → H) (u b : H)
    (hx : Tendsto x atTop (𝓝 u)) (hy : Tendsto y atTop (𝓝 b))
    (hgraph : ∀ n, (x n,z n) ∈ A.graph) (c : ℝ)
    (hdiff : ∀ n m, ‖y n-y m‖^2 = ‖z n-z m‖^2+c^2*‖x n-x m‖^2)
    (hnorm : ∀ n, ‖y n‖^2 = ‖z n‖^2+c^2*‖x n‖^2) :
    ∃ a, Tendsto z atTop (𝓝 a) ∧ (u,a) ∈ A.graph ∧ ‖b‖^2 = ‖a‖^2+c^2*‖u‖^2 := by
  have hbound (n m : ℕ) : ‖z n-z m‖ ≤ ‖y n-y m‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    nlinarith [hdiff n m,mul_nonneg (sq_nonneg c) (sq_nonneg ‖x n-x m‖)]
  have hzc : CauchySeq z := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hy.cauchySeq ε hε
    refine ⟨N,fun n hn m hm => ?_⟩
    rw [dist_eq_norm]
    exact (hbound n m).trans_lt (by simpa only [dist_eq_norm] using hN n hn m hm)
  obtain ⟨a,hz⟩ := cauchySeq_tendsto_of_complete hzc
  have hg : (u,a) ∈ A.graph := hA.mem_of_tendsto (hx.prodMk_nhds hz)
    (Eventually.of_forall hgraph)
  have hlim : Tendsto (fun n => ‖y n‖^2) atTop (𝓝 (‖a‖^2+c^2*‖u‖^2)) :=
    ((hz.norm.pow 2).add ((hx.norm.pow 2).const_mul (c^2))).congr'
      (Eventually.of_forall (fun n => (hnorm n).symm))
  exact ⟨a,hz,hg,tendsto_nhds_unique (hy.norm.pow 2) hlim⟩

lemma ccr_creation_graph_zero (f : OneBoson) (x y : Carrier)
    (hg : (x,y) ∈ (ordinaryCreation f).graph) : y 0 = 0 := by
  obtain ⟨u,hu,hy⟩ := (ordinaryCreation f).mem_graph_iff.mp hg
  have he : (ordinaryCreation f u : Carrier) = y := hy
  exact (congrArg (fun v : Carrier => v 0) he).symm.trans (ordinaryCreation_zero f u)

lemma ccr_creation_graph_coordinate (f : OneBoson) (x y : Carrier)
    (hg : (x,y) ∈ (ordinaryCreation f).graph) (n : ℕ) :
    y (n+1) = sectorCreation ordinarySectorKernel (ordinaryKernel f) n (x n) := by
  obtain ⟨u,hu,hy⟩ := (ordinaryCreation f).mem_graph_iff.mp hg
  have hx : u.val = x := hu
  calc
    y (n+1) = ordinaryCreation f u (n+1) := congrArg (fun z : Carrier => z (n+1)) hy.symm
    _ = _ := by rw [ordinaryCreation_succ,hx]

lemma ccrTwoOutput_creation_zero (f g : OneBoson)
    (u : (shiftedNumberPower Sector 1).domain) : ccrTwoOutput true true f g u 0 = 0 := by
  obtain ⟨w,hw,hz⟩ := ccrTwoOutput_graph true true f g u
  exact ccr_creation_graph_zero f _ _ hz

lemma ccrTwoOutput_creation_one (f g : OneBoson)
    (u : (shiftedNumberPower Sector 1).domain) : ccrTwoOutput true true f g u 1 = 0 := by
  obtain ⟨w,hw,hz⟩ := ccrTwoOutput_graph true true f g u
  change (u.val,w) ∈ (ordinaryCreation g).graph at hw
  change (w,ccrTwoOutput true true f g u) ∈ (ordinaryCreation f).graph at hz
  rw [ccr_creation_graph_coordinate f _ _ hz 0,ccr_creation_graph_zero g _ _ hw,map_zero]

lemma ccrTwoOutput_creation_coordinate (f g : OneBoson)
    (u : (shiftedNumberPower Sector 1).domain) (n : ℕ) :
    ccrTwoOutput true true f g u (n+2) =
      sectorCreation ordinarySectorKernel (ordinaryKernel f) (n+1)
        (sectorCreation ordinarySectorKernel (ordinaryKernel g) n (u.val n)) := by
  obtain ⟨w,hw,hz⟩ := ccrTwoOutput_graph true true f g u
  change (u.val,w) ∈ (ordinaryCreation g).graph at hw
  change (w,ccrTwoOutput true true f g u) ∈ (ordinaryCreation f).graph at hz
  rw [ccr_creation_graph_coordinate f _ _ hz (n+1),
    ccr_creation_graph_coordinate g _ _ hw n]


lemma ccrTwoOutput_creation_commute (f g : OneBoson)
    (u : (shiftedNumberPower Sector 1).domain) :
    ccrTwoOutput true true f g u = ccrTwoOutput true true g f u := by
  apply lp.ext
  funext j
  match j with
  | 0 => rw [ccrTwoOutput_creation_zero, ccrTwoOutput_creation_zero]
  | 1 => rw [ccrTwoOutput_creation_one, ccrTwoOutput_creation_one]
  | n+2 =>
    rw [ccrTwoOutput_creation_coordinate,ccrTwoOutput_creation_coordinate]
    exact creationSector_commute n f g (u.val n)




lemma ccr_raw_swap_prepend (n : ℕ) (f g : OneBoson) (u : AmbientSector (n+1)) :
    kernelAnnihilationRaw (ordinaryKernel f) (n+1)
      (permutationL2 (n+2) (Equiv.swap 0 1) (kernelCreationRaw (ordinaryKernel g) (n+1) u)) =
    kernelCreationRaw (ordinaryKernel g) n (kernelAnnihilationRaw (ordinaryKernel f) n u) := by
  let A := ((kernelAnnihilationRaw (ordinaryKernel f) (n+1)).comp
    (permutationL2 (n+2) (Equiv.swap 0 1)).toContinuousLinearMap).comp
    (kernelCreationRaw (ordinaryKernel g) (n+1))
  let B := (kernelCreationRaw (ordinaryKernel g) n).comp
    (kernelAnnihilationRaw (ordinaryKernel f) n)
  have hk : LinearMap.ker (A-B).toLinearMap = ⊤ := by
    apply rawTensor_dense_criterion (n+1) _ (A-B).isClosed_ker
    intro h
    change A (rawTensor (n+1) h)-B (rawTensor (n+1) h) = 0
    apply sub_eq_zero.mpr
    change kernelAnnihilationRaw (ordinaryKernel f) (n+1)
      (permutationL2 (n+2) (Equiv.swap 0 1)
        (kernelCreationRaw (ordinaryKernel g) (n+1) (rawTensor (n+1) h))) =
      kernelCreationRaw (ordinaryKernel g) n (kernelAnnihilationRaw (ordinaryKernel f) n (rawTensor (n+1) h))
    rw [ordinaryKernelCreationRaw,creationPrepend_tensor,rawTensor_permutation]
    have he : (fun i : Fin (n+2) => (Fin.cons g h : Fin (n+2) → OneBoson) ((Equiv.swap (0 : Fin (n+2)) 1).symm i)) =
        (Fin.cons (h 0) (Fin.cons g (fun i : Fin n => h i.succ)) : Fin (n+2) → OneBoson) := by
      funext i
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
      · simp
      · simp
      · simp only [Equiv.symm_swap,Equiv.swap_apply_of_ne_of_ne
          (Fin.succ_ne_zero _ : k.succ.succ ≠ (0 : Fin (n+2)))
          (by intro he; exact Fin.succ_ne_zero k ((Fin.succ_injective (n+1)) (he.trans (by rfl))) : k.succ.succ ≠ (1 : Fin (n+2))),Fin.cons_succ]
    rw [he,ccr_raw_annihilation_tensor,ccr_raw_annihilation_tensor,map_smul,
      ordinaryKernelCreationRaw,creationPrepend_tensor]
    simp only [Fin.cons_zero,Fin.cons_succ]
  have hu : u ∈ LinearMap.ker (A-B).toLinearMap := hk ▸ Submodule.mem_top
  exact sub_eq_zero.mp hu


lemma ccr_raw_swap_prepend_succ (n : ℕ) (f g : OneBoson) (u : AmbientSector (n+1))
    (hu : u ∈ symmetricSector (n+1)) (j : Fin (n+1)) :
    kernelAnnihilationRaw (ordinaryKernel f) (n+1)
      (permutationL2 (n+2) (swapZero (n+1) j.succ)
        (kernelCreationRaw (ordinaryKernel g) (n+1) u)) =
    permutationL2 (n+1) (swapZero n j)
      (kernelCreationRaw (ordinaryKernel g) n (kernelAnnihilationRaw (ordinaryKernel f) n u)) := by
  let τ := swapZero n j
  let H := extendSpectator (n+1) τ
  have h₀ : (H : Equiv.Perm (Fin (n+2))) 0 = 0 := H.property
  have h₁ : (H : Equiv.Perm (Fin (n+2))) 1 = j.succ := by
    change (extendSpectator (n+1) τ : Equiv.Perm (Fin (n+2))) (Fin.succ (0:Fin (n+1))) = _
    rw [extendSpectator_succ]
    exact congrArg Fin.succ (swapZero_zero n j)
  have ht : (H : Equiv.Perm (Fin (n+2))) * Equiv.swap 0 1 =
      swapZero (n+1) j.succ * (H : Equiv.Perm (Fin (n+2))) := by
    have h := Equiv.mul_swap_eq_swap_mul (H : Equiv.Perm (Fin (n+2))) 0 1
    rw [h₀,h₁] at h
    exact h
  have hv : permutationL2 (n+2) H (kernelCreationRaw (ordinaryKernel g) (n+1) u) =
      kernelCreationRaw (ordinaryKernel g) (n+1) u := by
    rw [creationRaw_ordinary_spectator]
    have he := hu τ
    exact congrArg (kernelCreationRaw (ordinaryKernel g) (n+1)) he
  have hp : permutationL2 (n+2) (swapZero (n+1) j.succ)
      (kernelCreationRaw (ordinaryKernel g) (n+1) u) =
      permutationL2 (n+2) H (permutationL2 (n+2) (Equiv.swap 0 1)
        (kernelCreationRaw (ordinaryKernel g) (n+1) u)) := by
    rw [permutationL2_comp,ht,← permutationL2_comp,hv]
  rw [hp]
  have hs := kernelAnnihilation_spectator (ordinaryKernel f) (n+1) τ
    (permutationL2 (n+2) (Equiv.swap 0 1) (kernelCreationRaw (ordinaryKernel g) (n+1) u))
  rw [ordinaryKernelPermutation,ordinaryKernelPermutation] at hs
  rw [hs,ccr_raw_swap_prepend]


lemma ccr_raw_mixed_sum (n : ℕ) (f g : OneBoson) (u : AmbientSector (n+1))
    (hu : u ∈ symmetricSector (n+1)) :
    (∑ j : Fin (n+2), kernelAnnihilationRaw (ordinaryKernel f) (n+1)
      (permutationL2 (n+2) (swapZero (n+1) j)
        (kernelCreationRaw (ordinaryKernel g) (n+1) u))) =
    ⟪f,g⟫_ℂ • u + ∑ j : Fin (n+1), permutationL2 (n+1) (swapZero n j)
      (kernelCreationRaw (ordinaryKernel g) n (kernelAnnihilationRaw (ordinaryKernel f) n u)) := by
  rw [Fin.sum_univ_succ]
  have hz : swapZero (n+1) (0:Fin (n+2)) = 1 := Equiv.swap_self 0
  rw [hz, permutationL2_one, ordinaryKernelCreationRaw, ccr_raw_annihilation_prepend]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [← ordinaryKernelCreationRaw]
  exact ccr_raw_swap_prepend_succ n f g u hu j

lemma ccr_creation_average_cancel (n : ℕ) (g : OneBoson) (v : AmbientSector n)
    (hv : v ∈ symmetricSector n) :
    (Real.sqrt (n+1:ℕ):ℂ) • creationAverage n g v =
      ∑ j : Fin (n+1), permutationL2 (n+1) (swapZero n j)
        (kernelCreationRaw (ordinaryKernel g) n v) := by
  rw [creationAverage_sum n g v hv, smul_smul]
  have hs : (Real.sqrt (n+1:ℕ):ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by positivity : 0 < ((n+1:ℕ):ℝ))))
  rw [mul_inv_cancel₀ hs,one_smul]
  simp only [ordinaryKernelCreationRaw]

set_option backward.isDefEq.respectTransparency.types false in
lemma ccr_kernel_mixed_pos (n : ℕ) (f g : OneBoson) (u : kernelFixed (E := ℂ) (n+1)) :
    kernelAnnihilation (ordinaryKernel f) (n+1) (kernelCreation (ordinaryKernel g) (n+1) u) =
      ⟪f,g⟫_ℂ • u + kernelCreation (ordinaryKernel g) n (kernelAnnihilation (ordinaryKernel f) n u) := by
  have hu : (u : AmbientSector (n+1)) ∈ symmetricSector (n+1) :=
    (ordinaryKernelFixed_iff (n+1) _).mp u.property
  have ha : kernelAnnihilationRaw (ordinaryKernel f) n u ∈ symmetricSector n :=
    (ordinaryKernelFixed_iff n _).mp (kernelAnnihilationRaw_mem (ordinaryKernel f) n u u.property)
  have hc : (kernelCreation (ordinaryKernel g) (n+1) u : AmbientSector (n+2)) =
      creationAverage (n+1) g (u : AmbientSector (n+1)) := by
    rw [kernelCreation_value,ordinaryKernelSymmetrizer,ordinaryKernelCreationRaw]
    rfl
  apply Subtype.ext
  change (kernelAnnihilation (ordinaryKernel f) (n+1) (kernelCreation (ordinaryKernel g) (n+1) u) : AmbientSector (n+1)) = _
  rw [kernelAnnihilation_value,hc,creationAverage_sum (n+1) g (u : AmbientSector (n+1)) hu,map_smul,map_sum,smul_smul]
  have hs : (Real.sqrt (n+2:ℕ):ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by positivity : 0 < ((n+2:ℕ):ℝ))))
  rw [mul_inv_cancel₀ hs,one_smul]
  simp_rw [← ordinaryKernelCreationRaw]
  rw [ccr_raw_mixed_sum n f g (u : AmbientSector (n+1)) hu]
  change ⟪f,g⟫_ℂ • (u : AmbientSector (n+1)) + _ =
    ⟪f,g⟫_ℂ • (u : AmbientSector (n+1)) +
      (kernelCreation (ordinaryKernel g) n (kernelAnnihilation (ordinaryKernel f) n u) : AmbientSector (n+1))
  congr 1
  rw [← ccr_creation_average_cancel n g _ ha]
  rw [kernelCreation_value,kernelAnnihilation_value,map_smul,map_smul,ordinaryKernelSymmetrizer,
    ordinaryKernelCreationRaw]
  unfold creationAverage
  simp only [smul_smul]


lemma ccr_sector_mixed_pos (n : ℕ) (f g : OneBoson) (u : Sector (n+1)) :
    sectorAnnihilation ordinarySectorKernel (ordinaryKernel f) (n+1)
      (sectorCreation ordinarySectorKernel (ordinaryKernel g) (n+1) u) =
    ⟪f,g⟫_ℂ • u + sectorCreation ordinarySectorKernel (ordinaryKernel g) n
      (sectorAnnihilation ordinarySectorKernel (ordinaryKernel f) n u) := by
  apply (ordinarySectorKernel (n+1)).injective
  simp only [sectorAnnihilation,sectorCreation,ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.apply_symm_apply,map_add,map_smul]
  exact ccr_kernel_mixed_pos n f g (ordinarySectorKernel (n+1) u)

lemma ccrTwoOutput_AC_coordinate (f g : OneBoson)
    (u : (shiftedNumberPower Sector 1).domain) (n : ℕ) :
    ccrTwoOutput false true f g u n =
      sectorAnnihilation ordinarySectorKernel (ordinaryKernel f) n
        (sectorCreation ordinarySectorKernel (ordinaryKernel g) n (u.val n)) := by
  obtain ⟨w,hw,hz⟩ := ccrTwoOutput_graph false true f g u
  change (u.val,w) ∈ (ordinaryCreation g).graph at hw
  change (w,ccrTwoOutput false true f g u) ∈ (ordinaryAnnihilation f).graph at hz
  rw [ccr_annihilation_graph_coordinate f _ _ hz n,ccr_creation_graph_coordinate g _ _ hw n]

lemma ccrTwoOutput_CA_zero (f g : OneBoson)
    (u : (shiftedNumberPower Sector 1).domain) : ccrTwoOutput true false f g u 0 = 0 := by
  obtain ⟨w,hw,hz⟩ := ccrTwoOutput_graph true false f g u
  exact ccr_creation_graph_zero f _ _ hz

lemma ccrTwoOutput_CA_coordinate (f g : OneBoson)
    (u : (shiftedNumberPower Sector 1).domain) (n : ℕ) :
    ccrTwoOutput true false f g u (n+1) =
      sectorCreation ordinarySectorKernel (ordinaryKernel f) n
        (sectorAnnihilation ordinarySectorKernel (ordinaryKernel g) n (u.val (n+1))) := by
  obtain ⟨w,hw,hz⟩ := ccrTwoOutput_graph true false f g u
  change (u.val,w) ∈ (ordinaryAnnihilation g).graph at hw
  change (w,ccrTwoOutput true false f g u) ∈ (ordinaryCreation f).graph at hz
  rw [ccr_creation_graph_coordinate f _ _ hz n,ccr_annihilation_graph_coordinate g _ _ hw n]

set_option backward.isDefEq.respectTransparency.types false in
lemma ccrTwoOutput_mixed (f g : OneBoson) (u : (shiftedNumberPower Sector 1).domain) :
    ccrTwoOutput false true f g u = ⟪f,g⟫_ℂ • u.val + ccrTwoOutput true false g f u := by
  apply lp.ext
  funext j
  cases j with
  | zero =>
    change ccrTwoOutput false true f g u 0 = ⟪f,g⟫_ℂ • u.val 0 + ccrTwoOutput true false g f u 0
    rw [ccrTwoOutput_AC_coordinate,ccrTwoOutput_CA_zero,add_zero]
    exact ccr_ordinary_vacuum f g (u.val 0)
  | succ n =>
    change ccrTwoOutput false true f g u (n+1) = ⟪f,g⟫_ℂ • u.val (n+1) + ccrTwoOutput true false g f u (n+1)
    rw [ccrTwoOutput_AC_coordinate,ccrTwoOutput_CA_coordinate]
    change sectorAnnihilation ordinarySectorKernel (ordinaryKernel f) (n+1)
      (sectorCreation ordinarySectorKernel (ordinaryKernel g) (n+1) (u.val (n+1))) =
      ⟪f,g⟫_ℂ • u.val (n+1) + sectorCreation ordinarySectorKernel (ordinaryKernel g) n
        (sectorAnnihilation ordinarySectorKernel (ordinaryKernel f) n (u.val (n+1)))
    exact ccr_sector_mixed_pos n f g (u.val (n+1))


lemma ccr_graph_pair_creation (f : OneBoson) (u c v a : Carrier)
    (hc : (u,c) ∈ (ordinaryCreation f).graph)
    (ha : (v,a) ∈ (ordinaryAnnihilation f).graph) : ⟪c,v⟫_ℂ = ⟪u,a⟫_ℂ := by
  obtain ⟨x,hx,hc⟩ := (ordinaryCreation f).mem_graph_iff.mp hc
  obtain ⟨y,hy,ha⟩ := (ordinaryAnnihilation f).mem_graph_iff.mp ha
  have h := creation_annihilation_pairing
    (sectorCreation ordinarySectorKernel (ordinaryKernel f))
    (sectorAnnihilation ordinarySectorKernel (ordinaryKernel f))
    (sectorCreation_pairing ordinarySectorKernel (ordinaryKernel f)) x y
  have hx' : (x : Carrier) = u := hx
  have hy' : (y : Carrier) = v := hy
  have hc' : ordinaryCreation f x = c := hc
  have ha' : ordinaryAnnihilation f y = a := ha
  change ⟪ordinaryCreation f x,(y : Carrier)⟫_ℂ = ⟪(x : Carrier),ordinaryAnnihilation f y⟫_ℂ at h
  simpa only [hx',hy',hc',ha'] using h

lemma ccr_graph_pair_annihilation (f : OneBoson) (u a v c : Carrier)
    (ha : (u,a) ∈ (ordinaryAnnihilation f).graph)
    (hc : (v,c) ∈ (ordinaryCreation f).graph) : ⟪a,v⟫_ℂ = ⟪u,c⟫_ℂ := by
  have h := ccr_graph_pair_creation f v c u a hc ha
  simpa only [inner_conj_symm] using congrArg (starRingEnd ℂ) h.symm

lemma ccr_norm_of_graphs (f : OneBoson) (u c a ac ca : Carrier)
    (hc : (u,c) ∈ (ordinaryCreation f).graph)
    (ha : (u,a) ∈ (ordinaryAnnihilation f).graph)
    (hac : (c,ac) ∈ (ordinaryAnnihilation f).graph)
    (hca : (a,ca) ∈ (ordinaryCreation f).graph)
    (hmix : ac = ca + ((‖f‖^2:ℝ):ℂ) • u) :
    ‖c‖^2 = ‖a‖^2 + ‖f‖^2*‖u‖^2 := by
  have hC := ccr_graph_pair_creation f u c c ac hc hac
  have hA := ccr_graph_pair_annihilation f u a a ca ha hca
  calc
    ‖c‖^2 = RCLike.re ⟪c,c⟫_ℂ := norm_sq_eq_re_inner (𝕜 := ℂ) c
    _ = RCLike.re ⟪u,ac⟫_ℂ := congrArg (fun z : ℂ => RCLike.re z) hC
    _ = RCLike.re ⟪u,ca⟫_ℂ + ‖f‖^2 * RCLike.re ⟪u,u⟫_ℂ := by
      rw [hmix,inner_add_right,inner_smul_right,map_add]
      congr 1
      exact RCLike.re_ofReal_mul (K := ℂ) (‖f‖^2) ⟪u,u⟫_ℂ
    _ = ‖a‖^2 + ‖f‖^2*‖u‖^2 := by
      rw [← hA, ← norm_sq_eq_re_inner (𝕜 := ℂ), ← norm_sq_eq_re_inner (𝕜 := ℂ)]


def ccrFiniteCreationInput (f : OneBoson) : finiteSectorDomain Sector →ₗ[ℂ] (ordinaryCreation f).domain :=
  Submodule.inclusion (finiteSector_le_creation (sectorCreation ordinarySectorKernel (ordinaryKernel f)))

def ccrFiniteAnnihilationInput (f : OneBoson) : finiteSectorDomain Sector →ₗ[ℂ] (ordinaryAnnihilation f).domain :=
  Submodule.inclusion (finiteSector_le_annihilation (sectorAnnihilation ordinarySectorKernel (ordinaryKernel f)))

def ccrFiniteCreationOutput (f : OneBoson) : finiteSectorDomain Sector →ₗ[ℂ] Carrier :=
  (ordinaryCreation f).toFun.comp (ccrFiniteCreationInput f)

def ccrFiniteAnnihilationOutput (f : OneBoson) : finiteSectorDomain Sector →ₗ[ℂ] Carrier :=
  (ordinaryAnnihilation f).toFun.comp (ccrFiniteAnnihilationInput f)

lemma ccr_domains_forward_from_finite (f : OneBoson)
    (hfin : ∀ v : finiteSectorDomain Sector,
      ‖ccrFiniteCreationOutput f v‖^2 = ‖ccrFiniteAnnihilationOutput f v‖^2+‖f‖^2*‖(v:Carrier)‖^2)
    (u : (ordinaryAnnihilation f).domain) :
    ∃ h : (u:Carrier) ∈ (ordinaryCreation f).domain,
      ‖ordinaryCreation f ⟨u,h⟩‖^2 = ‖ordinaryAnnihilation f u‖^2+‖f‖^2*‖(u:Carrier)‖^2 := by
  let v : ℕ → finiteSectorDomain Sector := fun m =>
    ⟨cutoff Sector (m+1) u.val,cutoff_mem_finiteSectorDomain Sector (m+1) u.val⟩
  let x : ℕ → Carrier := fun m => (v m).val
  let y := fun m => ccrFiniteCreationOutput f (v m)
  let z := fun m => ccrFiniteAnnihilationOutput f (v m)
  have hx : Tendsto x atTop (𝓝 u.val) :=
    (cutoff_tendsto Sector u.val).comp (tendsto_add_atTop_nat 1)
  have hz : Tendsto z atTop (𝓝 (ordinaryAnnihilation f u)) := by
    exact (continuous_snd.tendsto (u.val,ordinaryAnnihilation f u)).comp (ccrAnnihilationCutoff_graph_tendsto f u)
  have hg (m : ℕ) : (x m,y m) ∈ (ordinaryCreation f).graph :=
    (ordinaryCreation f).mem_graph_iff.mpr ⟨ccrFiniteCreationInput f (v m),rfl,rfl⟩
  have hn (m : ℕ) : ‖y m‖^2 = ‖z m‖^2+‖f‖^2*‖x m‖^2 := hfin (v m)
  have hd (m k : ℕ) : ‖y m-y k‖^2 = ‖z m-z k‖^2+‖f‖^2*‖x m-x k‖^2 := by
    simpa only [map_sub, Submodule.coe_sub] using hfin (v m-v k)
  obtain ⟨b,hb,hgraph,hnorm⟩ := ccr_closed_norm_completion (ordinaryCreation f)
    (ordinaryCreation_closed f) x y z u.val (ordinaryAnnihilation f u) hx hz hg ‖f‖ (norm_nonneg _) hd hn
  obtain ⟨w,hw,hb⟩ := (ordinaryCreation f).mem_graph_iff.mp hgraph
  have hw' : w.val = u.val := hw
  have hm : u.val ∈ (ordinaryCreation f).domain := hw' ▸ w.property
  refine ⟨hm,?_⟩
  have he : w = (⟨u.val,hm⟩ : (ordinaryCreation f).domain) := Subtype.ext hw'
  rw [he] at hb
  have hb' : ordinaryCreation f ⟨u.val,hm⟩ = b := hb
  simpa only [hb'] using hnorm


lemma ccr_domains_reverse_from_finite (f : OneBoson)
    (hfin : ∀ v : finiteSectorDomain Sector,
      ‖ccrFiniteCreationOutput f v‖^2 = ‖ccrFiniteAnnihilationOutput f v‖^2+‖f‖^2*‖(v:Carrier)‖^2)
    (u : (ordinaryCreation f).domain) :
    ∃ h : (u:Carrier) ∈ (ordinaryAnnihilation f).domain,
      ‖ordinaryCreation f u‖^2 = ‖ordinaryAnnihilation f ⟨u,h⟩‖^2+‖f‖^2*‖(u:Carrier)‖^2 := by
  let v : ℕ → finiteSectorDomain Sector := fun m =>
    ⟨cutoff Sector (m+1) u.val,cutoff_mem_finiteSectorDomain Sector (m+1) u.val⟩
  let x : ℕ → Carrier := fun m => (v m).val
  let y := fun m => ccrFiniteCreationOutput f (v m)
  let z := fun m => ccrFiniteAnnihilationOutput f (v m)
  have hx : Tendsto x atTop (𝓝 u.val) :=
    (cutoff_tendsto Sector u.val).comp (tendsto_add_atTop_nat 1)
  have hy : Tendsto y atTop (𝓝 (ordinaryCreation f u)) := by
    exact (continuous_snd.tendsto (u.val,ordinaryCreation f u)).comp (ccrCreationCutoff_graph_tendsto f u)
  have hg (m : ℕ) : (x m,z m) ∈ (ordinaryAnnihilation f).graph :=
    (ordinaryAnnihilation f).mem_graph_iff.mpr ⟨ccrFiniteAnnihilationInput f (v m),rfl,rfl⟩
  have hn (m : ℕ) : ‖y m‖^2 = ‖z m‖^2+‖f‖^2*‖x m‖^2 := hfin (v m)
  have hd (m k : ℕ) : ‖y m-y k‖^2 = ‖z m-z k‖^2+‖f‖^2*‖x m-x k‖^2 := by
    simpa only [map_sub, Submodule.coe_sub] using hfin (v m-v k)
  obtain ⟨a,ha,hgraph,hnorm⟩ := ccr_closed_norm_reverse_completion (ordinaryAnnihilation f)
    (ordinaryAnnihilation_closed f) x y z u.val (ordinaryCreation f u) hx hy hg ‖f‖ hd hn
  obtain ⟨w,hw,ha⟩ := (ordinaryAnnihilation f).mem_graph_iff.mp hgraph
  have hw' : w.val = u.val := hw
  have hm : u.val ∈ (ordinaryAnnihilation f).domain := hw' ▸ w.property
  refine ⟨hm,?_⟩
  have he : w = (⟨u.val,hm⟩ : (ordinaryAnnihilation f).domain) := Subtype.ext hw'
  rw [he] at ha
  have ha' : ordinaryAnnihilation f ⟨u.val,hm⟩ = a := ha
  simpa only [ha'] using hnorm

lemma ccr_maximal_domains_from_finite (f : OneBoson)
    (hfin : ∀ v : finiteSectorDomain Sector,
      ‖ccrFiniteCreationOutput f v‖^2 = ‖ccrFiniteAnnihilationOutput f v‖^2+‖f‖^2*‖(v:Carrier)‖^2) :
    (ordinaryCreation f).domain = (ordinaryAnnihilation f).domain := by
  apply le_antisymm
  · intro u hu
    exact (ccr_domains_reverse_from_finite f hfin ⟨u,hu⟩).choose
  · intro u hu
    exact (ccr_domains_forward_from_finite f hfin ⟨u,hu⟩).choose


def ccrOneOutput (b : Bool) (f : OneBoson) (u : (shiftedNumberPower Sector 1).domain) : Carrier :=
  (ordinaryTwoMiddle b f u).val

lemma ccrOneOutput_graph (b : Bool) (f : OneBoson) (u : (shiftedNumberPower Sector 1).domain) :
    (u.val,ccrOneOutput b f u) ∈ (sectorFieldChoice ordinarySectorKernel b (ordinaryKernel f)).graph :=
  sectorWeightedChoice_graph ordinarySectorKernel b (ordinaryKernel f) (1/2) (by norm_num) (ordinaryTwoInput u)

lemma ccrTwoOutput_outer_graph (b c : Bool) (f g : OneBoson) (u : (shiftedNumberPower Sector 1).domain) :
    (ccrOneOutput c g u,ccrTwoOutput b c f g u) ∈
      (sectorFieldChoice ordinarySectorKernel b (ordinaryKernel f)).graph :=
  sectorWeightedChoice_graph ordinarySectorKernel b (ordinaryKernel f) 0 le_rfl
    (ordinaryRootToZero (ordinaryTwoMiddle c g u))

lemma ccr_norm_on_shifted (f : OneBoson) (u : (shiftedNumberPower Sector 1).domain) :
    ‖ccrOneOutput true f u‖^2 = ‖ccrOneOutput false f u‖^2+‖f‖^2*‖u.val‖^2 := by
  apply ccr_norm_of_graphs f u.val (ccrOneOutput true f u) (ccrOneOutput false f u)
    (ccrTwoOutput false true f f u) (ccrTwoOutput true false f f u)
  · exact ccrOneOutput_graph true f u
  · exact ccrOneOutput_graph false f u
  · exact ccrTwoOutput_outer_graph false true f f u
  · exact ccrTwoOutput_outer_graph true false f f u
  · have hf : ⟪f,f⟫_ℂ = ((‖f‖^2:ℝ):ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      exact (RCLike.ofReal_pow (K := ℂ) ‖f‖ 2).symm
    rw [ccrTwoOutput_mixed,hf,add_comm]

def ccrFiniteNumberInput (v : finiteSectorDomain Sector) : (shiftedNumberPower Sector 1).domain :=
  ⟨v.val,finiteSectorDomain_le Sector (fun n => ((n:ℝ)+1)^1) v.property⟩

lemma ccr_finite_norm (f : OneBoson) (v : finiteSectorDomain Sector) :
    ‖ccrFiniteCreationOutput f v‖^2 = ‖ccrFiniteAnnihilationOutput f v‖^2+‖f‖^2*‖(v:Carrier)‖^2 := by
  have hc : ccrFiniteCreationOutput f v = ccrOneOutput true f (ccrFiniteNumberInput v) := by
    apply (ordinaryCreation f).mem_graph_snd_inj _ (ccrOneOutput_graph true f (ccrFiniteNumberInput v)) rfl
    exact (ordinaryCreation f).mem_graph_iff.mpr ⟨ccrFiniteCreationInput f v,rfl,rfl⟩
  have ha : ccrFiniteAnnihilationOutput f v = ccrOneOutput false f (ccrFiniteNumberInput v) := by
    apply (ordinaryAnnihilation f).mem_graph_snd_inj _ (ccrOneOutput_graph false f (ccrFiniteNumberInput v)) rfl
    exact (ordinaryAnnihilation f).mem_graph_iff.mpr ⟨ccrFiniteAnnihilationInput f v,rfl,rfl⟩
  rw [hc,ha]
  exact ccr_norm_on_shifted f (ccrFiniteNumberInput v)

lemma ordinaryCreation_domain_eq_annihilation (f : OneBoson) :
    (ordinaryCreation f).domain = (ordinaryAnnihilation f).domain :=
  ccr_maximal_domains_from_finite f (ccr_finite_norm f)

lemma ordinaryCreation_norm_identity (f : OneBoson) (u : (ordinaryAnnihilation f).domain)
    (hc : u.val ∈ (ordinaryCreation f).domain) :
    ‖ordinaryCreation f ⟨u.val,hc⟩‖^2 = ‖ordinaryAnnihilation f u‖^2+‖f‖^2*‖u.val‖^2 := by
  obtain ⟨h,hn⟩ := ccr_domains_forward_from_finite f (ccr_finite_norm f) u
  exact hn

lemma ordinaryCreation_norm_lower (f : OneBoson) (u : (ordinaryAnnihilation f).domain)
    (hc : u.val ∈ (ordinaryCreation f).domain) :
    ‖f‖*‖u.val‖ ≤ ‖ordinaryCreation f ⟨u.val,hc⟩‖ := by
  apply (sq_le_sq₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)).mp
  rw [mul_pow,ordinaryCreation_norm_identity f u hc]
  exact le_add_of_nonneg_left (sq_nonneg _)

lemma ordinaryCCR_mixed_graphs (f g : OneBoson) (u : numberOperator.domain) :
    ∃ c a ac ca : Carrier,
      (u.val,c) ∈ (ordinaryCreation g).graph ∧
      (u.val,a) ∈ (ordinaryAnnihilation f).graph ∧
      (c,ac) ∈ (ordinaryAnnihilation f).graph ∧
      (a,ca) ∈ (ordinaryCreation g).graph ∧ ac-ca = ⟪f,g⟫_ℂ • u.val := by
  let v := ccrNumberInput u
  refine ⟨ccrOneOutput true g v,ccrOneOutput false f v,
    ccrTwoOutput false true f g v,ccrTwoOutput true false g f v,
    ccrOneOutput_graph true g v,ccrOneOutput_graph false f v,
    ccrTwoOutput_outer_graph false true f g v,ccrTwoOutput_outer_graph true false g f v,?_⟩
  exact sub_eq_iff_eq_add.mpr (ccrTwoOutput_mixed f g v)

lemma ordinaryCCR_annihilation (f g : OneBoson) (u : numberOperator.domain) :
    ccrTwoOutput false false f g (ccrNumberInput u) = ccrTwoOutput false false g f (ccrNumberInput u) :=
  ccrTwoOutput_annihilation_commute f g (ccrNumberInput u)

lemma ordinaryCCR_creation (f g : OneBoson) (u : numberOperator.domain) :
    ccrTwoOutput true true f g (ccrNumberInput u) = ccrTwoOutput true true g f (ccrNumberInput u) :=
  ccrTwoOutput_creation_commute f g (ccrNumberInput u)


def ccrShiftedCutoff (m : ℕ) (u : (shiftedNumberPower Sector 1).domain) :
    (shiftedNumberPower Sector 1).domain :=
  ⟨cutoff Sector m u.val,scalarDiagonal_cutoff_mem Sector (fun n => ((n:ℝ)+1)^1) m u⟩

lemma ccrTwoOutput_cutoff_tendsto (b c : Bool) (f g : OneBoson)
    (u : (shiftedNumberPower Sector 1).domain) :
    Tendsto (fun m => ccrTwoOutput b c f g (ccrShiftedCutoff m u)) atTop (𝓝 (ccrTwoOutput b c f g u)) := by
  have hz := (continuous_snd.tendsto (u.val,shiftedNumberPower Sector 1 u)).comp
    (scalarDiagonal_cutoff_graph_tendsto Sector (fun n => ((n:ℝ)+1)^1) u)
  change Tendsto (fun m => shiftedNumberPower Sector 1 (ccrShiftedCutoff m u)) atTop
    (𝓝 (shiftedNumberPower Sector 1 u)) at hz
  have hd : Tendsto (fun m => shiftedNumberPower Sector 1 (ccrShiftedCutoff m u-u)) atTop (𝓝 0) := by
    have he (m : ℕ) : shiftedNumberPower Sector 1 (ccrShiftedCutoff m u-u) =
        shiftedNumberPower Sector 1 (ccrShiftedCutoff m u)-shiftedNumberPower Sector 1 u :=
      (shiftedNumberPower Sector 1).toFun.map_sub _ _
    simp_rw [he]
    simpa only [sub_self] using hz.sub_const (shiftedNumberPower Sector 1 u)
  have hb : Tendsto (fun m => (Real.sqrt 2*‖f‖*‖g‖)*‖shiftedNumberPower Sector 1 (ccrShiftedCutoff m u-u)‖)
      atTop (𝓝 0) := by
    simpa only [norm_zero,mul_zero] using hd.norm.const_mul (Real.sqrt 2*‖f‖*‖g‖)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) _ hb
  intro m
  rw [← ccrTwoOutput_sub]
  exact ccrTwoOutput_norm b c f g (ccrShiftedCutoff m u-u)


lemma ordinaryCCR_annihilation_graphs (f g : OneBoson) (u : numberOperator.domain) :
    ∃ a b ab ba : Carrier,
      (u.val,a) ∈ (ordinaryAnnihilation g).graph ∧
      (u.val,b) ∈ (ordinaryAnnihilation f).graph ∧
      (a,ab) ∈ (ordinaryAnnihilation f).graph ∧
      (b,ba) ∈ (ordinaryAnnihilation g).graph ∧ ab = ba := by
  let v := ccrNumberInput u
  exact ⟨ccrOneOutput false g v,ccrOneOutput false f v,
    ccrTwoOutput false false f g v,ccrTwoOutput false false g f v,
    ccrOneOutput_graph false g v,ccrOneOutput_graph false f v,
    ccrTwoOutput_outer_graph false false f g v,ccrTwoOutput_outer_graph false false g f v,
    ccrTwoOutput_annihilation_commute f g v⟩

lemma ordinaryCCR_creation_graphs (f g : OneBoson) (u : numberOperator.domain) :
    ∃ a b ab ba : Carrier,
      (u.val,a) ∈ (ordinaryCreation g).graph ∧
      (u.val,b) ∈ (ordinaryCreation f).graph ∧
      (a,ab) ∈ (ordinaryCreation f).graph ∧
      (b,ba) ∈ (ordinaryCreation g).graph ∧ ab = ba := by
  let v := ccrNumberInput u
  exact ⟨ccrOneOutput true g v,ccrOneOutput true f v,
    ccrTwoOutput true true f g v,ccrTwoOutput true true g f v,
    ccrOneOutput_graph true g v,ccrOneOutput_graph true f v,
    ccrTwoOutput_outer_graph true true f g v,ccrTwoOutput_outer_graph true true g f v,
    ccrTwoOutput_creation_commute f g v⟩

def ordinaryCreationCommonInput (f : OneBoson) (u : (ordinaryAnnihilation f).domain) :
    (ordinaryCreation f).domain :=
  ⟨u.val,by rw [ordinaryCreation_domain_eq_annihilation]; exact u.property⟩

lemma ordinaryCreation_common_norm (f : OneBoson) (u : (ordinaryAnnihilation f).domain) :
    ‖ordinaryCreation f (ordinaryCreationCommonInput f u)‖^2 =
      ‖ordinaryAnnihilation f u‖^2+‖f‖^2*‖u.val‖^2 :=
  ordinaryCreation_norm_identity f u (ordinaryCreationCommonInput f u).property

lemma ordinaryCreation_common_lower (f : OneBoson) (u : (ordinaryAnnihilation f).domain) :
    ‖f‖*‖u.val‖ ≤ ‖ordinaryCreation f (ordinaryCreationCommonInput f u)‖ :=
  ordinaryCreation_norm_lower f u (ordinaryCreationCommonInput f u).property

end GW.Fock
