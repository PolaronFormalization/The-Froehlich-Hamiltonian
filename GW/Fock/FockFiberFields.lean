module
public import GW.Fock.FockFieldDefinition
public import GW.Fock.FockWeightedFields
public import GW.Fock.ProductDensity
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal InnerProductSpace
namespace GW.Fock

abbrev FiberKernelBochner := Lp OneBoson 2 (volume : Measure GW.Space)

def fiberKernelRep (F : GW.Space → OneBoson) (u : ElectronL2) (x : GW.Space) : OneBoson :=
  u x • F x

lemma fiberKernelRep_memLp (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M) (u : ElectronL2) :
    MemLp (fiberKernelRep F u) 2 (volume : Measure GW.Space) := by
  apply (Lp.memLp u).of_le_mul (c := M) ((Lp.aestronglyMeasurable u).smul hF)
  filter_upwards [hM] with x hx
  change ‖u x • F x‖ ≤ M * ‖u x‖
  rw [norm_smul,mul_comm M]
  exact mul_le_mul_of_nonneg_left hx (norm_nonneg _)

def fiberKernelClass (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M) (u : ElectronL2) : FiberKernelBochner :=
  (fiberKernelRep_memLp F hF hM u).toLp (fiberKernelRep F u)

lemma fiberKernelClass_ae (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M) (u : ElectronL2) :
    fiberKernelClass F hF hM u =ᵐ[(volume : Measure GW.Space)] fiberKernelRep F u :=
  MemLp.coeFn_toLp _

lemma fiberKernelClass_norm (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M) (u : ElectronL2) :
    ‖fiberKernelClass F hF hM u‖ ≤ M * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hM,fiberKernelClass_ae F hF hM u] with x hx hy
  rw [hy]
  change ‖u x • F x‖ ≤ _
  rw [norm_smul,mul_comm M]
  exact mul_le_mul_of_nonneg_left hx (norm_nonneg _)

def fiberKernelLinear (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M) : ElectronL2 →ₗ[ℂ] FiberKernelBochner where
  toFun := fiberKernelClass F hF hM
  map_add' u v := by
    apply Lp.ext
    filter_upwards [fiberKernelClass_ae F hF hM (u+v),fiberKernelClass_ae F hF hM u,
      fiberKernelClass_ae F hF hM v,Lp.coeFn_add u v,
      Lp.coeFn_add (fiberKernelClass F hF hM u) (fiberKernelClass F hF hM v)] with x h₁ h₂ h₃ h₄ h₅
    change fiberKernelClass F hF hM (u+v) x = (fiberKernelClass F hF hM u+fiberKernelClass F hF hM v) x
    rw [h₁,h₅,Pi.add_apply,h₂,h₃]
    change (u+v) x • F x = u x • F x + v x • F x
    rw [show (u+v) x = u x+v x from h₄,add_smul]
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [fiberKernelClass_ae F hF hM (c • u),fiberKernelClass_ae F hF hM u,
      Lp.coeFn_smul c u,Lp.coeFn_smul c (fiberKernelClass F hF hM u)] with x h₁ h₂ h₃ h₄
    change fiberKernelClass F hF hM (c • u) x = (c • fiberKernelClass F hF hM u) x
    rw [h₁,h₄,Pi.smul_apply,h₂]
    change (c • u) x • F x = c • (u x • F x)
    rw [show (c • u) x = c*u x from h₃,mul_smul]

def fiberKernel (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M) : BosonKernel ElectronL2 :=
  let U : FiberKernelBochner ≃ₗᵢ[ℂ] ElectronBosonProduct := productUnitary volume volume
  let W := U.trans kernelProductIdentification.symm
  W.toLinearIsometry.toContinuousLinearMap.comp
    ((fiberKernelLinear F hF hM).mkContinuous M (fiberKernelClass_norm F hF hM))

lemma fiberKernel_product (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M) (u : ElectronL2) :
    kernelProductIdentification (fiberKernel F hF hM u) =
      productUnitary volume volume (fiberKernelClass F hF hM u) :=
  kernelProductIdentification.apply_symm_apply _

lemma fiberKernel_norm (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M) :
    ‖fiberKernel F hF hM‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_bound _ hM0
  intro u
  rw [← kernelProductIdentification.norm_map (fiberKernel F hF hM u),fiberKernel_product,
    LinearIsometryEquiv.norm_map]
  exact fiberKernelClass_norm F hF hM u

section KernelAddition
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {S : ℕ → Type*} [∀ n, NormedAddCommGroup (S n)] [∀ n, InnerProductSpace ℂ (S n)]
  (R : ∀ n, S n ≃ₗᵢ[ℂ] kernelFixed (E := E) n)

lemma fiberSectorCreation_add (F G : BosonKernel E) (n : ℕ) (u : S n) :
    sectorCreation R (F+G) n u = sectorCreation R F n u + sectorCreation R G n u := by
  have hr : kernelCreationRaw (F+G) n = kernelCreationRaw F n + kernelCreationRaw G n := by
    unfold kernelCreationRaw amplify
    rw [ContinuousLinearMap.add_compLpL,ContinuousLinearMap.comp_add]
  have h (v : kernelFixed (E := E) n) : kernelCreation (F+G) n v =
      kernelCreation F n v + kernelCreation G n v := by
    apply Subtype.ext
    rw [kernelCreation_value]
    change _ = (kernelCreation F n v : KernelSector E (n+1)) + (kernelCreation G n v : KernelSector E (n+1))
    rw [kernelCreation_value,kernelCreation_value,hr,ContinuousLinearMap.add_apply,map_add,smul_add]
  apply (R (n+1)).injective
  change R (n+1) ((R (n+1)).symm (kernelCreation (F+G) n (R n u))) =
    R (n+1) ((R (n+1)).symm (kernelCreation F n (R n u))+(R (n+1)).symm (kernelCreation G n (R n u)))
  rw [map_add,LinearIsometryEquiv.apply_symm_apply,LinearIsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.apply_symm_apply,h]

lemma fiberSectorAnnihilation_add (F G : BosonKernel E) (n : ℕ) (v : S (n+1)) :
    sectorAnnihilation R (F+G) n v = sectorAnnihilation R F n v + sectorAnnihilation R G n v := by
  apply ext_inner_left ℂ
  intro u
  rw [inner_add_right,← sectorCreation_pairing,← sectorCreation_pairing,← sectorCreation_pairing,
    fiberSectorCreation_add,inner_add_left]

end KernelAddition

abbrev FiberRootDomain := NumberWeightedDomain Sector (1/2) (by norm_num)

def fiberOrdinaryRootInput (u : FiberRootDomain) : (shiftedNumberPower Sector (1/2)).domain := u

lemma fiberOrdinaryRoot_norm (u : FiberRootDomain) :
    ‖shiftedNumberPower Sector (1/2) (fiberOrdinaryRootInput u)‖ = ‖u‖ :=
  (GW.Spaces.weightedDomain_norm (numberWeightedGraph Sector (1/2) (by norm_num)) u).symm

def fiberOrdinaryRootInputUnshifted (u : FiberRootDomain) : (numberPower Sector (1/2)).domain :=
  ⟨(fiberOrdinaryRootInput u).val,by
    rw [numberPower_domain_eq Sector (1/2) (by norm_num)]
    exact (fiberOrdinaryRootInput u).property⟩

lemma fiberOrdinaryRoot_unshifted_norm_le (u : FiberRootDomain) :
    ‖numberPower Sector (1/2) (fiberOrdinaryRootInputUnshifted u)‖ ≤ ‖u‖ := by
  rw [← fiberOrdinaryRoot_norm u]
  apply lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0)
  intro n
  rw [numberPower_apply Sector (1/2) (by norm_num),shiftedNumberPower_apply,norm_smul,norm_smul,
    Complex.norm_real,Complex.norm_real]
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
  have hm : 0 ≤ (n:ℝ)+1 := by positivity
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hn _),Real.norm_of_nonneg (Real.rpow_nonneg hm _)]
  change (n:ℝ)^(1/2:ℝ)*‖(fiberOrdinaryRootInput u).val n‖ ≤ ((n:ℝ)+1)^(1/2:ℝ)*‖(fiberOrdinaryRootInput u).val n‖
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hn (by linarith) (by norm_num)) (norm_nonneg _)

def fiberOrdinaryCreator (f : OneBoson) (u : FiberRootDomain) : Carrier :=
  ordinaryCreation f ⟨(fiberOrdinaryRootInput u).val,
    creation_mem_shiftedRoot ordinarySectorKernel (ordinaryKernel f) (fiberOrdinaryRootInput u)⟩

def fiberOrdinaryAnnihilator (f : OneBoson) (u : FiberRootDomain) : Carrier :=
  ordinaryAnnihilation f (ordinaryAnnihilationRootInput f (fiberOrdinaryRootInputUnshifted u))

lemma fiberOrdinaryCreator_bound (f : OneBoson) (u : FiberRootDomain) :
    ‖fiberOrdinaryCreator f u‖ ≤ ‖f‖ * ‖u‖ := by
  have h := creation_root_norm ordinarySectorKernel (ordinaryKernel f) (fiberOrdinaryRootInput u)
  change ‖fiberOrdinaryCreator f u‖ ≤ ‖ordinaryKernel f‖ * ‖shiftedNumberPower Sector (1/2) (fiberOrdinaryRootInput u)‖ at h
  rw [show ‖ordinaryKernel f‖ = ‖f‖ from ContinuousLinearMap.norm_toSpanSingleton f,fiberOrdinaryRoot_norm] at h
  exact h

lemma fiberOrdinaryAnnihilator_bound (f : OneBoson) (u : FiberRootDomain) :
    ‖fiberOrdinaryAnnihilator f u‖ ≤ ‖f‖ * ‖u‖ := by
  have h := annihilation_root_norm ordinarySectorKernel (ordinaryKernel f) (fiberOrdinaryRootInputUnshifted u)
  change ‖fiberOrdinaryAnnihilator f u‖ ≤ ‖ordinaryKernel f‖ * ‖numberPower Sector (1/2) (fiberOrdinaryRootInputUnshifted u)‖ at h
  rw [show ‖ordinaryKernel f‖ = ‖f‖ from ContinuousLinearMap.norm_toSpanSingleton f] at h
  exact h.trans (mul_le_mul_of_nonneg_left (fiberOrdinaryRoot_unshifted_norm_le u) (norm_nonneg _))

lemma fiberOrdinaryCreator_add_kernel (f g : OneBoson) (u : FiberRootDomain) :
    fiberOrdinaryCreator (f+g) u = fiberOrdinaryCreator f u + fiberOrdinaryCreator g u := by
  have hk : ordinaryKernel (f+g) = ordinaryKernel f+ordinaryKernel g := by
    apply ContinuousLinearMap.ext
    intro c
    change c • (f+g) = c • f+c • g
    exact smul_add c f g
  apply lp.ext
  funext n
  cases n with
  | zero => simp only [fiberOrdinaryCreator, ordinaryCreation_zero, lp.coeFn_add,Pi.add_apply,zero_add]
  | succ n =>
    simp only [fiberOrdinaryCreator,lp.coeFn_add,Pi.add_apply,ordinaryCreation_succ]
    rw [hk,fiberSectorCreation_add]

lemma fiberOrdinaryAnnihilator_add_kernel (f g : OneBoson) (u : FiberRootDomain) :
    fiberOrdinaryAnnihilator (f+g) u = fiberOrdinaryAnnihilator f u + fiberOrdinaryAnnihilator g u := by
  have hk : ordinaryKernel (f+g) = ordinaryKernel f+ordinaryKernel g := by
    apply ContinuousLinearMap.ext
    intro c
    change c • (f+g) = c • f+c • g
    exact smul_add c f g
  apply lp.ext
  funext n
  simp only [fiberOrdinaryAnnihilator,lp.coeFn_add,Pi.add_apply,ordinaryAnnihilation_apply]
  rw [hk,fiberSectorAnnihilation_add]
  rfl

lemma fiberOrdinaryCreator_add_vector (f : OneBoson) (u v : FiberRootDomain) :
    fiberOrdinaryCreator f (u+v) = fiberOrdinaryCreator f u + fiberOrdinaryCreator f v := by
  let A := ordinaryCreation f
  let w (u : FiberRootDomain) : A.domain := ⟨(fiberOrdinaryRootInput u).val,
    creation_mem_shiftedRoot ordinarySectorKernel (ordinaryKernel f) (fiberOrdinaryRootInput u)⟩
  have he : w (u+v) = w u + w v := Subtype.ext rfl
  change A (w (u+v)) = A (w u)+A (w v)
  rw [he]
  exact A.toFun.map_add _ _

lemma fiberOrdinaryAnnihilator_add_vector (f : OneBoson) (u v : FiberRootDomain) :
    fiberOrdinaryAnnihilator f (u+v) = fiberOrdinaryAnnihilator f u + fiberOrdinaryAnnihilator f v := by
  let A := ordinaryAnnihilation f
  let w (u : FiberRootDomain) : A.domain := ordinaryAnnihilationRootInput f (fiberOrdinaryRootInputUnshifted u)
  have he : w (u+v) = w u + w v := Subtype.ext rfl
  change A (w (u+v)) = A (w u)+A (w v)
  rw [he]
  exact A.toFun.map_add _ _

lemma fiberBilinear_difference {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    (B : X → Y → Z) (hx : ∀ x x' y, B (x+x') y = B x y+B x' y)
    (hy : ∀ x y y', B x (y+y') = B x y+B x y') (x x' : X) (y y' : Y) :
    B x y-B x' y' = B (x-x') y + B x' (y-y') := by
  have h₁ := hx (x-x') x' y
  have h₂ := hy x' (y-y') y'
  rw [sub_add_cancel] at h₁ h₂
  rw [h₁,h₂]
  abel

lemma fiberBilinear_continuous {X Y Z : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedAddCommGroup Z] (B : X → Y → Z)
    (hx : ∀ x x' y, B (x+x') y = B x y+B x' y)
    (hy : ∀ x y y', B x (y+y') = B x y+B x y') (hb : ∀ x y, ‖B x y‖ ≤ ‖x‖ * ‖y‖) :
    Continuous (fun p : X × Y => B p.1 p.2) := by
  apply continuous_iff_seqContinuous.mpr
  intro f p hf
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hx₁ : Tendsto (fun n => (f n).1) atTop (𝓝 p.1) := continuous_fst.continuousAt.tendsto.comp hf
  have hy₁ : Tendsto (fun n => (f n).2) atTop (𝓝 p.2) := continuous_snd.continuousAt.tendsto.comp hf
  have h0x := tendsto_iff_norm_sub_tendsto_zero.mp hx₁
  have h0y := tendsto_iff_norm_sub_tendsto_zero.mp hy₁
  have hh : Tendsto (fun n => ‖(f n).1-p.1‖*‖(f n).2‖ + ‖p.1‖*‖(f n).2-p.2‖) atTop (𝓝 0) := by
    simpa only [zero_mul,mul_zero,add_zero] using ((h0x.mul hy₁.norm).add (h0y.const_mul ‖p.1‖))
  apply squeeze_zero (fun _ => norm_nonneg _) _ hh
  intro n
  change ‖B (f n).1 (f n).2 - B p.1 p.2‖ ≤ _
  rw [fiberBilinear_difference B hx hy]
  exact (norm_add_le _ _).trans (add_le_add (hb _ _) (hb _ _))

lemma fiberOrdinaryCreator_continuous :
    Continuous (fun p : OneBoson × FiberRootDomain => fiberOrdinaryCreator p.1 p.2) :=
  fiberBilinear_continuous fiberOrdinaryCreator fiberOrdinaryCreator_add_kernel
    fiberOrdinaryCreator_add_vector fiberOrdinaryCreator_bound

lemma fiberOrdinaryAnnihilator_continuous :
    Continuous (fun p : OneBoson × FiberRootDomain => fiberOrdinaryAnnihilator p.1 p.2) :=
  fiberBilinear_continuous fiberOrdinaryAnnihilator fiberOrdinaryAnnihilator_add_kernel
    fiberOrdinaryAnnihilator_add_vector fiberOrdinaryAnnihilator_bound

abbrev FiberPhysicalRoot := PhysicalNumberDomain (1/2) (by norm_num)

def fiberRootRepresentative (u : FiberPhysicalRoot) : Lp FiberRootDomain 2 (volume : Measure GW.Space) :=
  (physicalNumberGraphBochnerUnitary (1/2) (by norm_num)).symm u

def fiberPointwiseCreator (F : GW.Space → OneBoson) (u : FiberPhysicalRoot) (x : GW.Space) : Carrier :=
  fiberOrdinaryCreator (F x) (fiberRootRepresentative u x)

def fiberPointwiseAnnihilator (F : GW.Space → OneBoson) (u : FiberPhysicalRoot) (x : GW.Space) : Carrier :=
  fiberOrdinaryAnnihilator (F x) (fiberRootRepresentative u x)

lemma fiberPointwiseCreator_memLp (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M) (u : FiberPhysicalRoot) :
    MemLp (fiberPointwiseCreator F u) 2 (volume : Measure GW.Space) := by
  apply (Lp.memLp (fiberRootRepresentative u)).of_le_mul (c := M)
    (fiberOrdinaryCreator_continuous.comp_aestronglyMeasurable
      (hF.prodMk (Lp.aestronglyMeasurable (fiberRootRepresentative u))))
  filter_upwards [hM] with x hx
  exact (fiberOrdinaryCreator_bound _ _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

lemma fiberPointwiseAnnihilator_memLp (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M) (u : FiberPhysicalRoot) :
    MemLp (fiberPointwiseAnnihilator F u) 2 (volume : Measure GW.Space) := by
  apply (Lp.memLp (fiberRootRepresentative u)).of_le_mul (c := M)
    (fiberOrdinaryAnnihilator_continuous.comp_aestronglyMeasurable
      (hF.prodMk (Lp.aestronglyMeasurable (fiberRootRepresentative u))))
  filter_upwards [hM] with x hx
  exact (fiberOrdinaryAnnihilator_bound _ _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

lemma fiberKernel_tensor_product (f : OneBoson) (γ : ElectronL2) :
    kernelProductIdentification (tensorEmbedding (volume : Measure GW.Space) f γ) =
      productFunction (volume : Measure GW.Space) (volume : Measure GW.Space) γ f := by
  change swapProduct volume volume (productUnitary volume volume (tensorEmbedding volume f γ)) = _
  rw [productUnitary_tensor]
  apply Lp.ext
  filter_upwards [swapProduct_ae volume volume (productFunction volume volume f γ),
    (Measure.measurePreserving_swap (μ := (volume : Measure GW.Space)) (ν := (volume : Measure GW.Space))).quasiMeasurePreserving.ae
      (productFunction_ae volume volume f γ),
    productFunction_ae volume volume γ f] with p h₁ h₂ h₃
  rw [h₁,h₃]
  change productFunction volume volume f γ p.swap = γ p.1 • f p.2
  have h : productFunction volume volume f γ p.swap = f p.2 • γ p.1 := h₂
  rw [h,smul_eq_mul,smul_eq_mul,mul_comm]

lemma fiberKernelClass_pair (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M)
    (f : OneBoson) (γ η : ElectronL2) :
    ⟪tensorEmbedding (E := OneBoson) (volume : Measure GW.Space) η f,fiberKernelClass F hF hM γ⟫_ℂ =
      ∫ x, ⟪η x • f,γ x • F x⟫_ℂ ∂(volume : Measure GW.Space) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [tensorEmbedding_ae (E := OneBoson) (volume : Measure GW.Space) η f,
    fiberKernelClass_ae F hF hM γ] with x h₁ h₂
  rw [h₁,h₂]
  rfl

lemma fiberKernel_pair_tensor (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M)
    (f : OneBoson) (γ η : ElectronL2) :
    ⟪tensorEmbedding (volume : Measure GW.Space) f η,fiberKernel F hF hM γ⟫_ℂ =
      ∫ x, ⟪η x • f,γ x • F x⟫_ℂ ∂(volume : Measure GW.Space) := by
  let μ : Measure GW.Space := volume
  let U : FiberKernelBochner ≃ₗᵢ[ℂ] ElectronBosonProduct := productUnitary μ μ
  let y : FiberKernelBochner := tensorEmbedding (E := OneBoson) μ η f
  let z : FiberKernelBochner := fiberKernelClass F hF hM γ
  have ht : U y = productFunction μ μ η f := productUnitary_tensor μ μ η f
  have hz : kernelProductIdentification (fiberKernel F hF hM γ) = U z := fiberKernel_product F hF hM γ
  have hy : kernelProductIdentification (tensorEmbedding μ f η) = U y :=
    (fiberKernel_tensor_product f η).trans ht.symm
  calc
    _ = ⟪kernelProductIdentification (tensorEmbedding μ f η),
      kernelProductIdentification (fiberKernel F hF hM γ)⟫_ℂ := (kernelProductIdentification.inner_map_map _ _).symm
    _ = ⟪U y,U z⟫_ℂ := congrArg₂ (fun a b : ElectronBosonProduct => ⟪a,b⟫_ℂ) hy hz
    _ = ⟪y,z⟫_ℂ := U.inner_map_map _ _
    _ = _ := fiberKernelClass_pair F hF hM f γ η

lemma fiberProductFunction_swap (μ ν : Measure GW.Space) [SigmaFinite μ] [SigmaFinite ν]
    (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    swapProduct μ ν (productFunction μ ν f g) = productFunction ν μ g f := by
  apply Lp.ext
  filter_upwards [swapProduct_ae μ ν (productFunction μ ν f g),
    (Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae
      (productFunction_ae μ ν f g),productFunction_ae ν μ g f] with p h₁ h₂ h₃
  change swapProduct μ ν (productFunction μ ν f g) p = productFunction ν μ g f p
  rw [h₁,h₃]
  have h : productFunction μ ν f g p.swap = f p.2 • g p.1 := h₂
  rw [h,smul_eq_mul,smul_eq_mul,mul_comm]

set_option maxHeartbeats 1500000 in
lemma fiberPhysicalSectorKernel_tensor_positive (n : ℕ) (γ : ElectronL2) (u : Sector (n+1)) :
    (physicalSectorKernel (n+1) ((ContinuousLinearMap.toSpanSingleton ℂ u).compLp γ) :
      KernelSector ElectronL2 (n+1)) =
        tensorEmbedding (sectorMeasure (n+1)) (sectorInclusion n u) γ := by
  let ν := sectorMeasure (n+1)
  let μ : Measure GW.Space := volume
  let I : Sector (n+1) →L[ℂ] AmbientSector (n+1) := (sectorInclusion n).toContinuousLinearMap
  let P := physicalKernelProduct (n+1)
  have hI : amplify μ I ((ContinuousLinearMap.toSpanSingleton ℂ u).compLp γ) =
      tensorEmbedding μ γ (I u) := by
    change amplify μ I (tensorEmbedding μ γ u) = tensorEmbedding μ γ (I u)
    exact amplify_tensor μ I γ u
  change P (productUnitary μ ν (amplify μ I ((ContinuousLinearMap.toSpanSingleton ℂ u).compLp γ))) = _
  rw [hI,productUnitary_tensor]
  change (productUnitary ν μ).symm (swapProduct μ ν (productFunction μ ν γ (I u))) =
    tensorEmbedding ν (I u) γ
  have he : swapProduct μ ν (productFunction μ ν γ (I u)) = productFunction ν μ (I u) γ := by
    apply Lp.ext
    filter_upwards [swapProduct_ae μ ν (productFunction μ ν γ (I u)),
      (Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae
        (productFunction_ae μ ν γ (I u)),productFunction_ae ν μ (I u) γ] with p h₁ h₂ h₃
    rw [h₁,h₃]
    have h : productFunction μ ν γ (I u) p.swap = γ p.2 • I u p.1 := h₂
    rw [h,smul_eq_mul,smul_eq_mul,mul_comm]
  rw [he,← productUnitary_tensor,LinearIsometryEquiv.symm_apply_apply]

lemma fiberPhysicalSectorKernel_tensor_vacuum (γ : ElectronL2) (u : ℂ) :
    (physicalSectorKernel 0 ((ContinuousLinearMap.toSpanSingleton ℂ u).compLp γ) : KernelSector ElectronL2 0) =
      kernelVacuum ((u : ℂ) • γ) := by
  change kernelVacuum ((ContinuousLinearMap.toSpanSingleton ℂ u).compLp γ) = _
  congr 1
  apply Lp.ext
  filter_upwards [(ContinuousLinearMap.toSpanSingleton ℂ u).coeFn_compLp γ,Lp.coeFn_smul (u : ℂ) γ] with x h₁ h₂
  rw [h₁,h₂]
  change γ x * u = u * γ x
  exact mul_comm _ _

lemma fiberTensor_inner {X E : Type*} [MeasurableSpace X] (μ : Measure X)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v u : Lp ℂ 2 μ) (η γ : E) :
    ⟪tensorEmbedding μ v η,tensorEmbedding μ u γ⟫_ℂ = ⟪v,u⟫_ℂ * ⟪η,γ⟫_ℂ := by
  rw [L2.inner_def,L2.inner_def,← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [tensorEmbedding_ae μ v η,tensorEmbedding_ae μ u γ] with z h₁ h₂
  rw [h₁,h₂,inner_smul_left,inner_smul_right]
  simp only [RCLike.inner_apply']
  ring

lemma fiberKernelCreationRaw_pair_generic {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (K : BosonKernel E)
    (n : ℕ) (v u : AmbientSector n) (f : Lp E 2 (volume : Measure GW.Space)) (γ : E) :
    ⟪(kernelSplit (E := E) n).symm (tensorEmbedding (sectorMeasure n) v f),
      kernelCreationRaw K n (tensorEmbedding (sectorMeasure n) u γ)⟫_ℂ =
      ⟪v,u⟫_ℂ * ⟪f,K γ⟫_ℂ := by
  change ⟪(kernelSplit (E := E) n).symm _,
    (kernelSplit (E := E) n).symm (amplify (sectorMeasure n) K (tensorEmbedding (sectorMeasure n) u γ))⟫_ℂ = _
  rw [(kernelSplit (E := E) n).symm.inner_map_map,amplify_tensor,fiberTensor_inner]

lemma fiberKernelCreationRaw_pair_tensor (F : GW.Space → OneBoson)
    (hF : AEStronglyMeasurable F volume) {M : ℝ}
    (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M)
    (n : ℕ) (v u : AmbientSector n) (f : OneBoson) (η γ : ElectronL2) :
    ⟪(kernelSplit (E := ElectronL2) n).symm
        (tensorEmbedding (sectorMeasure n) v (tensorEmbedding volume f η)),
      kernelCreationRaw (fiberKernel F hF hM) n
        (tensorEmbedding (sectorMeasure n) u γ)⟫_ℂ =
      ⟪v,u⟫_ℂ * ∫ x, ⟪η x • f,γ x • F x⟫_ℂ ∂(volume : Measure GW.Space) := by
  calc
    _ = ⟪v,u⟫_ℂ * ⟪tensorEmbedding volume f η,fiberKernel F hF hM γ⟫_ℂ :=
      fiberKernelCreationRaw_pair_generic (fiberKernel F hF hM) n v u _ γ
    _ = _ := congrArg (fun z : ℂ => ⟪v,u⟫_ℂ*z) (fiberKernel_pair_tensor F hF hM f γ η)

lemma fiberKernelSymmetrizer_average {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (n : ℕ) (z : KernelSector E n) :
    kernelSymmetrizer n z = ((n.factorial : ℂ)⁻¹) •
      ∑ τ : Equiv.Perm (Fin n), kernelPermutation n τ z := by
  rw [kernelSymmetrizer,groupAverage_apply]
  simp only [Fintype.card_perm,Fintype.card_fin]
  rfl

set_option maxHeartbeats 1500000 in
set_option backward.isDefEq.respectTransparency.types false in
lemma fiberPhysicalKernelProduct_symmetrizer (n : ℕ)
    (z : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure n))) :
    physicalKernelProduct n (productSymmetrizer volume n z) =
      kernelSymmetrizer n (physicalKernelProduct n z) := by
  rw [productSymmetrizer_average,map_smul,map_sum,fiberKernelSymmetrizer_average]
  congr 1
  apply Finset.sum_congr rfl
  intro τ _
  exact physicalKernelProduct_permutation n τ z

set_option maxHeartbeats 1500000 in
set_option backward.isDefEq.respectTransparency.types false in
lemma fiberPhysicalKernelProduct_tensor (n : ℕ) (γ : ElectronL2) (u : AmbientSector n) :
    physicalKernelProduct n (productFunction volume (sectorMeasure n) γ u) =
      tensorEmbedding (sectorMeasure n) u γ := by
  change (productUnitary (sectorMeasure n) volume).symm
    (swapProduct volume (sectorMeasure n) (productFunction volume (sectorMeasure n) γ u)) = _
  have he : swapProduct volume (sectorMeasure n) (productFunction volume (sectorMeasure n) γ u) =
      productFunction (sectorMeasure n) volume u γ := by
    apply Lp.ext
    filter_upwards [swapProduct_ae volume (sectorMeasure n) (productFunction volume (sectorMeasure n) γ u),
      (Measure.measurePreserving_swap (μ := sectorMeasure n) (ν := (volume : Measure GW.Space))).quasiMeasurePreserving.ae
        (productFunction_ae volume (sectorMeasure n) γ u),productFunction_ae (sectorMeasure n) volume u γ] with p h₁ h₂ h₃
    rw [h₁,h₃]
    have h : productFunction volume (sectorMeasure n) γ u p.swap = γ p.2 • u p.1 := h₂
    rw [h,smul_eq_mul,smul_eq_mul,mul_comm]
  rw [he,← productUnitary_tensor,LinearIsometryEquiv.symm_apply_apply]

lemma fiberVectorPullback_tensor {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {μ : Measure X} {ν : Measure Y} (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν)
    (f : Lp ℂ 2 ν) (γ : E) :
    vectorPullback e he (tensorEmbedding ν f γ) =
      tensorEmbedding μ (vectorPullback e he f) γ := by
  apply Lp.ext
  filter_upwards [vectorPullback_ae e he (tensorEmbedding ν f γ),
    he.quasiMeasurePreserving.ae (tensorEmbedding_ae ν f γ),
    tensorEmbedding_ae μ (vectorPullback e he f) γ,vectorPullback_ae e he f] with x h₁ h₂ h₃ h₄
  rw [h₁,h₂,h₃,h₄]

set_option maxHeartbeats 1200000 in
lemma fiberKernelSplit_prepend_tensor {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (n : ℕ) (f : OneBoson) (u : AmbientSector n) (γ : E) :
    kernelSplit (E := E) n
      (tensorEmbedding (sectorMeasure (n+1)) (prependProduct n f u) γ) =
        tensorEmbedding (sectorMeasure n) u (tensorEmbedding volume f γ) := by
  let μ : Measure GW.Space := volume
  let ν := sectorMeasure n
  let e := (splitCoordinates n 0).symm
  have he := splitCoordinates_inverse_preserving n 0
  have hs : vectorPullback e he (prependProduct n f u) = productFunction μ ν f u := by
    change splitUnitary n 0 (prependProduct n f u) = _
    exact (splitUnitary n 0).apply_symm_apply _
  apply (productUnitary ν μ).injective
  change productUnitary ν μ ((productUnitary ν μ).symm
    (swapProduct μ ν (vectorPullback e he (tensorEmbedding (sectorMeasure (n+1)) (prependProduct n f u) γ)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply,fiberVectorPullback_tensor,hs,productUnitary_tensor]
  apply Lp.ext
  have hswap : MeasurePreserving (Prod.swap : Coordinates n × GW.Space → GW.Space × Coordinates n)
      (ν.prod μ) (μ.prod ν) := Measure.measurePreserving_swap
  filter_upwards [swapProduct_ae μ ν (tensorEmbedding (μ.prod ν) (productFunction μ ν f u) γ),
    hswap.quasiMeasurePreserving.ae (tensorEmbedding_ae (μ.prod ν) (productFunction μ ν f u) γ),
    hswap.quasiMeasurePreserving.ae (productFunction_ae μ ν f u),
    productFunction_ae ν μ u (tensorEmbedding μ f γ),
    (Measure.quasiMeasurePreserving_snd (μ := ν) (ν := μ)).ae (tensorEmbedding_ae μ f γ)] with p h₁ h₂ h₃ h₄ h₅
  rw [h₁,h₂,h₃,h₄,h₅]
  simp only [smul_eq_mul,smul_smul,mul_comm]
  rfl

lemma fiberProduct_inner {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (f g : Lp ℂ 2 μ) (v u : Lp E 2 ν) :
    ⟪productFunction μ ν f v,productFunction μ ν g u⟫_ℂ = ⟪f,g⟫_ℂ * ⟪v,u⟫_ℂ := by
  have he := (productUnitary (E := E) μ ν).inner_map_map
    (tensorEmbedding μ f v) (tensorEmbedding μ g u)
  rw [productUnitary_tensor,productUnitary_tensor,fiberTensor_inner] at he
  exact he

lemma fiberPrepend_inner (n : ℕ) (f g : OneBoson) (v u : AmbientSector n) :
    ⟪prependProduct n f v,prependProduct n g u⟫_ℂ = ⟪v,u⟫_ℂ * ⟪f,g⟫_ℂ := by
  change ⟪(splitUnitary n 0).symm (productFunction volume (sectorMeasure n) f v),
    (splitUnitary n 0).symm (productFunction volume (sectorMeasure n) g u)⟫_ℂ = _
  rw [(splitUnitary n 0).symm.inner_map_map,fiberProduct_inner,mul_comm]

set_option maxHeartbeats 1200000 in
lemma fiberPhysicalRawCreation_pair (F : GW.Space → OneBoson)
    (hF : AEStronglyMeasurable F volume) {M : ℝ}
    (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M)
    (n : ℕ) (v u : AmbientSector n) (f : OneBoson) (η γ : ElectronL2) :
    ⟪physicalKernelProduct (n+1) (productFunction volume (sectorMeasure (n+1)) η (prependProduct n f v)),
      kernelCreationRaw (fiberKernel F hF hM) n (tensorEmbedding (sectorMeasure n) u γ)⟫_ℂ =
      ⟪v,u⟫_ℂ * ∫ x, ⟪η x • f,γ x • F x⟫_ℂ ∂(volume : Measure GW.Space) := by
  have ht := fiberPhysicalKernelProduct_tensor (n+1) η (prependProduct n f v)
  have hs := fiberKernelSplit_prepend_tensor n f v η
  have he : tensorEmbedding (sectorMeasure (n+1)) (prependProduct n f v) η =
      (kernelSplit (E := ElectronL2) n).symm
        (tensorEmbedding (sectorMeasure n) v (tensorEmbedding volume f η)) := by
    exact ((kernelSplit (E := ElectronL2) n).symm_apply_apply _).symm.trans
      (congrArg (kernelSplit (E := ElectronL2) n).symm hs)
  calc
    _ = ⟪(kernelSplit (E := ElectronL2) n).symm
        (tensorEmbedding (sectorMeasure n) v (tensorEmbedding volume f η)),
      kernelCreationRaw (fiberKernel F hF hM) n (tensorEmbedding (sectorMeasure n) u γ)⟫_ℂ :=
        congrArg (fun z : KernelSector ElectronL2 (n+1) => ⟪z,
          kernelCreationRaw (fiberKernel F hF hM) n (tensorEmbedding (sectorMeasure n) u γ)⟫_ℂ) (ht.trans he)
    _ = _ := fiberKernelCreationRaw_pair_tensor F hF hM n v u f η γ

lemma fiberTensor_total {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (μ : Measure X) (z : Lp E 2 μ)
    (h : ∀ (η : Lp ℂ 2 μ) (e : E), ⟪tensorEmbedding μ η e,z⟫_ℂ = 0) : z = 0 := by
  have hall : ∀ t : Lp E 2 μ, ⟪t,z⟫_ℂ = 0 := by
    apply Lp.induction (by norm_num : (2:ℝ≥0∞) ≠ ∞) (fun t => ⟪t,z⟫_ℂ = 0)
    · intro e A hA hf
      let η := indicatorConstLp 2 hA hf.ne (1:ℂ)
      have he : tensorEmbedding μ η e = indicatorConstLp 2 hA hf.ne e := by
        rw [tensorEmbedding_apply]
        simpa [η] using compLp_indicatorConst μ hA hf.ne (ContinuousLinearMap.toSpanSingleton ℂ e) 1
      rw [Lp.simpleFunc.coe_indicatorConst]
      simpa only [he] using h η e
    · intro f g hf hg hd h₁ h₂
      rw [inner_add_left,h₁,h₂,add_zero]
    · exact isClosed_eq (continuous_id.inner continuous_const) continuous_const
  exact inner_self_eq_zero.mp (hall z)

lemma fiberPrepend_total (n : ℕ) (z : AmbientSector (n+1))
    (h : ∀ (f : OneBoson) (v : AmbientSector n), ⟪prependProduct n f v,z⟫_ℂ = 0) : z = 0 := by
  let U := productUnitary (E := ℂ) (volume : Measure GW.Space) (sectorMeasure n)
  let V := splitUnitary n 0
  have hz : U.symm (V z) = 0 := by
    apply fiberTensor_total volume
    intro f v
    have he := h f v
    change ⟪V.symm (productFunction volume (sectorMeasure n) f v),z⟫_ℂ = 0 at he
    have hp := V.inner_map_map (V.symm (U (tensorEmbedding volume f v))) z
    rw [V.apply_symm_apply,productUnitary_tensor] at hp
    have hu := U.inner_map_map (tensorEmbedding volume f v) (U.symm (V z))
    rw [U.apply_symm_apply,productUnitary_tensor] at hu
    exact hu.symm.trans (hp.trans he)
  have hh := congrArg (fun a => V.symm (U a)) hz
  simpa only [U.apply_symm_apply,V.symm_apply_apply,map_zero] using hh

def fiberPrependMap (n : ℕ) (u : AmbientSector n) : OneBoson →L[ℂ] AmbientSector (n+1) :=
  (splitUnitary n 0).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (productFunctionMap (volume : Measure GW.Space) (sectorMeasure n) u)

lemma fiberPrependMap_apply (n : ℕ) (u : AmbientSector n) (f : OneBoson) :
    fiberPrependMap n u f = prependProduct n f u := rfl

def fiberRawCore (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M)
    (n : ℕ) (u : AmbientSector n) (γ : ElectronL2) :
    Lp (AmbientSector (n+1)) 2 (volume : Measure GW.Space) :=
  (fiberPrependMap n u).compLp (fiberKernelClass F hF hM γ)

lemma fiberRawCore_ae (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M)
    (n : ℕ) (u : AmbientSector n) (γ : ElectronL2) :
    fiberRawCore F hF hM n u γ =ᵐ[volume] fun x => γ x • prependProduct n (F x) u := by
  filter_upwards [(fiberPrependMap n u).coeFn_compLp (fiberKernelClass F hF hM γ),
    fiberKernelClass_ae F hF hM γ] with x h₁ h₂
  change (fiberPrependMap n u).compLp (fiberKernelClass F hF hM γ) x = _
  rw [h₁,h₂]
  change fiberPrependMap n u (γ x • F x) = _
  exact (fiberPrependMap n u).map_smul (γ x) (F x)

lemma fiberRawCore_pair (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M)
    (n : ℕ) (v u : AmbientSector n) (f : OneBoson) (η γ : ElectronL2) :
    ⟪tensorEmbedding volume η (prependProduct n f v),fiberRawCore F hF hM n u γ⟫_ℂ =
      ⟪v,u⟫_ℂ * ∫ x, ⟪η x • f,γ x • F x⟫_ℂ ∂(volume : Measure GW.Space) := by
  rw [L2.inner_def,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [tensorEmbedding_ae volume η (prependProduct n f v),
    fiberRawCore_ae F hF hM n u γ] with x h₁ h₂
  rw [h₁,h₂,inner_smul_left,inner_smul_right,fiberPrepend_inner,
    inner_smul_left,inner_smul_right]
  ring

set_option maxHeartbeats 1500000 in
lemma fiberPhysicalProduct_total (n : ℕ) (z : KernelSector ElectronL2 (n+1))
    (h : ∀ (η : ElectronL2) (f : OneBoson) (v : AmbientSector n),
      ⟪physicalKernelProduct (n+1) (productFunction volume (sectorMeasure (n+1)) η (prependProduct n f v)),z⟫_ℂ = 0) : z = 0 := by
  let P := physicalKernelProduct (n+1)
  let U := productUnitary (E := ℂ) (volume : Measure GW.Space) (sectorMeasure (n+1))
  let y := U.symm (P.symm z)
  have hy : y = 0 := by
    apply fiberTensor_total volume
    intro η e
    have hc : contraction volume η y = 0 := by
      apply fiberPrepend_total n
      intro f v
      rw [contraction_pairing]
      have he := h η f v
      have hp := P.inner_map_map (U (tensorEmbedding volume η (prependProduct n f v))) (P.symm z)
      rw [P.apply_symm_apply,productUnitary_tensor] at hp
      have hu := U.inner_map_map (tensorEmbedding volume η (prependProduct n f v)) y
      change ⟪U (tensorEmbedding volume η (prependProduct n f v)),U (U.symm (P.symm z))⟫_ℂ = _ at hu
      rw [U.apply_symm_apply,productUnitary_tensor] at hu
      exact hu.symm.trans (hp.symm.trans he)
    rw [← contraction_pairing,hc,inner_zero_right]
  have he := congrArg (fun t => P (U t)) hy
  simpa only [y,U.apply_symm_apply,P.apply_symm_apply,map_zero] using he

set_option maxHeartbeats 1500000 in
lemma fiberRawCore_identification (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M)
    (n : ℕ) (u : AmbientSector n) (γ : ElectronL2) :
    kernelCreationRaw (fiberKernel F hF hM) n (tensorEmbedding (sectorMeasure n) u γ) =
      physicalKernelProduct (n+1) (productUnitary volume (sectorMeasure (n+1)) (fiberRawCore F hF hM n u γ)) := by
  let P := physicalKernelProduct (n+1)
  let U := productUnitary (E := ℂ) (volume : Measure GW.Space) (sectorMeasure (n+1))
  apply sub_eq_zero.mp
  apply fiberPhysicalProduct_total n
  intro η f v
  rw [inner_sub_right]
  apply sub_eq_zero.mpr
  have hpair : ⟪P (productFunction volume (sectorMeasure (n+1)) η (prependProduct n f v)),
      P (U (fiberRawCore F hF hM n u γ))⟫_ℂ =
      ⟪v,u⟫_ℂ * ∫ x, ⟪η x • f,γ x • F x⟫_ℂ ∂(volume : Measure GW.Space) := by
    calc
      _ = ⟪productFunction volume (sectorMeasure (n+1)) η (prependProduct n f v),
          U (fiberRawCore F hF hM n u γ)⟫_ℂ := P.inner_map_map _ _
      _ = ⟪U (tensorEmbedding volume η (prependProduct n f v)),U (fiberRawCore F hF hM n u γ)⟫_ℂ :=
        congrArg (fun z => ⟪z,U (fiberRawCore F hF hM n u γ)⟫_ℂ)
          (productUnitary_tensor volume (sectorMeasure (n+1)) η (prependProduct n f v)).symm
      _ = ⟪tensorEmbedding volume η (prependProduct n f v),fiberRawCore F hF hM n u γ⟫_ℂ := U.inner_map_map _ _
      _ = _ := fiberRawCore_pair F hF hM n v u f η γ
  exact (fiberPhysicalRawCreation_pair F hF hM n v u f η γ).trans hpair.symm

lemma fiberVacuum_tensor {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (c : ℂ) (γ : E) :
    kernelVacuum (c • γ) = tensorEmbedding (sectorMeasure 0) (kernelVacuum c) γ := by
  apply Lp.ext
  filter_upwards [kernelVacuum_ae (c • γ),tensorEmbedding_ae (sectorMeasure 0) (kernelVacuum c) γ,
    kernelVacuum_ae c] with k h₁ h₂ h₃
  exact h₁.trans (h₂.trans (congrArg (fun z : ℂ => z • γ) h₃)).symm

lemma fiberPhysicalSectorKernel_tensor (n : ℕ) (γ : ElectronL2) (u : Sector n) :
    (physicalSectorKernel n ((ContinuousLinearMap.toSpanSingleton ℂ u).compLp γ) : KernelSector ElectronL2 n) =
      tensorEmbedding (sectorMeasure n) ((ordinarySectorKernel n u : kernelFixed (E := ℂ) n) : AmbientSector n) γ := by
  cases n with
  | zero =>
    change (physicalSectorKernel 0 ((ContinuousLinearMap.toSpanSingleton ℂ (u : ℂ)).compLp γ) : KernelSector ElectronL2 0) =
      tensorEmbedding (sectorMeasure 0) (kernelVacuum (u : ℂ)) γ
    exact (fiberPhysicalSectorKernel_tensor_vacuum γ u).trans (fiberVacuum_tensor u γ)
  | succ n => exact fiberPhysicalSectorKernel_tensor_positive n γ u

lemma fiberPhysicalSectorKernel_positive_formula (n : ℕ) (u : ElectronSector (n+1)) :
    (physicalSectorKernel (n+1) u : KernelSector ElectronL2 (n+1)) =
      physicalKernelProduct (n+1) (productUnitary volume (sectorMeasure (n+1))
        (amplify volume (symmetricInclusion (n+1)).toContinuousLinearMap u)) := rfl

lemma fiberSymmetricProjection_inclusion (n : ℕ) (u : Lp (AmbientSector n) 2 (volume : Measure GW.Space)) :
    amplify volume (symmetricInclusion n).toContinuousLinearMap
      (amplify volume (symmetricProjection n) u) = amplify volume (symmetrizer n) u := by
  apply Lp.ext
  filter_upwards [amplify_ae volume (symmetricInclusion n).toContinuousLinearMap
      (amplify volume (symmetricProjection n) u),
    amplify_ae volume (symmetricProjection n) u,amplify_ae volume (symmetrizer n) u] with x h₁ h₂ h₃
  rw [h₁,h₂,h₃]
  rfl

lemma fiberOrdinaryCreation_projection (n : ℕ) (f : OneBoson) (u : Sector n) :
    sectorCreation ordinarySectorKernel (ordinaryKernel f) n u =
      (Real.sqrt (n+1 : ℕ) : ℂ) • symmetricProjection (n+1)
        (prependProduct n f ((ordinarySectorKernel n u : kernelFixed (E := ℂ) n) : AmbientSector n)) := by
  apply (sectorInclusion n).injective
  have he : sectorInclusion n (sectorCreation ordinarySectorKernel (ordinaryKernel f) n u) =
      (kernelCreation (ordinaryKernel f) n (ordinarySectorKernel n u) : AmbientSector (n+1)) := by
    exact congrArg (fun z : kernelFixed (E := ℂ) (n+1) => (z : AmbientSector (n+1)))
      ((ordinarySectorKernel (n+1)).apply_symm_apply (kernelCreation (ordinaryKernel f) n (ordinarySectorKernel n u)))
  rw [he,kernelCreation_value,ordinaryKernelSymmetrizer,ordinaryKernelCreationRaw]
  rfl

def fiberCreationCore (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M)
    (n : ℕ) (u : Sector n) (γ : ElectronL2) : ElectronSector (n+1) :=
  (Real.sqrt (n+1 : ℕ) : ℂ) • amplify volume (symmetricProjection (n+1))
    (fiberRawCore F hF hM n ((ordinarySectorKernel n u : kernelFixed (E := ℂ) n) : AmbientSector n) γ)

set_option backward.isDefEq.respectTransparency.types false in
lemma fiberCreationCore_ae (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M)
    (n : ℕ) (u : Sector n) (γ : ElectronL2) :
    fiberCreationCore F hF hM n u γ =ᵐ[volume]
      fun x => γ x • sectorCreation ordinarySectorKernel (ordinaryKernel (F x)) n u := by
  let v : AmbientSector n := (ordinarySectorKernel n u : kernelFixed (E := ℂ) n)
  let z := fiberRawCore F hF hM n v γ
  filter_upwards [Lp.coeFn_smul (Real.sqrt (n+1 : ℕ) : ℂ) (amplify volume (symmetricProjection (n+1)) z),
    amplify_ae volume (symmetricProjection (n+1)) z,fiberRawCore_ae F hF hM n v γ] with x h₁ h₂ h₃
  change ((Real.sqrt (n+1 : ℕ) : ℂ) • amplify volume (symmetricProjection (n+1)) z) x = _
  simp only [Pi.smul_apply] at h₁
  rw [h₁,h₂,h₃,map_smul,fiberOrdinaryCreation_projection]
  exact smul_comm _ _ _

lemma fiberGeneralizedCreation_intertwines (K : BosonKernel ElectronL2) (n : ℕ) (u : ElectronSector n) :
    (physicalSectorKernel (n+1) (generalizedCreationSector K n u) : KernelSector ElectronL2 (n+1)) =
      (kernelCreation K n (physicalSectorKernel n u) : KernelSector ElectronL2 (n+1)) :=
  congrArg (fun z : kernelFixed (E := ElectronL2) (n+1) => (z : KernelSector ElectronL2 (n+1)))
    ((physicalSectorKernel (n+1)).apply_symm_apply (kernelCreation K n (physicalSectorKernel n u)))

set_option maxHeartbeats 1500000 in
set_option backward.isDefEq.respectTransparency.types false in
lemma fiberPhysicalProjection_formula (n : ℕ) (z : Lp (AmbientSector (n+1)) 2 (volume : Measure GW.Space)) :
    (physicalSectorKernel (n+1) (amplify volume (symmetricProjection (n+1)) z) : KernelSector ElectronL2 (n+1)) =
      kernelSymmetrizer (n+1) (physicalKernelProduct (n+1) (productUnitary volume (sectorMeasure (n+1)) z)) := by
  rw [fiberPhysicalSectorKernel_positive_formula,fiberSymmetricProjection_inclusion]
  let U := productUnitary (E := ℂ) (volume : Measure GW.Space) (sectorMeasure (n+1))
  have hs : U (amplify volume (symmetrizer (n+1)) z) = productSymmetrizer volume (n+1) (U z) := by
    change U (amplify volume (symmetrizer (n+1)) z) =
      U (amplify volume (symmetrizer (n+1)) (U.symm (U z)))
    rw [U.symm_apply_apply]
  rw [hs,fiberPhysicalKernelProduct_symmetrizer]

set_option maxHeartbeats 1500000 in
set_option backward.isDefEq.respectTransparency.types false in
lemma fiberCreationCore_identification (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M)
    (n : ℕ) (u : Sector n) (γ : ElectronL2) :
    generalizedCreationSector (fiberKernel F hF hM) n
      ((ContinuousLinearMap.toSpanSingleton ℂ u).compLp γ) = fiberCreationCore F hF hM n u γ := by
  apply (physicalSectorKernel (n+1)).injective
  apply Subtype.ext
  let v : AmbientSector n := (ordinarySectorKernel n u : kernelFixed (E := ℂ) n)
  let z := fiberRawCore F hF hM n v γ
  let c : ℂ := Real.sqrt (n+1 : ℕ)
  have hr := fiberRawCore_identification F hF hM n v γ
  have hl : (physicalSectorKernel (n+1) (generalizedCreationSector (fiberKernel F hF hM) n
      ((ContinuousLinearMap.toSpanSingleton ℂ u).compLp γ)) : KernelSector ElectronL2 (n+1)) =
      c • kernelSymmetrizer (n+1)
        (kernelCreationRaw (fiberKernel F hF hM) n (tensorEmbedding (sectorMeasure n) v γ)) := by
    rw [fiberGeneralizedCreation_intertwines,kernelCreation_value]
    exact congrArg (fun q : KernelSector ElectronL2 n => c • kernelSymmetrizer (n+1)
      (kernelCreationRaw (fiberKernel F hF hM) n q)) (fiberPhysicalSectorKernel_tensor n γ u)
  calc
    _ = c • kernelSymmetrizer (n+1)
        (kernelCreationRaw (fiberKernel F hF hM) n (tensorEmbedding (sectorMeasure n) v γ)) := hl
    _ = c • kernelSymmetrizer (n+1)
        (physicalKernelProduct (n+1) (productUnitary volume (sectorMeasure (n+1)) z)) :=
      congrArg (fun q => c • kernelSymmetrizer (n+1) q) hr
    _ = _ := by
      change _ = (physicalSectorKernel (n+1) (c • amplify volume (symmetricProjection (n+1)) z) : KernelSector ElectronL2 (n+1))
      have hm := congrArg (fun q : kernelFixed (E := ElectronL2) (n+1) => (q : KernelSector ElectronL2 (n+1)))
        ((physicalSectorKernel (n+1)).map_smul c (amplify volume (symmetricProjection (n+1)) z))
      exact (congrArg (fun q : KernelSector ElectronL2 (n+1) => c • q) (fiberPhysicalProjection_formula n z).symm).trans hm.symm

lemma fiberOrdinaryCreator_smul_vector (f : OneBoson) (c : ℂ) (u : FiberRootDomain) :
    fiberOrdinaryCreator f (c • u) = c • fiberOrdinaryCreator f u := by
  let A := ordinaryCreation f
  let w (v : FiberRootDomain) : A.domain := ⟨(fiberOrdinaryRootInput v).val,
    creation_mem_shiftedRoot ordinarySectorKernel (ordinaryKernel f) (fiberOrdinaryRootInput v)⟩
  have he : w (c • u) = c • w u := Subtype.ext rfl
  change A (w (c • u)) = c • A (w u)
  rw [he]
  exact A.toFun.map_smul c (w u)

def fiberCreatorClass (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M) (u : FiberPhysicalRoot) : Physical :=
  (fiberPointwiseCreator_memLp F hF hM u).toLp (fiberPointwiseCreator F u)

lemma fiberCreatorClass_ae (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M) (u : FiberPhysicalRoot) :
    fiberCreatorClass F hF hM u =ᵐ[volume] fiberPointwiseCreator F u := MemLp.coeFn_toLp _

lemma fiberCreatorClass_add (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M) (u v : FiberPhysicalRoot) :
    fiberCreatorClass F hF hM (u+v) = fiberCreatorClass F hF hM u+fiberCreatorClass F hF hM v := by
  apply Lp.ext
  have hr : fiberRootRepresentative (u+v) = fiberRootRepresentative u+fiberRootRepresentative v := map_add _ _ _
  filter_upwards [fiberCreatorClass_ae F hF hM (u+v),fiberCreatorClass_ae F hF hM u,
    fiberCreatorClass_ae F hF hM v,Lp.coeFn_add (fiberCreatorClass F hF hM u) (fiberCreatorClass F hF hM v),
    Lp.coeFn_add (fiberRootRepresentative u) (fiberRootRepresentative v)] with x h₁ h₂ h₃ h₄ h₅
  simp only [Pi.add_apply] at h₄ h₅
  rw [h₁,h₄,h₂,h₃]
  change fiberOrdinaryCreator (F x) (fiberRootRepresentative (u+v) x) = _
  rw [hr,h₅]
  exact fiberOrdinaryCreator_add_vector _ _ _

lemma fiberCreatorClass_smul (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M) (c : ℂ) (u : FiberPhysicalRoot) :
    fiberCreatorClass F hF hM (c • u) = c • fiberCreatorClass F hF hM u := by
  apply Lp.ext
  have hr : fiberRootRepresentative (c • u) = c • fiberRootRepresentative u := map_smul _ _ _
  filter_upwards [fiberCreatorClass_ae F hF hM (c • u),fiberCreatorClass_ae F hF hM u,
    Lp.coeFn_smul c (fiberCreatorClass F hF hM u),Lp.coeFn_smul c (fiberRootRepresentative u)] with x h₁ h₂ h₃ h₄
  simp only [Pi.smul_apply] at h₃ h₄
  rw [h₁,h₃,h₂]
  change fiberOrdinaryCreator (F x) (fiberRootRepresentative (c • u) x) = _
  rw [hr,h₄]
  exact fiberOrdinaryCreator_smul_vector _ _ _

lemma fiberCreatorClass_bound (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M) (u : FiberPhysicalRoot) :
    ‖fiberCreatorClass F hF hM u‖ ≤ M*‖u‖ := by
  have hb : ‖fiberCreatorClass F hF hM u‖ ≤ M*‖fiberRootRepresentative u‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [fiberCreatorClass_ae F hF hM u,hM] with x hx hM
    rw [hx]
    exact (fiberOrdinaryCreator_bound _ _).trans (mul_le_mul_of_nonneg_right hM (norm_nonneg _))
  exact hb.trans_eq (congrArg (fun r : ℝ => M*r) ((physicalNumberGraphBochnerUnitary (1/2) (by norm_num)).symm.norm_map u))

def fiberCreatorMap (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M) : FiberPhysicalRoot →L[ℂ] Physical :=
  LinearMap.mkContinuous
    { toFun := fiberCreatorClass F hF hM
      map_add' := fiberCreatorClass_add F hF hM
      map_smul' := fiberCreatorClass_smul F hF hM }
    M (fiberCreatorClass_bound F hF hM)

def fiberPhysicalRootInput (u : FiberPhysicalRoot) : (physicalShiftedNumberPower (1/2)).domain := u

lemma fiberPhysicalRoot_norm (u : FiberPhysicalRoot) :
    ‖physicalShiftedNumberPower (1/2) (fiberPhysicalRootInput u)‖ = ‖u‖ :=
  (GW.Spaces.weightedDomain_norm
    (bochnerWeightedGraph (volume : Measure GW.Space) Sector (fun n => ((n:ℝ)+1)^(1/2:ℝ))
      (shiftedNumber_weight_one (1/2) (by norm_num))) u).symm

def fiberGeneralizedCreator (K : BosonKernel ElectronL2) (u : FiberPhysicalRoot) : Physical :=
  generalizedCreation K (generalizedCreationShiftedInput K (fiberPhysicalRootInput u))

lemma fiberGeneralizedCreator_add (K : BosonKernel ElectronL2) (u v : FiberPhysicalRoot) :
    fiberGeneralizedCreator K (u+v) = fiberGeneralizedCreator K u+fiberGeneralizedCreator K v := by
  have he : generalizedCreationShiftedInput K (fiberPhysicalRootInput (u+v)) =
      generalizedCreationShiftedInput K (fiberPhysicalRootInput u)+generalizedCreationShiftedInput K (fiberPhysicalRootInput v) :=
    Subtype.ext rfl
  exact (congrArg (generalizedCreation K).toFun he).trans ((generalizedCreation K).toFun.map_add _ _)

lemma fiberGeneralizedCreator_smul (K : BosonKernel ElectronL2) (c : ℂ) (u : FiberPhysicalRoot) :
    fiberGeneralizedCreator K (c • u) = c • fiberGeneralizedCreator K u := by
  have he : generalizedCreationShiftedInput K (fiberPhysicalRootInput (c • u)) =
      c • generalizedCreationShiftedInput K (fiberPhysicalRootInput u) := Subtype.ext rfl
  exact (congrArg (generalizedCreation K).toFun he).trans ((generalizedCreation K).toFun.map_smul _ _)

lemma fiberGeneralizedCreator_bound (K : BosonKernel ElectronL2) (u : FiberPhysicalRoot) :
    ‖fiberGeneralizedCreator K u‖ ≤ ‖K‖*‖u‖ := by
  exact (generalizedCreation_shifted_norm K (fiberPhysicalRootInput u)).trans_eq
    (congrArg (fun r : ℝ => ‖K‖*r) (fiberPhysicalRoot_norm u))

def fiberGeneralizedCreatorMap (K : BosonKernel ElectronL2) : FiberPhysicalRoot →L[ℂ] Physical :=
  LinearMap.mkContinuous
    { toFun := fiberGeneralizedCreator K
      map_add' := fiberGeneralizedCreator_add K
      map_smul' := fiberGeneralizedCreator_smul K }
    ‖K‖ (fiberGeneralizedCreator_bound K)

lemma fiberOrdinaryCreator_single (f : OneBoson) (n : ℕ) (u : Sector n) :
    fiberOrdinaryCreator f (numberWeightedSingle Sector (1/2) (by norm_num) n u) =
      lp.single 2 (n+1) (sectorCreation ordinarySectorKernel (ordinaryKernel f) n u) := by
  let a : (ordinaryCreation f).domain :=
    ⟨lp.single 2 n u,creation_mem_shiftedRoot ordinarySectorKernel (ordinaryKernel f)
      (fiberOrdinaryRootInput (numberWeightedSingle Sector (1/2) (by norm_num) n u))⟩
  have hg := creation_single_graph (sectorCreation ordinarySectorKernel (ordinaryKernel f)) n u
  obtain ⟨b,hb,hvalue⟩ := (ordinaryCreation f).mem_graph_iff.mp hg
  have he : b = a := Subtype.ext hb
  rw [he] at hvalue
  exact hvalue

lemma fiberRootRepresentative_simpleTensor (γ : ElectronL2) (u : FiberRootDomain) :
    fiberRootRepresentative (weightedSimpleTensor volume Sector (1/2) (by norm_num) γ u) =
      tensorEmbedding volume γ u :=
  (physicalNumberGraphBochnerUnitary (1/2) (by norm_num)).symm_apply_apply _

set_option maxHeartbeats 1500000 in
lemma fiberCreatorClass_single (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M)
    (n : ℕ) (u : Sector n) (γ : ElectronL2) :
    fiberCreatorClass F hF hM
      (weightedSimpleTensor volume Sector (1/2) (by norm_num) γ (numberWeightedSingle Sector (1/2) (by norm_num) n u)) =
      electronBosonUnitary (lp.single 2 (n+1) (fiberCreationCore F hF hM n u γ)) := by
  rw [bochnerUnitary_single]
  apply Lp.ext
  let w := numberWeightedSingle Sector (1/2) (by norm_num) n u
  let U := weightedSimpleTensor volume Sector (1/2) (by norm_num) γ w
  have hr : fiberRootRepresentative U = tensorEmbedding volume γ w := fiberRootRepresentative_simpleTensor γ w
  filter_upwards [fiberCreatorClass_ae F hF hM U,tensorEmbedding_ae volume γ w,
    (lp.singleContinuousLinearMap ℂ Sector 2 (n+1)).coeFn_compLp (fiberCreationCore F hF hM n u γ),
    fiberCreationCore_ae F hF hM n u γ] with x h₁ h₂ h₃ h₄
  rw [h₁,h₃,h₄]
  change fiberOrdinaryCreator (F x) (fiberRootRepresentative U x) = _
  rw [hr,h₂,fiberOrdinaryCreator_smul_vector,fiberOrdinaryCreator_single]
  exact ((lp.singleContinuousLinearMap ℂ Sector 2 (n+1)).map_smul (γ x) _).symm

lemma fiberNumberWeightedSingle_inclusion (n : ℕ) (u : Sector n) :
    numberDomainInclusion Sector (1/2) (by norm_num) (numberWeightedSingle Sector (1/2) (by norm_num) n u) =
      lp.single 2 n u := numberDomainInclusion_apply Sector (1/2) (by norm_num) _

set_option maxHeartbeats 1500000 in
lemma fiberWeightedSingle_ambient (n : ℕ) (u : Sector n) (γ : ElectronL2) :
    (show Physical from (show (physicalShiftedNumberPower (1/2)).domain from
      weightedSimpleTensor volume Sector (1/2) (by norm_num) γ (numberWeightedSingle Sector (1/2) (by norm_num) n u))) =
      electronBosonUnitary (lp.single 2 n ((ContinuousLinearMap.toSpanSingleton ℂ u).compLp γ)) := by
  rw [weightedSimpleTensor_ambient,bochnerUnitary_single]
  apply Lp.ext
  filter_upwards [(ContinuousLinearMap.toSpanSingleton ℂ
      (numberDomainInclusion Sector (1/2) (by norm_num) (numberWeightedSingle Sector (1/2) (by norm_num) n u))).coeFn_compLp γ,
    (lp.singleContinuousLinearMap ℂ Sector 2 n).coeFn_compLp ((ContinuousLinearMap.toSpanSingleton ℂ u).compLp γ),
    (ContinuousLinearMap.toSpanSingleton ℂ u).coeFn_compLp γ] with x h₁ h₂ h₃
  rw [h₁,h₂,h₃,fiberNumberWeightedSingle_inclusion]
  change γ x • lp.single 2 n u = lp.single 2 n (γ x • u)
  exact ((lp.singleContinuousLinearMap ℂ Sector 2 n).map_smul (γ x) u).symm

set_option maxHeartbeats 1500000 in
lemma fiberGeneralizedCreator_single (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M)
    (n : ℕ) (u : Sector n) (γ : ElectronL2) :
    fiberGeneralizedCreator (fiberKernel F hF hM)
      (weightedSimpleTensor volume Sector (1/2) (by norm_num) γ (numberWeightedSingle Sector (1/2) (by norm_num) n u)) =
      electronBosonUnitary (lp.single 2 (n+1) (fiberCreationCore F hF hM n u γ)) := by
  let U := weightedSimpleTensor volume Sector (1/2) (by norm_num) γ (numberWeightedSingle Sector (1/2) (by norm_num) n u)
  let K := fiberKernel F hF hM
  let a := generalizedCreationShiftedInput K (fiberPhysicalRootInput U)
  have ha : electronBosonUnitary.symm a.val = lp.single 2 n ((ContinuousLinearMap.toSpanSingleton ℂ u).compLp γ) := by
    exact (congrArg electronBosonUnitary.symm (fiberWeightedSingle_ambient n u γ)).trans
      (electronBosonUnitary.symm_apply_apply _)
  apply electronBosonUnitary.symm.injective
  rw [electronBosonUnitary.symm_apply_apply]
  apply lp.ext
  funext j
  cases j with
  | zero =>
    exact (generalizedCreation_zero K a).trans (lp.single_apply_ne _ _ _ (by omega)).symm
  | succ j =>
    have hs := generalizedCreation_succ K a j
    have hx := congrArg (fun v : ElectronBosonSum => v j) ha
    have hh := hs.trans (congrArg (generalizedCreationSector K j) hx)
    by_cases hj : j = n
    · subst j
      rw [lp.single_apply_self,fiberCreationCore_identification F hF hM] at hh
      exact hh.trans (lp.single_apply_self _ _ _).symm
    · rw [lp.single_apply_ne _ _ _ hj,map_zero] at hh
      exact hh.trans (lp.single_apply_ne _ _ _ (by omega)).symm

set_option maxHeartbeats 1500000 in
lemma fiberCreation_identification_root (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M) (u : FiberPhysicalRoot) :
    fiberGeneralizedCreator (fiberKernel F hF hM) u = fiberCreatorClass F hF hM u := by
  let D := fiberGeneralizedCreatorMap (fiberKernel F hF hM)-fiberCreatorMap F hF hM
  have hs : Submodule.span ℂ (numberIndicatorProducts volume Sector (1/2) (by norm_num)) ≤ D.ker := by
    apply Submodule.span_le.mpr
    rintro U ⟨n,A,hA,hfin,v,hU⟩
    let γ : ElectronL2 := indicatorConstLp 2 hA hfin (1:ℂ)
    let w := numberWeightedSingle Sector (1/2) (by norm_num) n v
    let W := weightedSimpleTensor volume Sector (1/2) (by norm_num) γ w
    have he : U = W := by
      apply Subtype.ext
      have hw := weightedSimpleTensor_ambient (volume : Measure GW.Space) Sector (1/2) (by norm_num) γ w
      have hz : (show Physical from (show (physicalShiftedNumberPower (1/2)).domain from W)) =
          indicatorConstLp 2 hA hfin (lp.single 2 n v) := by
        dsimp only [w] at hw
        rw [fiberNumberWeightedSingle_inclusion] at hw
        exact hw.trans (simpleTensor_indicatorConst volume hA hfin (lp.single 2 n v))
      exact hU.trans hz.symm
    change fiberGeneralizedCreator (fiberKernel F hF hM) U-fiberCreatorClass F hF hM U = 0
    rw [he]
    apply sub_eq_zero.mpr
    exact (fiberGeneralizedCreator_single F hF hM n v γ).trans (fiberCreatorClass_single F hF hM n v γ).symm
  have hd : Dense (D.ker : Set FiberPhysicalRoot) :=
    (numberIndicatorSpan_dense (volume : Measure GW.Space) Sector (1/2) (by norm_num)).mono hs
  have hc := hd.closure_eq
  rw [D.isClosed_ker.closure_eq] at hc
  have hu : u ∈ D.ker := by
    change u ∈ (D.ker : Set FiberPhysicalRoot)
    rw [hc]
    trivial
  exact sub_eq_zero.mp hu

lemma fiberAdjoint_pairing {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B : H →ₗ.[ℂ] H) (hd : Dense (A.domain : Set H)) (he : A.adjoint = B)
    (u : A.domain) (v : B.domain) : ⟪A u,v.val⟫_ℂ = ⟪u.val,B v⟫_ℂ := by
  let va : A.adjoint.domain := ⟨v.val,he.symm ▸ v.property⟩
  have hp := GW.Operators.adjoint_pairing A hd u va
  have hv : A.adjoint va = B v := by
    have hg : (v.val,A.adjoint va) ∈ B.graph := (congrArg LinearPMap.graph he) ▸ A.adjoint.mem_graph va
    exact B.mem_graph_snd_inj hg (B.mem_graph v) rfl
  exact hp.trans (congrArg (fun z : H => ⟪u.val,z⟫_ℂ) hv)

lemma fiberOrdinary_pairing (f : OneBoson) (u v : FiberRootDomain) :
    ⟪fiberOrdinaryCreator f u,numberDomainInclusion Sector (1/2) (by norm_num) v⟫_ℂ =
      ⟪numberDomainInclusion Sector (1/2) (by norm_num) u,fiberOrdinaryAnnihilator f v⟫_ℂ := by
  rw [numberDomainInclusion_apply,numberDomainInclusion_apply]
  exact fiberAdjoint_pairing (ordinaryCreation f) (ordinaryAnnihilation f)
    (maximalSectorCreation_dense (sectorCreation ordinarySectorKernel (ordinaryKernel f)))
    (ordinaryCreation_adjoint_eq f)
    ⟨(fiberOrdinaryRootInput u).val,creation_mem_shiftedRoot ordinarySectorKernel (ordinaryKernel f) (fiberOrdinaryRootInput u)⟩
    (ordinaryAnnihilationRootInput f (fiberOrdinaryRootInputUnshifted v))

lemma fiberRootRepresentative_ambient (u : FiberPhysicalRoot) :
    (fun x => numberDomainInclusion Sector (1/2) (by norm_num) (fiberRootRepresentative u x)) =ᵐ[volume]
      (show Physical from fiberPhysicalRootInput u) := by
  have he := numberGraphBochnerUnitary_inclusion (volume : Measure GW.Space) Sector (1/2) (by norm_num)
    (fiberRootRepresentative u)
  change (show Physical from fiberPhysicalRootInput
    ((physicalNumberGraphBochnerUnitary (1/2) (by norm_num))
      ((physicalNumberGraphBochnerUnitary (1/2) (by norm_num)).symm u))) = _ at he
  rw [LinearIsometryEquiv.apply_symm_apply] at he
  have hc := (numberDomainInclusion Sector (1/2) (by norm_num)).coeFn_compLp (fiberRootRepresentative u)
  change numberGraphIncludeL2 volume Sector (1/2) (by norm_num) (fiberRootRepresentative u) =ᵐ[volume] _ at hc
  rw [← he] at hc
  exact hc.symm

def fiberAnnihilatorClass (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M) (u : FiberPhysicalRoot) : Physical :=
  (fiberPointwiseAnnihilator_memLp F hF hM u).toLp (fiberPointwiseAnnihilator F u)

lemma fiberAnnihilatorClass_ae (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M) (u : FiberPhysicalRoot) :
    fiberAnnihilatorClass F hF hM u =ᵐ[volume] fiberPointwiseAnnihilator F u := MemLp.coeFn_toLp _

lemma fiberPointwise_pairing (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M) (u v : FiberPhysicalRoot) :
    ⟪fiberCreatorClass F hF hM u,(show Physical from fiberPhysicalRootInput v)⟫_ℂ =
      ⟪(show Physical from fiberPhysicalRootInput u),fiberAnnihilatorClass F hF hM v⟫_ℂ := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fiberCreatorClass_ae F hF hM u,fiberAnnihilatorClass_ae F hF hM v,
    fiberRootRepresentative_ambient u,fiberRootRepresentative_ambient v] with x h₁ h₂ h₃ h₄
  rw [h₁,h₂,← h₃,← h₄]
  exact fiberOrdinary_pairing (F x) (fiberRootRepresentative u x) (fiberRootRepresentative v x)

def fiberPhysicalRootUnshiftedInput (u : FiberPhysicalRoot) : (physicalNumberPower (1/2)).domain :=
  ⟨(fiberPhysicalRootInput u).val,by
    rw [physicalRootNumber_domains_eq]
    exact (fiberPhysicalRootInput u).property⟩



lemma fiberOrdinaryAnnihilator_single_succ (f : OneBoson) (n : ℕ) (u : Sector (n+1)) :
    fiberOrdinaryAnnihilator f (numberWeightedSingle Sector (1/2) (by norm_num) (n+1) u) =
      lp.single 2 n (sectorAnnihilation ordinarySectorKernel (ordinaryKernel f) n u) := by
  let w := numberWeightedSingle Sector (1/2) (by norm_num) (n+1) u
  let a := ordinaryAnnihilationRootInput f (fiberOrdinaryRootInputUnshifted w)
  have hg := annihilation_single_graph (sectorAnnihilation ordinarySectorKernel (ordinaryKernel f)) n u
  obtain ⟨b,hb,hvalue⟩ := (ordinaryAnnihilation f).mem_graph_iff.mp hg
  have he : b = a := Subtype.ext hb
  rw [he] at hvalue
  exact hvalue

def fiberAnnihilationCore (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M)
    (n : ℕ) (u : Sector (n+1)) (γ : ElectronL2) : ElectronSector n :=
  (lp.evalCLM ℂ Sector 2 n).compLp (fiberAnnihilatorClass F hF hM
    (weightedSimpleTensor volume Sector (1/2) (by norm_num) γ
      (numberWeightedSingle Sector (1/2) (by norm_num) (n+1) u)))

lemma fiberAnnihilationCore_ae (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M)
    (n : ℕ) (u : Sector (n+1)) (γ : ElectronL2) :
    fiberAnnihilationCore F hF hM n u γ =ᵐ[volume]
      fun x => γ x • sectorAnnihilation ordinarySectorKernel (ordinaryKernel (F x)) n u := by
  let w := numberWeightedSingle Sector (1/2) (by norm_num) (n+1) u
  let U := weightedSimpleTensor volume Sector (1/2) (by norm_num) γ w
  have hr : fiberRootRepresentative U = tensorEmbedding volume γ w := fiberRootRepresentative_simpleTensor γ w
  filter_upwards [(lp.evalCLM ℂ Sector 2 n).coeFn_compLp (fiberAnnihilatorClass F hF hM U),
    fiberAnnihilatorClass_ae F hF hM U,tensorEmbedding_ae volume γ w] with x he ha hw
  change ((lp.evalCLM ℂ Sector 2 n).compLp (fiberAnnihilatorClass F hF hM U)) x = _
  rw [he,ha]
  change fiberOrdinaryAnnihilator (F x) (fiberRootRepresentative U x) n = _
  rw [hr,hw]
  have hs : fiberOrdinaryAnnihilator (F x) (γ x • w) = γ x • fiberOrdinaryAnnihilator (F x) w := by
    let a := ordinaryAnnihilationRootInput (F x) (fiberOrdinaryRootInputUnshifted (γ x • w))
    let b := ordinaryAnnihilationRootInput (F x) (fiberOrdinaryRootInputUnshifted w)
    have hab : a = γ x • b := Subtype.ext rfl
    exact (congrArg (ordinaryAnnihilation (F x)).toFun hab).trans
      ((ordinaryAnnihilation (F x)).toFun.map_smul _ _)
  rw [hs,fiberOrdinaryAnnihilator_single_succ]
  change (γ x • lp.single 2 n (sectorAnnihilation ordinarySectorKernel (ordinaryKernel (F x)) n u)) n = _
  rw [lp.coeFn_smul,Pi.smul_apply,lp.single_apply_self]


def fiberGeneralizedAnnihilationRootInput (K : BosonKernel ElectronL2)
    (u : (physicalNumberPower (1/2)).domain) : (generalizedAnnihilation K).domain :=
  ⟨u.val,generalizedAnnihilation_mem_root K u⟩

def fiberGeneralizedAnnihilator (K : BosonKernel ElectronL2) (u : FiberPhysicalRoot) : Physical :=
  generalizedAnnihilation K (fiberGeneralizedAnnihilationRootInput K (fiberPhysicalRootUnshiftedInput u))

lemma fiberAnnihilationCore_identification (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M)
    (n : ℕ) (v : Sector (n+1)) (γ : ElectronL2) :
    generalizedAnnihilationSector (fiberKernel F hF hM) n
      ((ContinuousLinearMap.toSpanSingleton ℂ v).compLp γ) = fiberAnnihilationCore F hF hM n v γ := by
  apply sub_eq_zero.mp
  apply fiberTensor_total volume
  intro η e
  rw [inner_sub_right,tensorEmbedding_apply]
  apply sub_eq_zero.mpr
  have hp := sectorCreation_pairing physicalSectorKernel (fiberKernel F hF hM) n
    ((ContinuousLinearMap.toSpanSingleton ℂ e).compLp η) ((ContinuousLinearMap.toSpanSingleton ℂ v).compLp γ)
  have hc := fiberCreationCore_identification F hF hM n e η
  change sectorCreation physicalSectorKernel (fiberKernel F hF hM) n
    ((ContinuousLinearMap.toSpanSingleton ℂ e).compLp η) = fiberCreationCore F hF hM n e η at hc
  rw [hc] at hp
  apply hp.symm.trans
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fiberCreationCore_ae F hF hM n e η,fiberAnnihilationCore_ae F hF hM n v γ,
    (ContinuousLinearMap.toSpanSingleton ℂ v).coeFn_compLp γ,
    (ContinuousLinearMap.toSpanSingleton ℂ e).coeFn_compLp η] with x hc ha hv he
  rw [hc,ha,hv,he]
  simp only [ContinuousLinearMap.toSpanSingleton_apply,inner_smul_left,inner_smul_right,
    sectorCreation_pairing]

set_option maxHeartbeats 1500000 in
lemma fiberGeneralizedAnnihilator_single_succ (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M)
    (n : ℕ) (u : Sector (n+1)) (γ : ElectronL2) :
    fiberGeneralizedAnnihilator (fiberKernel F hF hM)
      (weightedSimpleTensor volume Sector (1/2) (by norm_num) γ (numberWeightedSingle Sector (1/2) (by norm_num) (n+1) u)) =
      electronBosonUnitary (lp.single 2 n (fiberAnnihilationCore F hF hM n u γ)) := by
  let U := weightedSimpleTensor volume Sector (1/2) (by norm_num) γ (numberWeightedSingle Sector (1/2) (by norm_num) (n+1) u)
  let K := fiberKernel F hF hM
  let a := fiberGeneralizedAnnihilationRootInput K (fiberPhysicalRootUnshiftedInput U)
  have ha : electronBosonUnitary.symm a.val = lp.single 2 (n+1) ((ContinuousLinearMap.toSpanSingleton ℂ u).compLp γ) := by
    exact (congrArg electronBosonUnitary.symm (fiberWeightedSingle_ambient (n+1) u γ)).trans
      (electronBosonUnitary.symm_apply_apply _)
  apply electronBosonUnitary.symm.injective
  rw [electronBosonUnitary.symm_apply_apply]
  apply lp.ext
  funext j
  have hs := generalizedAnnihilation_apply K a j
  have hx := congrArg (fun v : ElectronBosonSum => v (j+1)) ha
  have hh := hs.trans (congrArg (generalizedAnnihilationSector K j) hx)
  by_cases hj : j = n
  · subst j
    rw [lp.single_apply_self,fiberAnnihilationCore_identification F hF hM] at hh
    exact hh.trans (lp.single_apply_self _ _ _).symm
  · rw [lp.single_apply_ne _ _ _ (by omega),map_zero] at hh
    exact hh.trans (lp.single_apply_ne _ _ _ hj).symm


def fiberPhysicalDomainInclusion (r : ℝ) (hr : 0 ≤ r) : PhysicalNumberDomain r hr →L[ℂ] Physical :=
  (physicalShiftedWeightGraph r hr).embedding.comp
    (GW.Spaces.weightedDomainIsometry (physicalShiftedWeightGraph r hr)).toContinuousLinearEquiv.toContinuousLinearMap

lemma fiberPhysicalDomainInclusion_val (r : ℝ) (hr : 0 ≤ r) (u : PhysicalNumberDomain r hr) :
    fiberPhysicalDomainInclusion r hr u =
      (show (physicalShiftedNumberPower r).domain from u).val :=
  GW.Spaces.weightedDomain_embedding (physicalShiftedWeightGraph r hr) u

def fiberPhysicalDomainCast (s t : {r : ℝ // 0 ≤ r}) (h : s = t) :
    PhysicalNumberDomain s.val s.property ≃ₗᵢ[ℂ] PhysicalNumberDomain t.val t.property := by
  cases h
  exact LinearIsometryEquiv.refl ℂ _

lemma fiberPhysicalDomainCast_val (s t : {r : ℝ // 0 ≤ r}) (h : s = t)
    (u : PhysicalNumberDomain s.val s.property) :
    (show (physicalShiftedNumberPower t.val).domain from fiberPhysicalDomainCast s t h u).val =
      (show (physicalShiftedNumberPower s.val).domain from u).val := by
  cases h
  rfl

def fiberGeneralizedAnnihilatorMap (K : BosonKernel ElectronL2) : FiberPhysicalRoot →L[ℂ] Physical := by
  let s : {r : ℝ // 0 ≤ r} := ⟨1/2,by norm_num⟩
  let t : {r : ℝ // 0 ≤ r} := ⟨0+1/2,by norm_num⟩
  have he : s = t := Subtype.ext (by dsimp [s,t]; norm_num)
  let A := physicalWeightedAnnihilation K 0 (by norm_num)
  exact (fiberPhysicalDomainInclusion 0 (by norm_num)).comp
    (A.comp (fiberPhysicalDomainCast s t he).toContinuousLinearEquiv.toContinuousLinearMap)

lemma fiberPhysicalWeightedAnnihilation_value (K : BosonKernel ElectronL2) (r : ℝ) (hr : 0 ≤ r)
    (u : PhysicalNumberDomain (r+1/2) (by linarith)) :
    fiberPhysicalDomainInclusion r hr (physicalWeightedAnnihilation K r hr u) =
      generalizedAnnihilation K (physicalWeightedAnnihilationInput K r hr u) := by
  rw [fiberPhysicalDomainInclusion_val]
  rfl


lemma fiberPhysicalDomainInclusion_root (u : FiberPhysicalRoot) :
    fiberPhysicalDomainInclusion (1/2) (by norm_num) u = (fiberPhysicalRootInput u).val :=
  fiberPhysicalDomainInclusion_val (1/2) (by norm_num) u

lemma fiberGeneralizedAnnihilatorMap_graph (K : BosonKernel ElectronL2) (u : FiberPhysicalRoot) :
    (fiberPhysicalDomainInclusion (1/2) (by norm_num) u,fiberGeneralizedAnnihilatorMap K u) ∈
      (generalizedAnnihilation K).graph := by
  let s : {r : ℝ // 0 ≤ r} := ⟨1/2,by norm_num⟩
  let t : {r : ℝ // 0 ≤ r} := ⟨0+1/2,by norm_num⟩
  have he : s = t := Subtype.ext (by dsimp [s,t]; norm_num)
  let v := fiberPhysicalDomainCast s t he u
  let a := physicalWeightedAnnihilationInput K 0 (by norm_num) v
  have hout : fiberGeneralizedAnnihilatorMap K u = generalizedAnnihilation K a :=
    fiberPhysicalWeightedAnnihilation_value K 0 (by norm_num) v
  have hval : a.val = fiberPhysicalDomainInclusion (1/2) (by norm_num) u :=
    (fiberPhysicalDomainCast_val s t he u).trans (fiberPhysicalDomainInclusion_val (1/2) (by norm_num) u).symm
  exact (generalizedAnnihilation K).mem_graph_iff.mpr ⟨a,hval,hout.symm⟩

lemma fiberGeneralizedAnnihilatorMap_single_succ (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M)
    (n : ℕ) (u : Sector (n+1)) (γ : ElectronL2) :
    fiberGeneralizedAnnihilatorMap (fiberKernel F hF hM)
      (weightedSimpleTensor volume Sector (1/2) (by norm_num) γ (numberWeightedSingle Sector (1/2) (by norm_num) (n+1) u)) =
      electronBosonUnitary (lp.single 2 n (fiberAnnihilationCore F hF hM n u γ)) := by
  let U := weightedSimpleTensor volume Sector (1/2) (by norm_num) γ (numberWeightedSingle Sector (1/2) (by norm_num) (n+1) u)
  let K := fiberKernel F hF hM
  obtain ⟨a,ha,hout⟩ := (generalizedAnnihilation K).mem_graph_iff.mp (fiberGeneralizedAnnihilatorMap_graph K U)
  change a.val = fiberPhysicalDomainInclusion (1/2) (by norm_num) U at ha
  change generalizedAnnihilation K a = fiberGeneralizedAnnihilatorMap K U at hout
  have hinput : electronBosonUnitary.symm a.val = lp.single 2 (n+1) ((ContinuousLinearMap.toSpanSingleton ℂ u).compLp γ) := by
    rw [ha,fiberPhysicalDomainInclusion_root]
    exact (congrArg electronBosonUnitary.symm (fiberWeightedSingle_ambient (n+1) u γ)).trans
      (electronBosonUnitary.symm_apply_apply _)
  change fiberGeneralizedAnnihilatorMap K U = _
  rw [← hout]
  apply electronBosonUnitary.symm.injective
  rw [electronBosonUnitary.symm_apply_apply]
  apply lp.ext
  funext j
  have hs := generalizedAnnihilation_apply K a j
  have hx := congrArg (fun v : ElectronBosonSum => v (j+1)) hinput
  have hh := hs.trans (congrArg (generalizedAnnihilationSector K j) hx)
  by_cases hj : j = n
  · subst j
    rw [lp.single_apply_self,fiberAnnihilationCore_identification F hF hM] at hh
    exact hh.trans (lp.single_apply_self _ _ _).symm
  · rw [lp.single_apply_ne _ _ _ (by omega),map_zero] at hh
    exact hh.trans (lp.single_apply_ne _ _ _ hj).symm

lemma fiberGeneralizedAnnihilatorMap_single_zero (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M)
    (u : Sector 0) (γ : ElectronL2) :
    fiberGeneralizedAnnihilatorMap (fiberKernel F hF hM)
      (weightedSimpleTensor volume Sector (1/2) (by norm_num) γ (numberWeightedSingle Sector (1/2) (by norm_num) 0 u)) = 0 := by
  let U := weightedSimpleTensor volume Sector (1/2) (by norm_num) γ (numberWeightedSingle Sector (1/2) (by norm_num) 0 u)
  let K := fiberKernel F hF hM
  obtain ⟨a,ha,hout⟩ := (generalizedAnnihilation K).mem_graph_iff.mp (fiberGeneralizedAnnihilatorMap_graph K U)
  change a.val = fiberPhysicalDomainInclusion (1/2) (by norm_num) U at ha
  change generalizedAnnihilation K a = fiberGeneralizedAnnihilatorMap K U at hout
  have hinput : electronBosonUnitary.symm a.val = lp.single 2 0 ((ContinuousLinearMap.toSpanSingleton ℂ u).compLp γ) := by
    rw [ha,fiberPhysicalDomainInclusion_root]
    exact (congrArg electronBosonUnitary.symm (fiberWeightedSingle_ambient 0 u γ)).trans
      (electronBosonUnitary.symm_apply_apply _)
  change fiberGeneralizedAnnihilatorMap K U = _
  rw [← hout]
  apply electronBosonUnitary.symm.injective
  rw [map_zero]
  apply lp.ext
  funext j
  rw [generalizedAnnihilation_apply]
  change generalizedAnnihilationSector K j ((electronBosonUnitary.symm a.val) (j+1)) = 0
  rw [hinput,lp.single_apply_ne _ _ _ (by omega),map_zero]


lemma fiberOrdinaryAnnihilator_smul_vector (f : OneBoson) (c : ℂ) (u : FiberRootDomain) :
    fiberOrdinaryAnnihilator f (c • u) = c • fiberOrdinaryAnnihilator f u := by
  let a := ordinaryAnnihilationRootInput f (fiberOrdinaryRootInputUnshifted (c • u))
  let b := ordinaryAnnihilationRootInput f (fiberOrdinaryRootInputUnshifted u)
  have hab : a = c • b := Subtype.ext rfl
  exact (congrArg (ordinaryAnnihilation f).toFun hab).trans ((ordinaryAnnihilation f).toFun.map_smul _ _)

lemma fiberAnnihilatorClass_add (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M) (u v : FiberPhysicalRoot) :
    fiberAnnihilatorClass F hF hM (u+v) = fiberAnnihilatorClass F hF hM u+fiberAnnihilatorClass F hF hM v := by
  apply Lp.ext
  have hr : fiberRootRepresentative (u+v) = fiberRootRepresentative u+fiberRootRepresentative v := map_add _ _ _
  filter_upwards [fiberAnnihilatorClass_ae F hF hM (u+v),fiberAnnihilatorClass_ae F hF hM u,
    fiberAnnihilatorClass_ae F hF hM v,Lp.coeFn_add (fiberAnnihilatorClass F hF hM u) (fiberAnnihilatorClass F hF hM v),
    Lp.coeFn_add (fiberRootRepresentative u) (fiberRootRepresentative v)] with x h₁ h₂ h₃ h₄ h₅
  simp only [Pi.add_apply] at h₄ h₅
  rw [h₁,h₄,h₂,h₃]
  change fiberOrdinaryAnnihilator (F x) (fiberRootRepresentative (u+v) x) = _
  rw [hr,h₅]
  exact fiberOrdinaryAnnihilator_add_vector _ _ _

lemma fiberAnnihilatorClass_smul (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M) (c : ℂ) (u : FiberPhysicalRoot) :
    fiberAnnihilatorClass F hF hM (c • u) = c • fiberAnnihilatorClass F hF hM u := by
  apply Lp.ext
  have hr : fiberRootRepresentative (c • u) = c • fiberRootRepresentative u := map_smul _ _ _
  filter_upwards [fiberAnnihilatorClass_ae F hF hM (c • u),fiberAnnihilatorClass_ae F hF hM u,
    Lp.coeFn_smul c (fiberAnnihilatorClass F hF hM u),Lp.coeFn_smul c (fiberRootRepresentative u)] with x h₁ h₂ h₃ h₄
  simp only [Pi.smul_apply] at h₃ h₄
  rw [h₁,h₃,h₂]
  change fiberOrdinaryAnnihilator (F x) (fiberRootRepresentative (c • u) x) = _
  rw [hr,h₄]
  exact fiberOrdinaryAnnihilator_smul_vector _ _ _

lemma fiberAnnihilatorClass_bound (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M) (u : FiberPhysicalRoot) :
    ‖fiberAnnihilatorClass F hF hM u‖ ≤ M*‖u‖ := by
  have hb : ‖fiberAnnihilatorClass F hF hM u‖ ≤ M*‖fiberRootRepresentative u‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [fiberAnnihilatorClass_ae F hF hM u,hM] with x hx hM
    rw [hx]
    exact (fiberOrdinaryAnnihilator_bound _ _).trans (mul_le_mul_of_nonneg_right hM (norm_nonneg _))
  exact hb.trans_eq (congrArg (fun r : ℝ => M*r) ((physicalNumberGraphBochnerUnitary (1/2) (by norm_num)).symm.norm_map u))

def fiberAnnihilatorMap (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M) : FiberPhysicalRoot →L[ℂ] Physical :=
  LinearMap.mkContinuous
    { toFun := fiberAnnihilatorClass F hF hM
      map_add' := fiberAnnihilatorClass_add F hF hM
      map_smul' := fiberAnnihilatorClass_smul F hF hM }
    M (fiberAnnihilatorClass_bound F hF hM)


lemma fiberAnnihilatorClass_single_succ (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M)
    (n : ℕ) (u : Sector (n+1)) (γ : ElectronL2) :
    fiberAnnihilatorClass F hF hM
      (weightedSimpleTensor volume Sector (1/2) (by norm_num) γ (numberWeightedSingle Sector (1/2) (by norm_num) (n+1) u)) =
      electronBosonUnitary (lp.single 2 n (fiberAnnihilationCore F hF hM n u γ)) := by
  rw [bochnerUnitary_single]
  apply Lp.ext
  let w := numberWeightedSingle Sector (1/2) (by norm_num) (n+1) u
  let U := weightedSimpleTensor volume Sector (1/2) (by norm_num) γ w
  have hr : fiberRootRepresentative U = tensorEmbedding volume γ w := fiberRootRepresentative_simpleTensor γ w
  filter_upwards [fiberAnnihilatorClass_ae F hF hM U,tensorEmbedding_ae volume γ w,
    (lp.singleContinuousLinearMap ℂ Sector 2 n).coeFn_compLp (fiberAnnihilationCore F hF hM n u γ),
    fiberAnnihilationCore_ae F hF hM n u γ] with x h₁ h₂ h₃ h₄
  rw [h₁,h₃,h₄]
  change fiberOrdinaryAnnihilator (F x) (fiberRootRepresentative U x) = _
  rw [hr,h₂,fiberOrdinaryAnnihilator_smul_vector,fiberOrdinaryAnnihilator_single_succ]
  exact ((lp.singleContinuousLinearMap ℂ Sector 2 n).map_smul (γ x) _).symm

lemma fiberOrdinaryAnnihilator_single_zero (f : OneBoson) (u : Sector 0) :
    fiberOrdinaryAnnihilator f (numberWeightedSingle Sector (1/2) (by norm_num) 0 u) = 0 := by
  apply lp.ext
  funext j
  change ordinaryAnnihilation f (ordinaryAnnihilationRootInput f
    (fiberOrdinaryRootInputUnshifted (numberWeightedSingle Sector (1/2) (by norm_num) 0 u))) j = 0
  rw [ordinaryAnnihilation_apply]
  change sectorAnnihilation ordinarySectorKernel (ordinaryKernel f) j ((lp.single 2 0 u) (j+1)) = 0
  rw [lp.single_apply_ne _ _ _ (by omega),map_zero]

lemma fiberAnnihilatorClass_single_zero (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M)
    (u : Sector 0) (γ : ElectronL2) :
    fiberAnnihilatorClass F hF hM
      (weightedSimpleTensor volume Sector (1/2) (by norm_num) γ (numberWeightedSingle Sector (1/2) (by norm_num) 0 u)) = 0 := by
  apply Lp.ext
  let w := numberWeightedSingle Sector (1/2) (by norm_num) 0 u
  let U := weightedSimpleTensor volume Sector (1/2) (by norm_num) γ w
  have hr : fiberRootRepresentative U = tensorEmbedding volume γ w := fiberRootRepresentative_simpleTensor γ w
  filter_upwards [fiberAnnihilatorClass_ae F hF hM U,tensorEmbedding_ae volume γ w,
    Lp.coeFn_zero Carrier 2 (volume : Measure GW.Space)] with x ha hw hz
  rw [ha,hz]
  change fiberOrdinaryAnnihilator (F x) (fiberRootRepresentative U x) = 0
  rw [hr,hw,fiberOrdinaryAnnihilator_smul_vector,fiberOrdinaryAnnihilator_single_zero,smul_zero]


set_option maxHeartbeats 1500000 in
lemma fiberAnnihilationMap_identification_root (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M) (u : FiberPhysicalRoot) :
    fiberGeneralizedAnnihilatorMap (fiberKernel F hF hM) u = fiberAnnihilatorClass F hF hM u := by
  let D := fiberGeneralizedAnnihilatorMap (fiberKernel F hF hM)-fiberAnnihilatorMap F hF hM
  have hs : Submodule.span ℂ (numberIndicatorProducts volume Sector (1/2) (by norm_num)) ≤ D.ker := by
    apply Submodule.span_le.mpr
    rintro U ⟨n,A,hA,hfin,v,hU⟩
    let γ : ElectronL2 := indicatorConstLp 2 hA hfin (1:ℂ)
    let w := numberWeightedSingle Sector (1/2) (by norm_num) n v
    let W := weightedSimpleTensor volume Sector (1/2) (by norm_num) γ w
    have he : U = W := by
      apply Subtype.ext
      have hw := weightedSimpleTensor_ambient (volume : Measure GW.Space) Sector (1/2) (by norm_num) γ w
      have hz : (show Physical from (show (physicalShiftedNumberPower (1/2)).domain from W)) =
          indicatorConstLp 2 hA hfin (lp.single 2 n v) := by
        dsimp only [w] at hw
        rw [fiberNumberWeightedSingle_inclusion] at hw
        exact hw.trans (simpleTensor_indicatorConst volume hA hfin (lp.single 2 n v))
      exact hU.trans hz.symm
    change fiberGeneralizedAnnihilatorMap (fiberKernel F hF hM) U-fiberAnnihilatorClass F hF hM U = 0
    rw [he]
    apply sub_eq_zero.mpr
    cases n with
    | zero => rw [fiberGeneralizedAnnihilatorMap_single_zero,fiberAnnihilatorClass_single_zero]
    | succ n => exact (fiberGeneralizedAnnihilatorMap_single_succ F hF hM n v γ).trans (fiberAnnihilatorClass_single_succ F hF hM n v γ).symm
  have hd : Dense (D.ker : Set FiberPhysicalRoot) :=
    (numberIndicatorSpan_dense (volume : Measure GW.Space) Sector (1/2) (by norm_num)).mono hs
  have hc := hd.closure_eq
  rw [D.isClosed_ker.closure_eq] at hc
  have hu : u ∈ D.ker := by
    change u ∈ (D.ker : Set FiberPhysicalRoot)
    rw [hc]
    trivial
  exact sub_eq_zero.mp hu

def fiberWeightedInput {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (G : GW.Spaces.WeightedGraph H W) (V : Submodule ℂ H) (h : V ≤ G.domain) (u : V) :
    GW.Spaces.WeightedDomain G := ⟨u.val,h u.property⟩

lemma fiberWeightedInput_embedding {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (G : GW.Spaces.WeightedGraph H W) (V : Submodule ℂ H) (h : V ≤ G.domain) (u : V) :
    G.embedding (GW.Spaces.weightedDomainIsometry G (fiberWeightedInput G V h u)) = u.val :=
  G.embedding_product ⟨u.val,h u.property⟩

def fiberPhysicalFromUnshifted (u : (physicalNumberPower (1/2)).domain) : FiberPhysicalRoot :=
  fiberWeightedInput (physicalShiftedWeightGraph (1/2) (by norm_num))
    (physicalNumberPower (1/2)).domain (fun v hv => physicalRootNumber_domains_eq ▸ hv) u

lemma fiberPhysicalFromUnshifted_inclusion (u : (physicalNumberPower (1/2)).domain) :
    fiberPhysicalDomainInclusion (1/2) (by norm_num) (fiberPhysicalFromUnshifted u) = u.val :=
  fiberWeightedInput_embedding (physicalShiftedWeightGraph (1/2) (by norm_num))
    (physicalNumberPower (1/2)).domain (fun v hv => physicalRootNumber_domains_eq ▸ hv) u

lemma fiberPhysicalFromUnshifted_value (u : (physicalNumberPower (1/2)).domain) :
    (fiberPhysicalRootInput (fiberPhysicalFromUnshifted u)).val = u.val :=
  (fiberPhysicalDomainInclusion_root _).symm.trans (fiberPhysicalFromUnshifted_inclusion u)

lemma fiberCreation_original_input (K : BosonKernel ElectronL2) (u : (physicalNumberPower (1/2)).domain) :
    generalizedCreation K (generalizedCreationRootInput K u) =
      fiberGeneralizedCreator K (fiberPhysicalFromUnshifted u) := by
  let v := fiberPhysicalFromUnshifted u
  let a := generalizedCreationShiftedInput K (fiberPhysicalRootInput v)
  have hv : a.val = u.val := (generalizedCreationShiftedInput_val K _).trans (fiberPhysicalFromUnshifted_value u)
  have he : generalizedCreationRootInput K u = a := Subtype.ext hv.symm
  exact congrArg (generalizedCreation K).toFun he

lemma fiberAnnihilation_original_input (K : BosonKernel ElectronL2) (u : (physicalNumberPower (1/2)).domain) :
    generalizedAnnihilation K (fiberGeneralizedAnnihilationRootInput K u) =
      fiberGeneralizedAnnihilatorMap K (fiberPhysicalFromUnshifted u) := by
  have hg := fiberGeneralizedAnnihilatorMap_graph K (fiberPhysicalFromUnshifted u)
  rw [fiberPhysicalFromUnshifted_inclusion] at hg
  exact (generalizedAnnihilation K).mem_graph_snd_inj
    ((generalizedAnnihilation K).mem_graph (fiberGeneralizedAnnihilationRootInput K u)) hg rfl

lemma multiplicationKernel_fiberwise (F : GW.Space → OneBoson) (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hM : ∀ᵐ x ∂(volume : Measure GW.Space), ‖F x‖ ≤ M)
    (u : (physicalNumberPower (1/2)).domain) :
    ∃ g : GW.Space → FiberRootDomain, StronglyMeasurable g ∧ MemLp g 2 volume ∧
      (fun x => numberDomainInclusion Sector (1/2) (by norm_num) (g x)) =ᵐ[volume] u.val ∧
      generalizedCreation (fiberKernel F hF hM) (generalizedCreationRootInput (fiberKernel F hF hM) u) =ᵐ[volume]
        (fun x => fiberOrdinaryCreator (F x) (g x)) ∧
      generalizedAnnihilation (fiberKernel F hF hM) (fiberGeneralizedAnnihilationRootInput (fiberKernel F hF hM) u) =ᵐ[volume]
        (fun x => fiberOrdinaryAnnihilator (F x) (g x)) ∧
      MemLp (fun x => fiberOrdinaryCreator (F x) (g x)) 2 volume ∧
      MemLp (fun x => fiberOrdinaryAnnihilator (F x) (g x)) 2 volume := by
  let v := fiberPhysicalFromUnshifted u
  let g := fiberRootRepresentative v
  have hv : (fiberPhysicalRootInput v).val = u.val := fiberPhysicalFromUnshifted_value u
  have hr := fiberRootRepresentative_ambient v
  have hr' : (show Physical from fiberPhysicalRootInput v) = u.val := hv
  have hrU : (fun x => numberDomainInclusion Sector (1/2) (by norm_num) (g x)) =ᵐ[volume] u.val := by
    filter_upwards [hr] with x hx
    exact hx.trans (congrArg (fun z : Physical => z x) hr')
  refine ⟨g,Lp.stronglyMeasurable g,Lp.memLp g,hrU,?_,?_,
    fiberPointwiseCreator_memLp F hF hM v,fiberPointwiseAnnihilator_memLp F hF hM v⟩
  · rw [fiberCreation_original_input,fiberCreation_identification_root F hF hM v]
    exact fiberCreatorClass_ae F hF hM v
  · rw [fiberAnnihilation_original_input,fiberAnnihilationMap_identification_root F hF hM v]
    exact fiberAnnihilatorClass_ae F hF hM v


end GW.Fock
