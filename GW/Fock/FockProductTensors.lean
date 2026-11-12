module
public import GW.Fock.FockAmplification
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ENNReal
namespace GW.Fock

abbrev OneBoson := Lp ℂ 2 (volume : Measure GW.Space)

def rawTensorRep (n : ℕ) (f : Fin n → OneBoson) (k : Coordinates n) : ℂ := ∏ i, f i (k i)

lemma rawTensorRep_strong (n : ℕ) (f : Fin n → OneBoson) : StronglyMeasurable (rawTensorRep n f) := by
  apply Finset.stronglyMeasurable_fun_prod
  intro i _
  exact (Lp.stronglyMeasurable (f i)).comp_measurable (measurable_pi_apply i)

lemma rawTensorRep_memLp (n : ℕ) (f : Fin n → OneBoson) :
    MemLp (rawTensorRep n f) 2 (sectorMeasure n) := by
  apply (memLp_two_iff_integrable_sq_norm (rawTensorRep_strong n f).aestronglyMeasurable).mpr
  have hi := Integrable.fintype_prod (fun i =>
    (Lp.memLp (f i)).integrable_norm_pow (p := 2) (by norm_num))
  apply hi.congr
  exact Eventually.of_forall (fun k => by simp [rawTensorRep,norm_prod,Finset.prod_pow])

def rawTensor (n : ℕ) (f : Fin n → OneBoson) : AmbientSector n := (rawTensorRep_memLp n f).toLp _

lemma rawTensor_ae (n : ℕ) (f : Fin n → OneBoson) :
    rawTensor n f =ᵐ[sectorMeasure n] rawTensorRep n f := MemLp.coeFn_toLp _

lemma rawTensor_norm (n : ℕ) (f : Fin n → OneBoson) : ‖rawTensor n f‖ = ∏ i, ‖f i‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (Finset.prod_nonneg (fun i _ => norm_nonneg (f i)))).mp
  rw [GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
  calc
    _ = ∫ k : Coordinates n, ∏ i, ‖f i (k i)‖^2 ∂sectorMeasure n := by
      apply integral_congr_ae
      filter_upwards [rawTensor_ae n f] with k hk
      rw [hk]
      simp only [rawTensorRep,norm_prod,Finset.prod_pow]
    _ = ∏ i, ∫ k : GW.Space, ‖f i k‖^2 :=
      integral_fintype_prod_eq_prod (μ := fun _ : Fin n => (volume : Measure GW.Space))
        (fun (i : Fin n) (k : GW.Space) => ‖f i k‖^2)
    _ = (∏ i, ‖f i‖)^2 := by
      simp_rw [← GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
      rw [Finset.prod_pow]

lemma rawTensorRep_change (n : ℕ) (f : Fin n → OneBoson) (r : Fin n → GW.Space → ℂ)
    (hr : ∀ i, (f i : GW.Space → ℂ) =ᵐ[volume] r i) :
    rawTensorRep n f =ᵐ[sectorMeasure n] fun k => ∏ i, r i (k i) := by
  have h i : ∀ᵐ k ∂sectorMeasure n, f i (k i) = r i (k i) :=
    (Measure.quasiMeasurePreserving_eval (fun _ : Fin n => (volume : Measure GW.Space)) i).ae (hr i)
  filter_upwards [ae_all_iff.mpr h] with k hk
  exact Finset.prod_congr rfl (fun i _ => hk i)

lemma rawTensor_inner_integrable (n : ℕ) (f g : Fin n → OneBoson) :
    Integrable (fun k : Coordinates n => ∏ i, (starRingEnd ℂ) (f i (k i)) * g i (k i)) (sectorMeasure n) := by
  exact Integrable.fintype_prod (μ := fun _ : Fin n => (volume : Measure GW.Space))
    (f := fun i k => (starRingEnd ℂ) (f i k) * g i k)
    (fun i => by simpa only [RCLike.inner_apply,mul_comm] using (L2.integrable_inner (𝕜 := ℂ) (f i) (g i)))

lemma rawTensor_inner (n : ℕ) (f g : Fin n → OneBoson) :
    ⟪rawTensor n f,rawTensor n g⟫_ℂ = ∏ i, ⟪f i,g i⟫_ℂ := by
  have hi := rawTensor_inner_integrable n f g
  rw [L2.inner_def]
  calc
    _ = ∫ k : Coordinates n, ∏ i, (starRingEnd ℂ) (f i (k i)) * g i (k i) ∂sectorMeasure n := by
      apply integral_congr_ae
      filter_upwards [rawTensor_ae n f,rawTensor_ae n g] with k hf hg
      rw [hf,hg]
      simp only [rawTensorRep, RCLike.inner_apply, map_prod, Finset.prod_mul_distrib]
      exact mul_comm _ _
    _ = ∏ i, ∫ k : GW.Space, (starRingEnd ℂ) (f i k) * g i k :=
      integral_fintype_prod_eq_prod (μ := fun _ : Fin n => (volume : Measure GW.Space))
        (fun (i : Fin n) (k : GW.Space) => (starRingEnd ℂ) (f i k) * g i k)
    _ = ∏ i, ⟪f i,g i⟫_ℂ := by
      apply Finset.prod_congr rfl
      intro i _
      simpa only [RCLike.inner_apply,mul_comm] using (L2.inner_def (𝕜 := ℂ) (f i) (g i)).symm
lemma rawTensorRep_update (n : ℕ) [DecidableEq (Fin n)] (f : Fin n → OneBoson) (i : Fin n) (v : OneBoson) (k : Coordinates n) :
    rawTensorRep n (Function.update f i v) k = v (k i) * ∏ j ∈ Finset.univ \ {i}, f j (k j) := by
  classical
  have he : (fun j => Function.update f i v j (k j)) =
      Function.update (fun j => f j (k j)) i (v (k i)) := by
    funext j
    by_cases hj : j = i
    · subst j; simp
    · simp [Function.update_of_ne hj]
  unfold rawTensorRep
  rw [he]
  exact Finset.prod_update_of_mem (Finset.mem_univ i) _ _

lemma rawTensor_update_add (n : ℕ) [DecidableEq (Fin n)] (f : Fin n → OneBoson) (i : Fin n) (v w : OneBoson) :
    rawTensor n (Function.update f i (v+w)) = rawTensor n (Function.update f i v) + rawTensor n (Function.update f i w) := by
  apply Lp.ext
  filter_upwards [rawTensor_ae n (Function.update f i (v+w)),rawTensor_ae n (Function.update f i v),
    rawTensor_ae n (Function.update f i w),
    (Measure.quasiMeasurePreserving_eval (fun _ : Fin n => (volume : Measure GW.Space)) i).ae (Lp.coeFn_add v w),
    Lp.coeFn_add (rawTensor n (Function.update f i v)) (rawTensor n (Function.update f i w))] with k h₁ h₂ h₃ h₄ h₅
  simp only [Pi.add_apply] at h₄ h₅
  rw [h₁,h₅,h₂,h₃,rawTensorRep_update,rawTensorRep_update,rawTensorRep_update,h₄,add_mul]

lemma rawTensor_update_smul (n : ℕ) [DecidableEq (Fin n)] (f : Fin n → OneBoson) (i : Fin n) (c : ℂ) (v : OneBoson) :
    rawTensor n (Function.update f i (c • v)) = c • rawTensor n (Function.update f i v) := by
  apply Lp.ext
  filter_upwards [rawTensor_ae n (Function.update f i (c • v)),rawTensor_ae n (Function.update f i v),
    (Measure.quasiMeasurePreserving_eval (fun _ : Fin n => (volume : Measure GW.Space)) i).ae (Lp.coeFn_smul c v),
    Lp.coeFn_smul c (rawTensor n (Function.update f i v))] with k h₁ h₂ h₃ h₄
  simp only [Pi.smul_apply] at h₃ h₄
  rw [h₁,h₄,h₂,rawTensorRep_update,rawTensorRep_update,h₃,smul_eq_mul,smul_eq_mul,mul_assoc]

def rawTensorMultilinear (n : ℕ) : MultilinearMap (RingHom.id ℂ) (fun _ : Fin n => OneBoson) (AmbientSector n) where
  toFun := rawTensor n
  map_update_add' := rawTensor_update_add n
  map_update_smul' := rawTensor_update_smul n

def rawTensorContinuous (n : ℕ) : ContinuousMultilinearMap ℂ (fun _ : Fin n => OneBoson) (AmbientSector n) :=
  (rawTensorMultilinear n).mkContinuous 1 (fun f => by
    change ‖rawTensor n f‖ ≤ _
    rw [rawTensor_norm,one_mul])

def symmetricTensorContinuous (n : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin (n+1) => OneBoson) (Sector (n+1)) :=
  (symmetricProjection (n+1)).compContinuousMultilinearMap (rawTensorContinuous (n+1))

lemma symmetricTensor_norm (n : ℕ) (f : Fin (n+1) → OneBoson) :
    ‖symmetricTensorContinuous n f‖ ≤ ∏ i, ‖f i‖ := by
  change ‖symmetrizer (n+1) (rawTensor (n+1) f)‖ ≤ _
  exact (symmetrizer_norm_le _ _).trans (rawTensor_norm _ _).le

def mixedFactors (n m : ℕ) (f g : Fin n → OneBoson) (i : Fin n) : OneBoson :=
  if i.val < m then g i else f i

lemma rawTensor_step_norm (n : ℕ) (f g : Fin n → OneBoson) (j : Fin n) :
    ‖rawTensor n (mixedFactors n j.val f g) - rawTensor n (mixedFactors n (j.val+1) f g)‖ =
      ‖f j - g j‖ * ∏ i ∈ Finset.univ \ {j}, if i < j then ‖g i‖ else ‖f i‖ := by
  classical
  have h0 : Function.update (mixedFactors n j.val f g) j (f j) = mixedFactors n j.val f g := by
    funext i
    by_cases hi : i = j
    · subst i; simp [mixedFactors]
    · simp [Function.update_of_ne hi]
  have h1 : Function.update (mixedFactors n j.val f g) j (g j) = mixedFactors n (j.val+1) f g := by
    funext i
    by_cases hi : i = j
    · subst i; simp [mixedFactors]
    · have hv : i.val ≠ j.val := fun h => hi (Fin.ext h)
      have he : i.val < j.val + 1 ↔ i.val < j.val := by omega
      simp [Function.update_of_ne hi,mixedFactors,he]
  have he := (rawTensorMultilinear n).map_update_sub (mixedFactors n j.val f g) j (f j) (g j)
  change rawTensor n (Function.update (mixedFactors n j.val f g) j (f j-g j)) =
    rawTensor n (Function.update (mixedFactors n j.val f g) j (f j)) -
    rawTensor n (Function.update (mixedFactors n j.val f g) j (g j)) at he
  rw [h0,h1] at he
  rw [← he,rawTensor_norm]
  have hn : (fun i => ‖Function.update (mixedFactors n j.val f g) j (f j-g j) i‖) =
      Function.update (fun i => ‖mixedFactors n j.val f g i‖) j ‖f j-g j‖ := by
    funext i
    by_cases hi : i = j
    · subst i; simp
    · simp [Function.update_of_ne hi]
  rw [hn,Finset.prod_update_of_mem (Finset.mem_univ j)]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i < j <;> simp [mixedFactors,hi]

lemma rawTensor_telescoping (n : ℕ) (f g : Fin n → OneBoson) :
    ‖rawTensor n f - rawTensor n g‖ ≤
      ∑ j : Fin n, ‖f j-g j‖ * ∏ i ∈ Finset.univ \ {j}, if i < j then ‖g i‖ else ‖f i‖ := by
  classical
  have h0 : mixedFactors n 0 f g = f := by funext i; simp [mixedFactors]
  have hn : mixedFactors n n f g = g := by funext i; simp [mixedFactors,i.isLt]
  have he : (∑ j : Fin n, (rawTensor n (mixedFactors n j.val f g) -
      rawTensor n (mixedFactors n (j.val+1) f g))) = rawTensor n f - rawTensor n g := by
    rw [Fin.sum_univ_eq_sum_range (fun m => rawTensor n (mixedFactors n m f g) - rawTensor n (mixedFactors n (m+1) f g)),
      Finset.sum_range_sub',h0,hn]
  rw [← he]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => (rawTensor_step_norm n f g j).le))

lemma tensor_ordered_product (n : ℕ) (a b : Fin n → ℝ) (j : Fin n) :
    (∏ i ∈ Finset.univ \ {j}, if i < j then b i else a i) =
      (∏ i ∈ Finset.univ.filter (fun i => i < j), b i) *
      ∏ i ∈ Finset.univ.filter (fun i => j < i), a i := by
  classical
  rw [Finset.prod_ite]
  congr 1 <;> congr 1 <;> ext i <;>
    simp only [Finset.mem_filter,Finset.mem_sdiff,Finset.mem_univ,Finset.mem_singleton,
      true_and,Fin.ext_iff,Fin.lt_def] <;> omega

/-- The source's ordered telescoping inequality with the earlier/later products explicit. -/
lemma rawTensor_telescoping_ordered (n : ℕ) (f g : Fin n → OneBoson) :
    ‖rawTensor n f-rawTensor n g‖ ≤ ∑ j : Fin n, ‖f j-g j‖ *
      (∏ i ∈ Finset.univ.filter (fun i => i < j), ‖g i‖) *
      ∏ i ∈ Finset.univ.filter (fun i => j < i), ‖f i‖ := by
  have h := rawTensor_telescoping n f g
  simpa only [tensor_ordered_product,mul_assoc] using h

lemma rawTensorContinuous_norm (n : ℕ) : ‖rawTensorContinuous n‖ ≤ 1 :=
  (rawTensorMultilinear n).mkContinuous_norm_le zero_le_one (fun f => by
    change ‖rawTensor n f‖ ≤ 1 * ∏ i, ‖f i‖
    rw [rawTensor_norm,one_mul])

lemma symmetricTensorContinuous_norm (n : ℕ) : ‖symmetricTensorContinuous n‖ ≤ 1 := by
  apply ContinuousMultilinearMap.opNorm_le_bound zero_le_one
  intro f
  simpa only [one_mul] using symmetricTensor_norm n f

lemma symmetricTensor_telescoping (n : ℕ) (f g : Fin (n+1) → OneBoson) :
    ‖symmetricTensorContinuous n f - symmetricTensorContinuous n g‖ ≤
      ∑ j : Fin (n+1), ‖f j-g j‖ * ∏ i ∈ Finset.univ \ {j}, if i < j then ‖g i‖ else ‖f i‖ := by
  change ‖symmetrizer (n+1) (rawTensor (n+1) f) - symmetrizer (n+1) (rawTensor (n+1) g)‖ ≤ _
  rw [← map_sub]
  exact (symmetrizer_norm_le _ _).trans (rawTensor_telescoping (n+1) f g)

lemma rawTensor_split (n : ℕ) (f : Fin (n+1) → OneBoson) :
    splitUnitary n 0 (rawTensor (n+1) f) =
      productFunction volume (sectorMeasure n) (f 0) (rawTensor n (fun i => f i.succ)) := by
  apply Lp.ext
  filter_upwards [splitUnitary_ae n 0 (rawTensor (n+1) f),
    (splitCoordinates_inverse_preserving n 0).quasiMeasurePreserving.ae (rawTensor_ae (n+1) f),
    productFunction_ae volume (sectorMeasure n) (f 0) (rawTensor n (fun i => f i.succ)),
    (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure GW.Space)) (ν := sectorMeasure n)).ae
      (rawTensor_ae n (fun i => f i.succ))] with p h₁ h₂ h₃ h₄
  rw [h₁,h₂,h₃,h₄]
  simp only [rawTensorRep,Fin.prod_univ_succ,smul_eq_mul]
  congr 1

lemma rawTensor_zero (f : Fin 0 → OneBoson) : rawTensor 0 f = vacuumAdapter (1 : ℂ) := by
  apply Lp.ext
  filter_upwards [rawTensor_ae 0 f,vacuumAdapter_ae (1 : ℂ)] with k hk h1
  rw [hk]
  change rawTensorRep 0 f k = vacuumAdapterIsometry (1 : ℂ) k
  rw [h1]
  simp [rawTensorRep]

def rawPrepend (n : ℕ) (γ : OneBoson) : AmbientSector n →L[ℂ] AmbientSector (n+1) :=
  (splitUnitary n 0).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((productUnitary volume (sectorMeasure n)).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (tensorEmbedding volume γ))

lemma rawPrepend_tensor (n : ℕ) (γ : OneBoson) (g : Fin n → OneBoson) :
    rawPrepend n γ (rawTensor n g) = rawTensor (n+1) (Fin.cons γ g) := by
  apply (splitUnitary n 0).injective
  change splitUnitary n 0 ((splitUnitary n 0).symm
    (productUnitary volume (sectorMeasure n) (tensorEmbedding volume γ (rawTensor n g)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply,productUnitary_tensor,rawTensor_split]
  simp only [Fin.cons_zero,Fin.cons_succ]

/-- Density of raw products, by repeated product identification and the proved rectangle criterion. -/
lemma rawTensor_dense_criterion (n : ℕ) (V : Submodule ℂ (AmbientSector n))
    (hV : IsClosed (V : Set (AmbientSector n))) (hT : ∀ f : Fin n → OneBoson, rawTensor n f ∈ V) : V = ⊤ := by
  induction n with
  | zero =>
    have h1 : vacuumAdapter (1 : ℂ) ∈ V := by
      rw [← rawTensor_zero (fun i => Fin.elim0 i)]
      exact hT _
    apply top_unique
    intro v _
    obtain ⟨c,rfl⟩ := vacuumAdapter.surjective v
    have h := V.smul_mem c h1
    simpa only [← map_smul,smul_eq_mul,mul_one] using h
  | succ n ih =>
    let U := splitUnitary n 0
    let W : Submodule ℂ (Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure n))) :=
      V.comap U.symm.toLinearMap
    have hW : IsClosed (W : Set (Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure n)))) := hV.preimage U.symm.continuous
    have htop : W = ⊤ := by
      apply rectangle_dense_criterion volume (sectorMeasure n) W hW
      intro A B hA hB hAf hBf e
      let γ : OneBoson := indicatorConstLp 2 hA hAf (1 : ℂ)
      let L := rawPrepend n γ
      let Z : Submodule ℂ (AmbientSector n) := V.comap L.toLinearMap
      have hZ : IsClosed (Z : Set (AmbientSector n)) := hV.preimage L.continuous
      have hz : Z = ⊤ := by
        apply ih Z hZ
        intro g
        change rawPrepend n γ (rawTensor n g) ∈ V
        rw [rawPrepend_tensor]
        exact hT _
      have hm : L (indicatorConstLp 2 hB hBf e) ∈ V := by
        have hh : indicatorConstLp 2 hB hBf e ∈ Z := hz ▸ Submodule.mem_top
        exact hh
      change U.symm (indicatorConstLp 2 (hA.prod hB) _ e) ∈ V
      change U.symm (productUnitary volume (sectorMeasure n)
        (tensorEmbedding volume γ (indicatorConstLp 2 hB hBf e))) ∈ V at hm
      rw [productUnitary_tensor,productFunction_indicator] at hm
      exact hm
    apply top_unique
    intro v _
    have hm : U v ∈ W := htop ▸ Submodule.mem_top
    change U.symm (U v) ∈ V at hm
    simpa only [LinearIsometryEquiv.symm_apply_apply] using hm

lemma rawTensor_span_dense (n : ℕ) :
    Dense (Submodule.span ℂ (Set.range (rawTensor n)) : Set (AmbientSector n)) := by
  have htop : (Submodule.span ℂ (Set.range (rawTensor n))).topologicalClosure = ⊤ := by
    apply rawTensor_dense_criterion n _ (Submodule.isClosed_topologicalClosure _)
    intro f
    exact (Submodule.span ℂ (Set.range (rawTensor n))).le_topologicalClosure (Submodule.subset_span (Set.mem_range_self f))
  rw [dense_iff_closure_eq]
  exact congrArg (fun S : Submodule ℂ (AmbientSector n) => (S : Set (AmbientSector n))) htop

/-- Approximation of each of the finitely many factors uses the constructed joint continuity. -/
lemma rawTensor_dense_subspace_criterion (n : ℕ) (D : Submodule ℂ OneBoson)
    (hD : Dense (D : Set OneBoson)) (V : Submodule ℂ (AmbientSector n))
    (hV : IsClosed (V : Set (AmbientSector n)))
    (hT : ∀ f : Fin n → D, rawTensor n (fun i => (f i : OneBoson)) ∈ V) : V = ⊤ := by
  apply rawTensor_dense_criterion n V hV
  intro f
  have hd : DenseRange (fun g : Fin n → D => (fun i => (g i : OneBoson))) :=
    DenseRange.piMap (fun _ => (denseRange_subtype_val.mpr hD))
  exact hd.induction_on f (hV.preimage (rawTensorContinuous n).cont) hT

lemma rawTensor_dense_subspace (n : ℕ) (D : Submodule ℂ OneBoson) (hD : Dense (D : Set OneBoson)) :
    Dense (Submodule.span ℂ (Set.range (fun f : Fin n → D => rawTensor n (fun i => (f i : OneBoson)))) : Set (AmbientSector n)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply rawTensor_dense_subspace_criterion n D hD _ (Submodule.isClosed_topologicalClosure _)
  intro f
  exact (Submodule.span ℂ (Set.range (fun f : Fin n → D => rawTensor n (fun i => (f i : OneBoson))))).le_topologicalClosure
    (Submodule.subset_span (Set.mem_range_self f))

lemma symmetricTensor_dense_subspace_criterion (n : ℕ) (D : Submodule ℂ OneBoson)
    (hD : Dense (D : Set OneBoson)) (V : Submodule ℂ (Sector (n+1)))
    (hV : IsClosed (V : Set (Sector (n+1))))
    (hT : ∀ f : Fin (n+1) → D, symmetricTensorContinuous n (fun i => (f i : OneBoson)) ∈ V) : V = ⊤ := by
  let P := symmetricProjection (n+1)
  let C : Submodule ℂ (AmbientSector (n+1)) := V.comap P.toLinearMap
  have hC : IsClosed (C : Set (AmbientSector (n+1))) := hV.preimage P.continuous
  have ht : C = ⊤ := by
    apply rawTensor_dense_subspace_criterion (n+1) D hD C hC
    intro f
    exact hT f
  apply top_unique
  intro u _
  let u' : symmetricSector (n+1) := u
  have hu : u'.val ∈ C := ht ▸ Submodule.mem_top
  have he : P u'.val = u' := by
    apply Subtype.ext
    exact symmetrizer_of_fixed (n+1) u'.val u'.property
  change P u'.val ∈ V at hu
  rwa [he] at hu

lemma symmetricTensor_dense_subspace (n : ℕ) (D : Submodule ℂ OneBoson) (hD : Dense (D : Set OneBoson)) :
    Dense (Submodule.span ℂ (Set.range (fun f : Fin (n+1) → D => symmetricTensorContinuous n (fun i => (f i : OneBoson)))) :
      Set (Sector (n+1))) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply symmetricTensor_dense_subspace_criterion n D hD _ (Submodule.isClosed_topologicalClosure _)
  intro f
  exact (Submodule.span ℂ (Set.range (fun f : Fin (n+1) → D => symmetricTensorContinuous n (fun i => (f i : OneBoson))))).le_topologicalClosure
    (Submodule.subset_span (Set.mem_range_self f))

def vacuumProductTensor : Sector 0 := (1 : ℂ)

lemma vacuumProductTensor_norm : ‖vacuumProductTensor‖ = 1 := by
  change ‖(1 : ℂ)‖ = 1
  exact norm_one

lemma vacuumProductTensor_span : Submodule.span ℂ ({vacuumProductTensor} : Set (Sector 0)) = ⊤ := by
  change Submodule.span ℂ ({(1 : ℂ)} : Set ℂ) = ⊤
  apply top_unique
  intro z _
  apply Submodule.mem_span_singleton.mpr
  exact ⟨(z : ℂ),by change (z : ℂ) • (1 : ℂ) = (z : ℂ); simp⟩

end GW.Fock
