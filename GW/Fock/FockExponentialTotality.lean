module
public import GW.Fock.FockCoherentJets
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace BigOperators ENNReal
namespace GW.Fock

lemma exponentialCoefficient_tail_bound (c : ℕ → ℂ) (hc : Summable (fun n => ‖c n‖))
    (m : ℕ) (t : ℝ) (ht : |t| ≤ 1) :
    ‖∑' n, c (m+n+1)*(t:ℂ)^(n+1)‖ ≤ |t| *(∑' n, ‖c (m+n+1)‖) := by
  have hs : Summable (fun n => ‖c (m+n+1)‖) := by
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using (summable_nat_add_iff (m+1)).mpr hc
  have hb (n : ℕ) : ‖c (m+n+1)*(t:ℂ)^(n+1)‖ ≤ |t| *‖c (m+n+1)‖ := by
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,pow_succ]
    calc
      _ = |t| *(‖c (m+n+1)‖*|t| ^n) := by ring
      _ ≤ |t| *(‖c (m+n+1)‖*1) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg t) ht) (norm_nonneg _)) (abs_nonneg t)
      _ = _ := by rw [mul_one]
  have hnorm : Summable (fun n => ‖c (m+n+1)*(t:ℂ)^(n+1)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb (hs.mul_left |t|)
  calc
    _ ≤ ∑' n, ‖c (m+n+1)*(t:ℂ)^(n+1)‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n, |t| *‖c (m+n+1)‖ := Summable.tsum_le_tsum hb hnorm (hs.mul_left |t|)
    _ = _ := by rw [tsum_mul_left]

lemma exponentialCoefficient_tail_tendsto (c : ℕ → ℂ) (hc : Summable (fun n => ‖c n‖)) (m : ℕ) :
    Tendsto (fun t : ℝ => ‖∑' n, c (m+n+1)*(t:ℂ)^(n+1)‖) (𝓝 0) (𝓝 0) := by
  have hb : ∀ᶠ t : ℝ in 𝓝 0, |t| ≤ 1 := by
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) (by norm_num : (0:ℝ) < 1)] with t ht
    exact (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht : |t| < 1).le
  have hz : Tendsto (fun t : ℝ => |t| *(∑' n, ‖c (m+n+1)‖)) (𝓝 0) (𝓝 0) := by
    simpa only [abs_zero,zero_mul] using ((continuous_abs.tendsto (0:ℝ)).mul_const (∑' n, ‖c (m+n+1)‖))
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hz
  filter_upwards [hb] with t ht
  exact exponentialCoefficient_tail_bound c hc m t ht

lemma exponentialCoefficient_power_summable (c : ℕ → ℂ) (hc : Summable (fun n => ‖c n‖))
    (t : ℝ) (ht : |t| ≤ 1) : Summable (fun n => ‖c n*(t:ℂ)^n‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hc
  intro n
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg t) ht) (norm_nonneg _)).trans_eq (mul_one _)

lemma exponentialCoefficient_split (c : ℕ → ℂ) (hc : Summable (fun n => ‖c n‖))
    (m : ℕ) (hp : ∀ j < m, c j = 0) (t : ℝ) (ht : |t| ≤ 1) :
    (∑' n, c n*(t:ℂ)^n) = (t:ℂ)^m*(c m+∑' n, c (m+n+1)*(t:ℂ)^(n+1)) := by
  let f : ℕ → ℂ := fun n => c n*(t:ℂ)^n
  have hs : Summable f := (exponentialCoefficient_power_summable c hc t ht).of_norm
  have hsum := hs.sum_add_tsum_nat_add m
  have hprefix : (∑ j ∈ Finset.range m, f j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    dsimp only [f]
    rw [hp j (Finset.mem_range.mp hj),zero_mul]
  rw [hprefix,zero_add] at hsum
  change (∑' n, f n) = _
  rw [← hsum]
  have hf : (fun n => f (n+m)) = fun n => (t:ℂ)^m*(c (m+n)*(t:ℂ)^n) := by
    funext n
    dsimp only [f]
    rw [Nat.add_comm n m,pow_add]
    ring
  rw [hf,tsum_mul_left]
  congr 1
  have hcs : Summable (fun n => ‖c (m+n)‖) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff m).mpr hc
  have hrest := (exponentialCoefficient_power_summable (fun n => c (m+n)) hcs t ht).of_norm.sum_add_tsum_nat_add 1
  simpa only [Finset.sum_range_one,add_zero,pow_zero,mul_one,Nat.add_assoc] using hrest.symm

lemma exponentialCoefficient_unique (c : ℕ → ℂ) (hc : Summable (fun n => ‖c n‖))
    (hz : ∀ t : ℝ, |t| ≤ 1 → (∑' n, c n*(t:ℂ)^n) = 0) :
    ∀ m, c m = 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    let t : ℕ → ℝ := fun j => 1 / ((j:ℝ)+1)
    have ht (j : ℕ) : |t j| ≤ 1 := by
      dsimp only [t]
      rw [abs_of_pos (by positivity)]
      exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) j])
    have htn (j : ℕ) : (t j : ℂ) ^ m ≠ 0 := by
      apply pow_ne_zero
      exact_mod_cast (show t j ≠ 0 by dsimp [t]; positivity)
    have he (j : ℕ) : c m + ∑' n, c (m+n+1)*(t j:ℂ)^(n+1) = 0 := by
      have h := exponentialCoefficient_split c hc m ih (t j) (ht j)
      rw [hz (t j) (ht j)] at h
      exact (mul_eq_zero.mp h.symm).resolve_left (htn j)
    have hn (j : ℕ) : ‖∑' n, c (m+n+1)*(t j:ℂ)^(n+1)‖ = ‖c m‖ := by
      have h := eq_neg_of_add_eq_zero_left (he j)
      rw [h, norm_neg]
    have hlim : Tendsto (fun j => ‖∑' n, c (m+n+1)*(t j:ℂ)^(n+1)‖) atTop (𝓝 0) :=
      (exponentialCoefficient_tail_tendsto c hc m).comp tendsto_one_div_add_atTop_nhds_zero_nat
    simp_rw [hn] at hlim
    exact norm_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hlim)


def exponentialSign (b : Bool) : ℂ := if b then 1 else -1
lemma exponentialSign_not (b : Bool) : exponentialSign (!b) = -exponentialSign b := by
  cases b <;> norm_num [exponentialSign]
lemma exponentialSign_sq (b : Bool) : exponentialSign b * exponentialSign b = 1 := by
  cases b <;> norm_num [exponentialSign]

lemma exponentialSign_product_flip {n : ℕ} (δ : Fin n → Bool) (i : Fin n) :
    (∏ j, exponentialSign (Function.update δ i (!δ i) j)) = -(∏ j, exponentialSign (δ j)) := by
  classical
  have hf : (fun j => exponentialSign (Function.update δ i (!δ i) j)) =
      Function.update (fun j => exponentialSign (δ j)) i (exponentialSign (!δ i)) := by
    funext j
    by_cases h : j = i <;> simp [h]
  rw [hf, Finset.prod_update_of_mem (Finset.mem_univ i), exponentialSign_not]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp [Finset.sdiff_singleton_eq_erase]

lemma exponentialSign_missing_sum {n : ℕ} (k : Fin n → Fin n)
    (i : Fin n) (hi : ∀ j, k j ≠ i) :
    (∑ δ : Fin n → Bool, (∏ j, exponentialSign (δ j)) * (∏ j, exponentialSign (δ (k j)))) = 0 := by
  classical
  apply Finset.sum_ninvolution (fun δ => Function.update δ i (!δ i))
  · intro δ
    have hf : (fun j => exponentialSign (Function.update δ i (!δ i) (k j))) =
        fun j => exponentialSign (δ (k j)) := by
      funext j
      simp [Function.update_of_ne (hi j)]
    rw [exponentialSign_product_flip, hf]
    ring
  · intro δ _ he
    have h := congrFun he i
    simpa using h
  · intro δ
    exact Finset.mem_univ _
  · intro δ
    funext j
    by_cases h : j = i
    · subst j; simp
    · simp [h]

lemma exponentialSign_assignment_sum {n : ℕ} (k : Fin n → Fin n) :
    (∑ δ : Fin n → Bool, (∏ j, exponentialSign (δ j)) * (∏ j, exponentialSign (δ (k j)))) =
      if Function.Bijective k then (2:ℂ)^n else 0 := by
  classical
  by_cases hk : Function.Bijective k
  · rw [if_pos hk]
    have he (δ : Fin n → Bool) :
        (∏ j, exponentialSign (δ j)) * (∏ j, exponentialSign (δ (k j))) = 1 := by
      rw [hk.prod_comp (fun j => exponentialSign (δ j)), ← Finset.prod_mul_distrib]
      simp only [exponentialSign_sq, Finset.prod_const_one]
    simp_rw [he]
    simp [Fintype.card_fun]
  · rw [if_neg hk]
    have hns : ¬Function.Surjective k := by
      intro hs
      exact hk ⟨Finite.injective_iff_surjective.mpr hs, hs⟩
    unfold Function.Surjective at hns
    push_neg at hns
    obtain ⟨i, hi⟩ := hns
    exact exponentialSign_missing_sum k i hi

lemma exponentialSign_multilinear_expansion {n : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℂ V]
    (T : MultilinearMap (RingHom.id ℂ) (fun _ : Fin n => OneBoson) V) (g : Fin n → OneBoson) :
    (∑ δ : Fin n → Bool, (∏ j, exponentialSign (δ j)) •
      T (fun _ => ∑ j, exponentialSign (δ j) • g j)) =
    ∑ k : Fin n → Fin n, (if Function.Bijective k then (2:ℂ)^n else 0) • T (fun j => g (k j)) := by
  classical
  simp_rw [T.map_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp_rw [T.map_smul_univ, smul_smul]
  simp only [RingHom.id_apply]
  rw [← Finset.sum_smul, exponentialSign_assignment_sum]

def exponentialPermutationEquiv (n : ℕ) :
    Equiv.Perm (Fin n) ≃ {k : Fin n → Fin n // Function.Bijective k} where
  toFun σ := ⟨σ, σ.bijective⟩
  invFun k := Equiv.ofBijective k.val k.property
  left_inv σ := by ext i; rfl
  right_inv k := by rfl

lemma exponentialTensor_sign_polarization (n : ℕ) (g : Fin n → OneBoson) :
    (∑ δ : Fin n → Bool, (∏ j, exponentialSign (δ j)) •
      coherentJetSectorTensor n (fun _ => ∑ j, exponentialSign (δ j) • g j)) =
      ((2:ℂ)^n * (n.factorial:ℂ)) • coherentJetSectorTensor n g := by
  classical
  change (∑ δ : Fin n → Bool, (∏ j, exponentialSign (δ j)) •
    (coherentJetSectorTensor n).toMultilinearMap (fun _ => ∑ j, exponentialSign (δ j) • g j)) = _
  rw [exponentialSign_multilinear_expansion]
  have he (k : Fin n → Fin n) :
      (if Function.Bijective k then (2:ℂ)^n else 0) • coherentJetSectorTensor n (fun j => g (k j)) =
      if Function.Bijective k then (2:ℂ)^n • coherentJetSectorTensor n g else 0 := by
    split_ifs with hk
    · have h := coherentJetSectorTensor_permutation n g (Equiv.ofBijective k hk).symm
      simpa using congrArg (fun v => (2:ℂ)^n • v) h
    · simp
  change (∑ k : Fin n → Fin n, (if Function.Bijective k then (2:ℂ)^n else 0) •
    coherentJetSectorTensor n (fun j => g (k j))) = _
  simp_rw [he]
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := Function.Bijective) _ (fun _ => by simp) (fun _ => (2:ℂ)^n • coherentJetSectorTensor n g)]
  rw [← (exponentialPermutationEquiv n).sum_comp]
  simp [Fintype.card_perm, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_comm]


def exponentialGraph (r : ℝ) (hr : 0 ≤ r) (g : OneBoson) : Carrier :=
  numberDomainIsometry Sector r hr (coherentExponentialWeighted r hr g)

set_option backward.isDefEq.respectTransparency.types false in
lemma exponentialGraph_apply (r : ℝ) (hr : 0 ≤ r) (g : OneBoson) (n : ℕ) :
    exponentialGraph r hr g n = (↑(((n:ℝ)+1)^r) : ℂ) • exponentialRaw g n := by
  change scalarDiagonal Sector (fun j => ((j:ℝ)+1)^r) _ n = _
  rw [scalarDiagonal_apply]
  congr 1
  exact congrArg (fun v : Carrier => v n) (coherentExponentialWeighted_ambient r hr g)

lemma exponentialGraph_inner_norm_summable (r : ℝ) (hr : 0 ≤ r) (g : OneBoson) (w : Carrier) :
    Summable (fun n => ‖⟪w n, exponentialGraph r hr g n⟫_ℂ‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => norm_inner_le_norm (𝕜 := ℂ) _ _) (lp.summable_mul ?_ w (exponentialGraph r hr g))
  rw [Real.holderConjugate_iff]
  norm_num

lemma tensorPower_smul (n : ℕ) (z : ℂ) (g : OneBoson) :
    tensorPower n (z • g) = z^n • tensorPower n g := by
  rw [← coherentJetSectorTensor_diagonal, ← coherentJetSectorTensor_diagonal]
  rw [ContinuousMultilinearMap.map_smul_univ]
  simp

lemma exponentialGraph_smul_apply (r : ℝ) (hr : 0 ≤ r) (g : OneBoson) (t : ℝ) (n : ℕ) :
    exponentialGraph r hr (t • g) n = (t:ℂ)^n • exponentialGraph r hr g n := by
  rw [exponentialGraph_apply, exponentialGraph_apply]
  unfold exponentialRaw
  have hs : t • g = (t:ℂ) • g := by
    exact (IsScalarTower.algebraMap_smul ℂ t g).symm
  rw [hs, tensorPower_smul]
  simp only [smul_smul]
  congr 1
  ring

lemma exponentialGraph_orthogonal_coefficient (r : ℝ) (hr : 0 ≤ r)
    (D : Submodule ℂ OneBoson) (w : Carrier)
    (hw : ∀ g ∈ D, ⟪w, exponentialGraph r hr g⟫_ℂ = 0)
    (g : OneBoson) (hg : g ∈ D) (n : ℕ) :
    ⟪w n, exponentialGraph r hr g n⟫_ℂ = 0 := by
  apply exponentialCoefficient_unique (fun j => ⟪w j, exponentialGraph r hr g j⟫_ℂ)
    (exponentialGraph_inner_norm_summable r hr g w) _ n
  intro t _
  have h := hw (t • g) (D.smul_mem (t:ℂ) hg)
  rw [lp.inner_eq_tsum] at h
  convert h using 1
  apply tsum_congr
  intro j
  rw [exponentialGraph_smul_apply,inner_smul_right]
  ring


lemma exponentialGraph_orthogonal_tensor (r : ℝ) (hr : 0 ≤ r)
    (D : Submodule ℂ OneBoson) (w : Carrier)
    (hw : ∀ g ∈ D, ⟪w, exponentialGraph r hr g⟫_ℂ = 0)
    (g : OneBoson) (hg : g ∈ D) (n : ℕ) :
    ⟪w n, tensorPower n g⟫_ℂ = 0 := by
  have h := exponentialGraph_orthogonal_coefficient r hr D w hw g hg n
  rw [exponentialGraph_apply, exponentialRaw, inner_smul_right, inner_smul_right] at h
  have h₁ : (↑(((n:ℝ)+1)^r) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.rpow_pos_of_pos (by positivity : 0 < (n:ℝ)+1) r))
  have h₂ : (↑((Real.sqrt (n.factorial:ℝ))⁻¹) : ℂ) ≠ 0 := by
    exact_mod_cast (inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (by positivity : 0 < (n.factorial:ℝ)))))
  exact (mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_left h₁)).resolve_left h₂


lemma exponentialGraph_orthogonal_product (r : ℝ) (hr : 0 ≤ r)
    (D : Submodule ℂ OneBoson) (w : Carrier)
    (hw : ∀ g ∈ D, ⟪w, exponentialGraph r hr g⟫_ℂ = 0)
    (n : ℕ) (g : Fin n → D) :
    ⟪w n, coherentJetSectorTensor n (fun i => (g i : OneBoson))⟫_ℂ = 0 := by
  let L := innerSL ℂ (w n)
  have hsum : L (∑ δ : Fin n → Bool, (∏ j, exponentialSign (δ j)) •
      coherentJetSectorTensor n (fun _ => ∑ j, exponentialSign (δ j) • (g j : OneBoson))) = 0 := by
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro δ _
    rw [map_smul, coherentJetSectorTensor_diagonal]
    have hg : (∑ j, exponentialSign (δ j) • (g j : OneBoson)) ∈ D :=
      D.sum_mem (fun j _ => D.smul_mem _ (g j).property)
    change (∏ j, exponentialSign (δ j)) • ⟪w n, tensorPower n _⟫_ℂ = 0
    rw [exponentialGraph_orthogonal_tensor r hr D w hw _ hg n, smul_zero]
  rw [exponentialTensor_sign_polarization, map_smul] at hsum
  have hn : ((2:ℂ)^n * (n.factorial:ℂ)) ≠ 0 := by
    apply mul_ne_zero (pow_ne_zero _ (by norm_num))
    exact_mod_cast Nat.factorial_ne_zero n
  exact (smul_eq_zero.mp hsum).resolve_left hn

lemma exponentialVacuum_inner_zero (z : ℂ) (h : ⟪z,(1:ℂ)⟫_ℂ = 0) : z = 0 := by
  rw [RCLike.inner_apply, one_mul] at h
  exact star_eq_zero.mp h

lemma exponentialGraph_orthogonal_zero (r : ℝ) (hr : 0 ≤ r)
    (D : Submodule ℂ OneBoson) (hD : Dense (D : Set OneBoson)) (w : Carrier)
    (hw : ∀ g ∈ D, ⟪w, exponentialGraph r hr g⟫_ℂ = 0) : w = 0 := by
  apply lp.ext
  funext n
  have hn : w n = 0 := by
    cases n with
    | zero =>
      have h := exponentialGraph_orthogonal_tensor r hr D w hw 0 D.zero_mem 0
      change ⟪w 0, (1:ℂ)⟫_ℂ = 0 at h
      exact exponentialVacuum_inner_zero (w 0) h
    | succ n =>
      let L := innerSL ℂ (w (n+1))
      have hk : LinearMap.ker L.toLinearMap = ⊤ := by
        apply symmetricTensor_dense_subspace_criterion n D hD _ L.isClosed_ker
        intro g
        exact exponentialGraph_orthogonal_product r hr D w hw (n+1) g
      have hs : L (w (n+1)) = 0 := by
        exact show w (n+1) ∈ LinearMap.ker L.toLinearMap from hk ▸ Submodule.mem_top
      exact inner_self_eq_zero.mp hs
  exact hn


lemma coherentExponentialWeighted_graph_total (r : ℝ) (hr : 0 ≤ r)
    (D : Submodule ℂ OneBoson) (hD : Dense (D : Set OneBoson)) :
    Dense (Submodule.span ℂ (Set.range (fun g : D => coherentExponentialWeighted r hr g)) :
      Set (NumberWeightedDomain Sector r hr)) := by
  let V : Submodule ℂ (NumberWeightedDomain Sector r hr) := Submodule.span ℂ (Set.range (fun g : D => coherentExponentialWeighted r hr g))
  change Dense (V : Set (NumberWeightedDomain Sector r hr))
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    ← Submodule.orthogonal_eq_bot_iff, Submodule.orthogonal_closure]
  apply le_antisymm _ bot_le
  intro w hw
  rw [Submodule.mem_bot]
  have hz : (show Carrier from numberDomainIsometry Sector r hr w) = 0 := by
    apply exponentialGraph_orthogonal_zero r hr D hD
    intro g hg
    have h := (V.mem_orthogonal' w).mp hw (coherentExponentialWeighted r hr g)
      (Submodule.subset_span (Set.mem_range_self (⟨g,hg⟩ : D)))
    change ⟪numberDomainIsometry Sector r hr w,
      numberDomainIsometry Sector r hr (coherentExponentialWeighted r hr g)⟫_ℂ = 0
    rwa [LinearIsometryEquiv.inner_map_map]
  have hh := congrArg (numberDomainIsometry Sector r hr).symm hz
  rw [LinearIsometryEquiv.symm_apply_apply] at hh
  exact hh.trans (map_zero (numberDomainIsometry Sector r hr).symm)


lemma coherentJet_lipschitz_increment (m : ℕ) (r R : ℝ) (hr : 0 ≤ r) (hR : 1 ≤ R)
    (g h : OneBoson) (hg : ‖g‖ ≤ R) (hgh : ‖g+h‖ ≤ R) :
    ‖coherentJet m r hr (g+h)-coherentJet m r hr g‖ ≤ coherentJetConstant (m+1) r R*‖h‖ := by
  have he : coherentJet m r hr (g+h)-coherentJet m r hr g =
      coherentJetDomainTransport m r hr (coherentJetCarrier m r (g+h)-coherentJetCarrier m r g) := by
    ext v
    simp only [map_sub]
    rfl
  rw [he, coherentJetDomainTransport_norm]
  exact coherentJetCarrier_lipschitz_increment m r R hr hR g h hg hgh

lemma coherentExponentialWeighted_lipschitz_increment (r R : ℝ) (hr : 0 ≤ r) (hR : 1 ≤ R)
    (g h : OneBoson) (hg : ‖g‖ ≤ R) (hgh : ‖g+h‖ ≤ R) :
    ‖coherentExponentialWeighted r hr (g+h)-coherentExponentialWeighted r hr g‖ ≤
      coherentJetConstant 1 r R*‖h‖ := by
  let v : Fin 0 → OneBoson := fun i => Fin.elim0 i
  calc
    _ = ‖(coherentJet 0 r hr (g+h)-coherentJet 0 r hr g) v‖ := rfl
    _ ≤ ‖coherentJet 0 r hr (g+h)-coherentJet 0 r hr g‖ * ∏ i, ‖v i‖ :=
      (coherentJet 0 r hr (g+h)-coherentJet 0 r hr g).le_opNorm v
    _ = ‖coherentJet 0 r hr (g+h)-coherentJet 0 r hr g‖ := by simp
    _ ≤ _ := coherentJet_lipschitz_increment 0 r R hr hR g h hg hgh


lemma tensorPower_inner (n : ℕ) (f g : OneBoson) :
    ⟪tensorPower n f,tensorPower n g⟫_ℂ = ⟪f,g⟫_ℂ^n := by
  cases n with
  | zero =>
    change ⟪(1:ℂ),(1:ℂ)⟫_ℂ = _
    simp
  | succ n =>
    change ⟪rawTensor (n+1) (fun _ => f),rawTensor (n+1) (fun _ => g)⟫_ℂ = _
    rw [rawTensor_inner]
    simp

lemma exponentialRaw_inner (n : ℕ) (f g : OneBoson) :
    ⟪exponentialRaw f n,exponentialRaw g n⟫_ℂ = ⟪f,g⟫_ℂ^n/(n.factorial:ℂ) := by
  unfold exponentialRaw
  rw [inner_smul_left,inner_smul_right,tensorPower_inner]
  simp only [map_inv,Complex.conj_ofReal]
  have hc : (((Real.sqrt (n.factorial:ℝ))⁻¹ : ℝ) : ℂ) *
      (((Real.sqrt (n.factorial:ℝ))⁻¹ : ℝ) : ℂ) = (n.factorial:ℂ)⁻¹ := by
    rw [← Complex.ofReal_mul,← mul_inv,← pow_two,Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n.factorial)]
    push_cast <;> rfl
  calc
    _ = ((((Real.sqrt (n.factorial:ℝ))⁻¹ : ℝ) : ℂ)*
        (((Real.sqrt (n.factorial:ℝ))⁻¹ : ℝ) : ℂ))*⟪f,g⟫_ℂ^n := by ring
    _ = _ := by rw [hc]; ring

lemma exponentialVector_inner (f g : OneBoson) :
    ⟪exponentialVector f,exponentialVector g⟫_ℂ = Complex.exp ⟪f,g⟫_ℂ := by
  have hi : HasSum (fun n : ℕ => ⟪f,g⟫_ℂ^n/(n.factorial:ℂ))
      ⟪exponentialVector f,exponentialVector g⟫_ℂ := by
    convert lp.hasSum_inner (exponentialVector f) (exponentialVector g) using 1
    funext n
    exact (exponentialRaw_inner n f g).symm
  have he := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) ⟪f,g⟫_ℂ
  have he' : HasSum (fun n : ℕ => ⟪f,g⟫_ℂ^n/(n.factorial:ℂ)) (Complex.exp ⟪f,g⟫_ℂ) := by
    convert he using 1
    · funext n
      simp only [smul_eq_mul,div_eq_mul_inv,mul_comm]
    · exact congrFun Complex.exp_eq_exp_ℂ _
  exact hi.unique he'

lemma exponentialAmplify_comp {X E F G : Type*} [MeasurableSpace X] (μ : Measure X)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (T : F →L[ℂ] G) (S : E →L[ℂ] F) (u : Lp E 2 μ) :
    amplify μ T (amplify μ S u) = amplify μ (T.comp S) u := by
  apply Lp.ext
  filter_upwards [amplify_ae μ T (amplify μ S u),amplify_ae μ S u,
    amplify_ae μ (T.comp S) u] with x h₁ h₂ h₃
  rw [h₁,h₂,h₃]
  rfl

lemma exponentialKernel_contraction {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (F G : BosonKernel E)
    (n : ℕ) (u : KernelSector E n) :
    kernelAnnihilationRaw F n (kernelCreationRaw G n u) =
      amplify (sectorMeasure n) (F.adjoint.comp G) u := by
  change amplify (sectorMeasure n) F.adjoint
    ((kernelSplit (E := E) n) ((kernelSplit (E := E) n).symm (amplify (sectorMeasure n) G u))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact exponentialAmplify_comp _ _ _ _

lemma exponentialOrdinaryKernel_gram (f g : OneBoson) :
    (ordinaryKernel f).adjoint.comp (ordinaryKernel g) = ⟪f,g⟫_ℂ • ContinuousLinearMap.id ℂ ℂ := by
  ext c
  simp [ordinaryKernel,ContinuousLinearMap.adjoint_toSpanSingleton,inner_smul_right,mul_comm]

lemma exponentialTensor_kernel (n : ℕ) (g : OneBoson) :
    (ordinarySectorKernel n (tensorPower n g) : AmbientSector n) = rawTensor n (fun _ => g) := by
  rw [← coherentJetSectorTensor_diagonal,coherentJetTensor_kernel]
  exact symmetrizer_of_fixed n _ (diagonalTensor_fixed n g)

lemma exponentialAmplify_scalar (n : ℕ) (c : ℂ) (u : AmbientSector n) :
    amplify (sectorMeasure n) (c • ContinuousLinearMap.id ℂ ℂ) u = c • u := by
  apply Lp.ext
  filter_upwards [amplify_ae (sectorMeasure n) (c • ContinuousLinearMap.id ℂ ℂ) u,
    Lp.coeFn_smul c u] with k hk hc
  rw [hk,hc]
  rfl

lemma exponentialTensor_rawAnnihilation (n : ℕ) (f g : OneBoson) :
    kernelAnnihilationRaw (ordinaryKernel f) n (rawTensor (n+1) (fun _ => g)) =
      ⟪f,g⟫_ℂ • rawTensor n (fun _ => g) := by
  have hc : Fin.cons g (fun _ : Fin n => g) = fun _ => g := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [← hc,← creationPrepend_tensor]
  rw [← ordinaryKernelCreationRaw]
  rw [exponentialKernel_contraction,exponentialOrdinaryKernel_gram,exponentialAmplify_scalar]

lemma exponentialTensor_annihilation (n : ℕ) (f g : OneBoson) :
    sectorAnnihilation ordinarySectorKernel (ordinaryKernel f) n (tensorPower (n+1) g) =
      ((Real.sqrt (n+1:ℕ) : ℂ)*⟪f,g⟫_ℂ) • tensorPower n g := by
  apply (ordinarySectorKernel n).injective
  simp only [sectorAnnihilation,ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.apply_symm_apply,map_smul]
  apply Subtype.ext
  rw [kernelAnnihilation_value,exponentialTensor_kernel,exponentialTensor_rawAnnihilation]
  change _ = ((Real.sqrt (n+1:ℕ) : ℂ)*⟪f,g⟫_ℂ) •
    (ordinarySectorKernel n (tensorPower n g) : AmbientSector n)
  rw [exponentialTensor_kernel,smul_smul]

lemma exponentialCoefficient_step (n : ℕ) :
    (Real.sqrt ((n+1).factorial:ℝ))⁻¹*Real.sqrt (n+1:ℕ) = (Real.sqrt (n.factorial:ℝ))⁻¹ := by
  rw [Nat.factorial_succ,Nat.cast_mul,Real.sqrt_mul (Nat.cast_nonneg (α := ℝ) (n+1))]
  have hn : Real.sqrt (n+1:ℕ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  field_simp

lemma exponentialRaw_annihilation (n : ℕ) (f g : OneBoson) :
    sectorAnnihilation ordinarySectorKernel (ordinaryKernel f) n (exponentialRaw g (n+1)) =
      ⟪f,g⟫_ℂ • exponentialRaw g n := by
  unfold exponentialRaw
  rw [map_smul,exponentialTensor_annihilation,smul_smul,smul_smul]
  have hc := congrArg (fun a : ℝ => (a:ℂ)) (exponentialCoefficient_step n)
  rw [Complex.ofReal_mul] at hc
  congr 1
  calc
    _ = ((((Real.sqrt ((n+1).factorial:ℝ))⁻¹:ℝ):ℂ)*(Real.sqrt (n+1:ℕ):ℂ))*⟪f,g⟫_ℂ := by ring
    _ = _ := by rw [hc]; ring

lemma exponentialVector_annihilation (f g : OneBoson) :
    ordinaryAnnihilation f (ordinaryAnnihilationAllInput f (coherentExponentialAll g)) =
      ⟪f,g⟫_ℂ • exponentialVector g := by
  apply lp.ext
  funext n
  rw [ordinaryAnnihilation_apply]
  change sectorAnnihilation ordinarySectorKernel (ordinaryKernel f) n (exponentialRaw g (n+1)) =
    ⟪f,g⟫_ℂ • exponentialRaw g n
  exact exponentialRaw_annihilation n f g


lemma exponentialCoefficient_number (n : ℕ) :
    coherentJetCoefficient (n+1) 1 = (n+1:ℕ)*(Real.sqrt ((n+1).factorial:ℝ))⁻¹ := by
  unfold coherentJetCoefficient
  rw [Nat.succ_sub_succ_eq_sub,Nat.sub_zero]
  have hf : (n.factorial:ℝ) ≠ 0 := by positivity
  have hs : Real.sqrt ((n+1).factorial:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hfac : ((n+1).factorial:ℝ) = (n+1:ℕ)*(n.factorial:ℝ) := by rw [Nat.factorial_succ,Nat.cast_mul]
  have he := (Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (n+1).factorial)).trans hfac
  field_simp
  nlinarith

def exponentialNumberInput (g : OneBoson) : (numberPower Sector 1).domain :=
  ⟨exponentialVector g,(coherentCreatorProduct_preserves g 0 (fun i => Fin.elim0 i) 1 zero_le_one)⟩

lemma exponentialVector_number (g : OneBoson) :
    numberPower Sector 1 (exponentialNumberInput g) =
      ordinaryCreation g (ordinaryCreationAllInput g (coherentExponentialAll g)) := by
  change numberPower Sector 1 (exponentialNumberInput g) = (coherentCreatorProduct g 1 (fun _ => g)).val
  apply lp.ext
  funext n
  rw [numberPower_apply Sector 1 one_ne_zero,Real.rpow_one]
  change ((n:ℝ):ℂ) • exponentialRaw g n = (coherentCreatorProduct g 1 (fun _ => g)).val n
  cases n with
  | zero =>
    rw [Nat.cast_zero,Complex.ofReal_zero,zero_smul,coherentCreatorProduct_coordinate_below g 1 _ 0 (by norm_num)]
  | succ n =>
    rw [coherentCreatorProduct_coordinate g 1 _ (n+1) (by omega)]
    have hf : coherentJetFactors (n+1) 1 (fun _ => g) g = fun _ => g := by
      funext i
      simp [coherentJetFactors]
    rw [hf,coherentJetSectorTensor_diagonal,exponentialRaw,smul_smul,exponentialCoefficient_number]
    congr 1
    exact (Complex.ofReal_mul _ _).symm



lemma exponentialGraph_zero (g : OneBoson) : exponentialGraph 0 (by norm_num) g = exponentialVector g := by
  apply lp.ext
  funext n
  rw [exponentialGraph_apply]
  simp only [Real.rpow_zero, Complex.ofReal_one, one_smul]
  rfl

lemma exponentialSpan_dense (D : Submodule ℂ OneBoson) (hD : Dense (D : Set OneBoson)) :
    Dense (exponentialSpan D : Set Carrier) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    ← Submodule.orthogonal_eq_bot_iff, Submodule.orthogonal_closure]
  apply le_antisymm _ bot_le
  intro w hw
  rw [Submodule.mem_bot]
  apply exponentialGraph_orthogonal_zero 0 (by norm_num) D hD
  intro g hg
  rw [exponentialGraph_zero]
  exact ((exponentialSpan D).mem_orthogonal' w).mp hw (exponentialVector g)
    (Submodule.subset_span ⟨g,hg,rfl⟩)

end GW.Fock
