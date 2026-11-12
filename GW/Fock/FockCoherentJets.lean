module
public import GW.Fock.FockExponential
public import GW.Fock.FockWeightedFields
public import GW.Analysis.BridgeUniformDerivatives
public import GW.Analysis.BridgeSymmetrizer
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import GW.Fock.CreationSymmetrization
public import Mathlib.Analysis.Calculus.ContDiff.Basic
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace BigOperators ENNReal
namespace GW.Fock

def coherentJetMajorant (n m : ℕ) (r R : ℝ) : ℝ :=
  (n+1:ℝ)^(2*r) * (n.factorial:ℝ) / ((n-m).factorial:ℝ)^2 * R^(2*(n-m))

def coherentJetThreshold (m : ℕ) (r R : ℝ) : ℕ :=
  max (max m (2*m)) ⌈(2:ℝ)^(2*r+3)*R^2⌉₊

def coherentJetConstant (m : ℕ) (r R : ℝ) : ℝ :=
  Real.sqrt ((∑ n ∈ Finset.Ico m (coherentJetThreshold m r R), coherentJetMajorant n m r R) +
    2*coherentJetMajorant (coherentJetThreshold m r R) m r R)

lemma coherentJetMajorant_pos (n m : ℕ) (r R : ℝ) (hR : 1 ≤ R) :
    0 < coherentJetMajorant n m r R := by
  unfold coherentJetMajorant
  positivity

lemma coherentJetThreshold_ge_m (m : ℕ) (r R : ℝ) : m ≤ coherentJetThreshold m r R :=
  (le_max_left m (2*m)).trans (le_max_left _ _)

lemma coherentJetThreshold_ge_twice (m : ℕ) (r R : ℝ) : 2*m ≤ coherentJetThreshold m r R :=
  (le_max_right m (2*m)).trans (le_max_left _ _)

lemma coherentJetThreshold_ge_real (m : ℕ) (r R : ℝ) :
    (2:ℝ)^(2*r+3)*R^2 ≤ (coherentJetThreshold m r R:ℝ) :=
  (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))

lemma coherentJetMajorant_ratio (n m : ℕ) (r R : ℝ) (hn : m ≤ n) :
    coherentJetMajorant (n+1) m r R = coherentJetMajorant n m r R *
      (((n+2:ℝ)/(n+1:ℝ))^(2*r) * (n+1:ℝ)/(n+1-m:ℝ)^2 * R^2) := by
  have hi : n+1-m = (n-m)+1 := by omega
  have he : 2*(n+1-m) = 2*(n-m)+2 := by omega
  have hf : (n.factorial:ℝ) ≠ 0 := by positivity
  have hg : ((n-m).factorial:ℝ) ≠ 0 := by positivity
  have hnr : (m:ℝ) ≤ n := by exact_mod_cast hn
  have hp : (n+1-m:ℝ) ≠ 0 := ne_of_gt (by nlinarith)
  have hc : ((n-m:ℕ):ℝ) = (n:ℝ)-m := Nat.cast_sub hn
  unfold coherentJetMajorant
  rw [he,hi,Nat.factorial_succ,Nat.factorial_succ,pow_add,
    Real.div_rpow (by positivity : (0:ℝ) ≤ n+2) (by positivity : (0:ℝ) ≤ n+1)]
  push_cast
  rw [hc]
  have hn1 : (n+1:ℝ)^(2*r) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)
  rw [show (n:ℝ)-m+1 = n+1-m by ring]
  field_simp [hf,hg,hp,hn1]
  <;> ring

lemma coherentJetRatio_le_half (n m : ℕ) (r R : ℝ) (hr : 0 ≤ r)
    (hn : coherentJetThreshold m r R ≤ n) :
    ((n+2:ℝ)/(n+1:ℝ))^(2*r) * (n+1:ℝ)/(n+1-m:ℝ)^2 * R^2 ≤ 1/2 := by
  have hm : 2*m ≤ n := (coherentJetThreshold_ge_twice m r R).trans hn
  have hmr : (2:ℝ)*m ≤ n := by exact_mod_cast hm
  have hpos : (0:ℝ) < n+1 := by positivity
  have hden : (0:ℝ) < n+1-m := by nlinarith
  have hfrac : (n+2:ℝ)/(n+1:ℝ) ≤ 2 := (div_le_iff₀ hpos).mpr (by nlinarith)
  have hp := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ (n+2:ℝ)/(n+1:ℝ)) hfrac (by positivity : 0 ≤ 2*r)
  have hd : (n+1:ℝ)/(n+1-m:ℝ)^2 ≤ 4/(n+1:ℝ) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hden) hpos).mpr
    nlinarith [sq_nonneg ((n+1:ℝ)-2*m)]
  have hthreshold : (2:ℝ)^(2*r+3)*R^2 ≤ n :=
    (coherentJetThreshold_ge_real m r R).trans (Nat.cast_le.mpr hn)
  have hpow : (2:ℝ)^(2*r+3) = 8*(2:ℝ)^(2*r) := by
    rw [Real.rpow_add (by norm_num)]
    norm_num
    ring
  rw [hpow] at hthreshold
  calc
    _ = ((n+2:ℝ)/(n+1:ℝ))^(2*r) * ((n+1:ℝ)/(n+1-m:ℝ)^2) * R^2 := by ring
    _ ≤ (2:ℝ)^(2*r) * (4/(n+1:ℝ)) * R^2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hp hd (by positivity) (Real.rpow_nonneg (by norm_num) _)) (sq_nonneg R)
    _ = ((2:ℝ)^(2*r)*4*R^2)/(n+1:ℝ) := by ring
    _ ≤ 1/2 := (div_le_iff₀ hpos).mpr (by nlinarith)

lemma coherentJetMajorant_step (n m : ℕ) (r R : ℝ) (hr : 0 ≤ r) (hR : 1 ≤ R)
    (hn : coherentJetThreshold m r R ≤ n) :
    coherentJetMajorant (n+1) m r R ≤ (1/2)*coherentJetMajorant n m r R := by
  rw [coherentJetMajorant_ratio n m r R ((coherentJetThreshold_ge_m m r R).trans hn)]
  nlinarith [mul_le_mul_of_nonneg_left (coherentJetRatio_le_half n m r R hr hn)
    (coherentJetMajorant_pos n m r R hR).le]

lemma coherentJetMajorant_tail_pointwise (m : ℕ) (r R : ℝ) (hr : 0 ≤ r) (hR : 1 ≤ R) (j : ℕ) :
    coherentJetMajorant (coherentJetThreshold m r R+j) m r R ≤
      (1/2:ℝ)^j * coherentJetMajorant (coherentJetThreshold m r R) m r R := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h := coherentJetMajorant_step (coherentJetThreshold m r R+j) m r R hr hR (by omega)
    rw [Nat.add_succ, pow_succ]
    nlinarith

lemma coherentJetMajorant_geometric_from (m L : ℕ) (r R : ℝ) (hr : 0 ≤ r) (hR : 1 ≤ R)
    (hL : coherentJetThreshold m r R ≤ L) (j : ℕ) :
    coherentJetMajorant (L+j) m r R ≤ (1/2:ℝ)^j * coherentJetMajorant L m r R := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h := coherentJetMajorant_step (L+j) m r R hr hR (by omega)
    rw [Nat.add_succ,pow_succ]
    nlinarith

lemma coherentJetMajorant_tail_summable (m L : ℕ) (r R : ℝ) (hr : 0 ≤ r) (hR : 1 ≤ R)
    (hL : coherentJetThreshold m r R ≤ L) :
    Summable (fun j => coherentJetMajorant (L+j) m r R) := by
  have hs : Summable (fun j : ℕ => (1/2:ℝ)^j * coherentJetMajorant L m r R) :=
    (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)).mul_right _
  apply Summable.of_norm_bounded hs
  intro j
  rw [Real.norm_eq_abs,abs_of_pos (coherentJetMajorant_pos _ _ _ _ hR)]
  exact coherentJetMajorant_geometric_from m L r R hr hR hL j

lemma coherentJetMajorant_summable (m : ℕ) (r R : ℝ) (hr : 0 ≤ r) (hR : 1 ≤ R) :
    Summable (fun n => coherentJetMajorant n m r R) := by
  apply (summable_nat_add_iff (coherentJetThreshold m r R)).mp
  simpa only [Nat.add_comm] using coherentJetMajorant_tail_summable m _ r R hr hR le_rfl

lemma coherentJetMajorant_tail_bound (m L : ℕ) (r R : ℝ) (hr : 0 ≤ r) (hR : 1 ≤ R)
    (hL : coherentJetThreshold m r R ≤ L) :
    (∑' j, coherentJetMajorant (L+j) m r R) ≤ 2*coherentJetMajorant L m r R := by
  have hs : Summable (fun j : ℕ => (1/2:ℝ)^j * coherentJetMajorant L m r R) :=
    (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)).mul_right _
  have h := (coherentJetMajorant_tail_summable m L r R hr hR hL).tsum_le_tsum
    (coherentJetMajorant_geometric_from m L r R hr hR hL) hs
  rw [tsum_mul_right,tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1)] at h
  norm_num at h ⊢
  exact h

lemma coherentJetMajorant_shifted_tail_bound (m j : ℕ) (r R : ℝ) (hr : 0 ≤ r) (hR : 1 ≤ R) :
    (∑' k, coherentJetMajorant (coherentJetThreshold m r R+j+k) m r R) ≤
      2*((1/2:ℝ)^j * coherentJetMajorant (coherentJetThreshold m r R) m r R) := by
  exact (coherentJetMajorant_tail_bound m _ r R hr hR (by omega)).trans
    (mul_le_mul_of_nonneg_left (coherentJetMajorant_tail_pointwise m r R hr hR j) (by norm_num))

lemma coherentJetMajorant_shifted_tail_tendsto (m : ℕ) (r R : ℝ) (hr : 0 ≤ r) (hR : 1 ≤ R) :
    Tendsto (fun j => ∑' k, coherentJetMajorant (coherentJetThreshold m r R+j+k) m r R) atTop (𝓝 0) := by
  have ht : Tendsto (fun j : ℕ => 2*((1/2:ℝ)^j * coherentJetMajorant (coherentJetThreshold m r R) m r R)) atTop (𝓝 0) := by
    simpa only [zero_mul,mul_zero] using
      ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1)).mul_const
        (coherentJetMajorant (coherentJetThreshold m r R) m r R)).const_mul 2
  exact squeeze_zero (fun j => tsum_nonneg (fun k => (coherentJetMajorant_pos _ _ _ _ hR).le))
    (fun j => coherentJetMajorant_shifted_tail_bound m j r R hr hR) ht

def coherentJetSectorTensor : (n : ℕ) → ContinuousMultilinearMap ℂ (fun _ : Fin n => OneBoson) (Sector n)
  | 0 => ContinuousMultilinearMap.constOfIsEmpty ℂ (fun _ : Fin 0 => OneBoson) (1:ℂ)
  | n+1 => symmetricTensorContinuous n

lemma coherentJetSectorTensor_norm (n : ℕ) : ‖coherentJetSectorTensor n‖ ≤ 1 := by
  cases n with
  | zero =>
    change ‖ContinuousMultilinearMap.constOfIsEmpty ℂ (fun _ : Fin 0 => OneBoson) (1:ℂ)‖ ≤ 1
    rw [ContinuousMultilinearMap.norm_constOfIsEmpty,norm_one]
  | succ n => exact symmetricTensorContinuous_norm n

def coherentJetWeightedInjection (n : ℕ) (r : ℝ) : Sector n →L[ℂ] NumberGraphCarrier Sector r :=
  (numberGraphCopy Sector r).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((((n+1:ℝ)^r):ℝ):ℂ) • lp.singleContinuousLinearMap ℂ Sector 2 n)

lemma coherentJetWeightedInjection_norm (n : ℕ) (r : ℝ) (v : Sector n) :
    ‖coherentJetWeightedInjection n r v‖ = (n+1:ℝ)^r * ‖v‖ := by
  change ‖numberGraphCopy Sector r (((((n+1:ℝ)^r):ℝ):ℂ) • lp.single 2 n v)‖ = _
  rw [LinearIsometryEquiv.norm_map,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (by positivity) _),lp.norm_single (by norm_num : (0:ℝ≥0∞) < 2)]

lemma coherentJetWeightedInjection_opNorm (n : ℕ) (r : ℝ) :
    ‖coherentJetWeightedInjection n r‖ ≤ (n+1:ℝ)^r :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.rpow_nonneg (by positivity) _) (fun v =>
    (coherentJetWeightedInjection_norm n r v).le)

def coherentJetBlockScalar (m k : ℕ) : ℝ :=
  ((m+k).factorial:ℝ) / ((k.factorial:ℝ)*Real.sqrt ((m+k).factorial:ℝ))

lemma coherentJetBlockScalar_nonneg (m k : ℕ) : 0 ≤ coherentJetBlockScalar m k := by
  unfold coherentJetBlockScalar
  positivity

/-- The varying slots are curried into the direction-map Banach space before differentiating. -/
def coherentJetBlock (m k : ℕ) (r : ℝ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin k => OneBoson)
      (ContinuousMultilinearMap ℂ (fun _ : Fin m => OneBoson) (NumberGraphCarrier Sector r)) :=
  (ContinuousMultilinearMap.currySumEquiv ℂ (Fin k) (Fin m) OneBoson (NumberGraphCarrier Sector r))
    (ContinuousMultilinearMap.domDomCongr
      ((finSumFinEquiv : Fin m ⊕ Fin k ≃ Fin (m+k)).symm.trans (Equiv.sumComm _ _))
      (((coherentJetBlockScalar m k : ℂ) • coherentJetWeightedInjection (m+k) r).compContinuousMultilinearMap
        (coherentJetSectorTensor (m+k))))

lemma coherentJetBlock_norm (m k : ℕ) (r : ℝ) :
    ‖coherentJetBlock m k r‖ ≤ (m+k+1:ℝ)^r * coherentJetBlockScalar m k := by
  unfold coherentJetBlock
  rw [LinearIsometryEquiv.norm_map,ContinuousMultilinearMap.norm_domDomCongr]
  apply le_trans (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _)
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (coherentJetBlockScalar_nonneg m k)]
  have hi := coherentJetWeightedInjection_opNorm (m+k) r
  have ht := coherentJetSectorTensor_norm (m+k)
  have hc := coherentJetBlockScalar_nonneg m k
  have hw : (0:ℝ) ≤ (m+k+1:ℝ)^r := Real.rpow_nonneg (by positivity) _
  push_cast at hi
  nlinarith [mul_le_mul_of_nonneg_left hi hc,
    mul_le_mul_of_nonneg_left ht (mul_nonneg hc (norm_nonneg (coherentJetWeightedInjection (m+k) r)))]

def coherentJetPolynomial (m k : ℕ) (r : ℝ) (g : OneBoson) :
    ContinuousMultilinearMap ℂ (fun _ : Fin m => OneBoson) (NumberGraphCarrier Sector r) :=
  coherentJetBlock m k r (fun _ => g)

def coherentJetPolynomialDerivative (m k : ℕ) (r : ℝ) (g : OneBoson) :
    OneBoson →L[ℂ] ContinuousMultilinearMap ℂ (fun _ : Fin m => OneBoson) (NumberGraphCarrier Sector r) :=
  ∑ i : Fin k, (coherentJetBlock m k r).toContinuousLinearMap (fun _ => g) i

set_option backward.isDefEq.respectTransparency.types false in
lemma coherentJetPolynomial_hasFDerivAt (m k : ℕ) (r : ℝ) (g : OneBoson) :
    HasFDerivAt (coherentJetPolynomial m k r) (coherentJetPolynomialDerivative m k r g) g := by
  unfold coherentJetPolynomial coherentJetPolynomialDerivative
  simpa only [id_eq,ContinuousLinearMap.comp_id] using
    (HasFDerivAt.multilinear_comp (coherentJetBlock m k r)
      (fun _ : Fin k => hasFDerivAt_id (𝕜 := ℂ) g))

lemma coherentJetPolynomial_norm (m k : ℕ) (r : ℝ) (g : OneBoson) :
    ‖coherentJetPolynomial m k r g‖ ≤
      ((m+k+1:ℝ)^r * coherentJetBlockScalar m k) * ‖g‖^k := by
  have h := (coherentJetBlock m k r).le_opNorm (fun _ => g)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at h
  exact h.trans (mul_le_mul_of_nonneg_right (coherentJetBlock_norm m k r) (by positivity))

def coherentJetFinite (m : ℕ) (r : ℝ) (L : ℕ) (g : OneBoson) :
    ContinuousMultilinearMap ℂ (fun _ : Fin m => OneBoson) (NumberGraphCarrier Sector r) :=
  ∑ n ∈ Finset.Icc m L, coherentJetPolynomial m (n-m) r g

lemma coherentJet_single_sum_norm_sq
    {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℂ (E n)]
    (s : Finset ℕ) (v : ∀ n, E n) :
    ‖∑ n ∈ s, lp.single 2 n (v n)‖^2 = ∑ n ∈ s, ‖v n‖^2 := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
    (lp.norm_sum_single (p := 2) (by norm_num) v s)

lemma coherentJetWeightedInjection_apply (n j : ℕ) (r : ℝ) (v : Sector n) :
    ((numberGraphCopy Sector r).symm (coherentJetWeightedInjection n r v)) j =
      lp.single 2 n (((((n+1:ℝ)^r):ℝ):ℂ) • v) j := by
  change ((numberGraphCopy Sector r).symm (numberGraphCopy Sector r (((((n+1:ℝ)^r):ℝ):ℂ) • lp.single 2 n v))) j = _
  rw [LinearIsometryEquiv.symm_apply_apply]
  change (((((n+1:ℝ)^r):ℝ):ℂ) • lp.single 2 n v) j = _
  rw [← lp.single_smul]

lemma coherentJetMajorant_sum_bound (m : ℕ) (r R : ℝ) (hr : 0 ≤ r) (hR : 1 ≤ R) :
    (∑' n, if m ≤ n then coherentJetMajorant n m r R else 0) ≤ coherentJetConstant m r R ^ 2 := by
  let M := coherentJetThreshold m r R
  let b (n : ℕ) := if m ≤ n then coherentJetMajorant n m r R else 0
  have hb : Summable b := by
    apply Summable.of_norm_bounded (coherentJetMajorant_summable m r R hr hR)
    intro n
    dsimp [b]
    split_ifs
    · exact (abs_of_pos (coherentJetMajorant_pos _ _ _ _ hR)).le
    · simpa only [abs_zero] using (coherentJetMajorant_pos n m r R hR).le
  have he := hb.sum_add_tsum_nat_add M
  have hfilter : (Finset.range M).filter (fun n => m ≤ n) = Finset.Ico m M := by
    ext n
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Ico]
    omega
  have hpref : (∑ n ∈ Finset.range M, b n) = ∑ n ∈ Finset.Ico m M, coherentJetMajorant n m r R := by
    dsimp [b]
    rw [← Finset.sum_filter,hfilter]
  have htail : (fun n => b (n+M)) = (fun n => coherentJetMajorant (M+n) m r R) := by
    funext n
    dsimp [b]
    rw [if_pos (by have := coherentJetThreshold_ge_m m r R; change m ≤ n+coherentJetThreshold m r R; omega)]
    rw [Nat.add_comm]
  rw [hpref,htail] at he
  have hbound := coherentJetMajorant_tail_bound m M r R hr hR le_rfl
  have hnon : 0 ≤ (∑ n ∈ Finset.Ico m M, coherentJetMajorant n m r R) + 2*coherentJetMajorant M m r R := by
    exact add_nonneg (Finset.sum_nonneg (fun n _ => (coherentJetMajorant_pos _ _ _ _ hR).le))
      (mul_nonneg (by norm_num) (coherentJetMajorant_pos _ _ _ _ hR).le)
  change (∑' n, b n) ≤ (Real.sqrt _)^2
  rw [Real.sq_sqrt hnon,← he]
  linarith

lemma coherentJetPolynomialDerivative_apply (m k : ℕ) (r : ℝ) (g h : OneBoson)
    (v : Fin m → OneBoson) :
    coherentJetPolynomialDerivative m k r g h v =
      ∑ i : Fin k, coherentJetBlock m k r (Function.update (fun _ => g) i h) v := by
  simp [coherentJetPolynomialDerivative,ContinuousMultilinearMap.toContinuousLinearMap]

lemma coherentJetPolynomialDerivative_zero (m : ℕ) (r : ℝ) (g : OneBoson) :
    coherentJetPolynomialDerivative m 0 r g = 0 := by
  simp [coherentJetPolynomialDerivative]

lemma coherentJetSectorTensor_permutation (n : ℕ) (f : Fin n → OneBoson) (τ : Equiv.Perm (Fin n)) :
    coherentJetSectorTensor n (fun i => f (τ.symm i)) = coherentJetSectorTensor n f := by
  cases n with
  | zero => rfl
  | succ n =>
    apply Subtype.ext
    change symmetrizer (n+1) (rawTensor (n+1) (fun i => f (τ.symm i))) =
      symmetrizer (n+1) (rawTensor (n+1) f)
    rw [← rawTensor_permutation,creationSymmetrizer_permutation_right]

lemma coherentJetBlock_apply (m k : ℕ) (r : ℝ) (z : Fin k → OneBoson) (h : Fin m → OneBoson) :
    coherentJetBlock m k r z h = (coherentJetBlockScalar m k : ℂ) •
      coherentJetWeightedInjection (m+k) r
        (coherentJetSectorTensor (m+k) (fun j => Sum.elim z h
          (((finSumFinEquiv : Fin m ⊕ Fin k ≃ Fin (m+k)).symm.trans (Equiv.sumComm _ _)) j))) := by
  rfl

lemma coherentJetConstant_nonneg (m : ℕ) (r R : ℝ) : 0 ≤ coherentJetConstant m r R := Real.sqrt_nonneg _

lemma coherentJetConstant_sq (m : ℕ) (r R : ℝ) (hR : 1 ≤ R) :
    coherentJetConstant m r R ^ 2 =
      (∑ n ∈ Finset.Ico m (coherentJetThreshold m r R), coherentJetMajorant n m r R)+
        2*coherentJetMajorant (coherentJetThreshold m r R) m r R := by
  exact Real.sq_sqrt (add_nonneg
    (Finset.sum_nonneg (fun n _ => (coherentJetMajorant_pos _ _ _ _ hR).le))
    (mul_nonneg (by norm_num) (coherentJetMajorant_pos _ _ _ _ hR).le))

lemma coherentJetPolynomial_continuous (m k : ℕ) (r : ℝ) : Continuous (coherentJetPolynomial m k r) :=
  (coherentJetBlock m k r).cont.comp (continuous_pi (fun _ => continuous_id))

lemma coherentJetBlockScalar_sq (m k : ℕ) :
    coherentJetBlockScalar m k ^ 2 = ((m+k).factorial:ℝ)/(k.factorial:ℝ)^2 := by
  unfold coherentJetBlockScalar
  rw [div_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
  have hf : ((m+k).factorial:ℝ) ≠ 0 := by positivity
  have hg : (k.factorial:ℝ) ≠ 0 := by positivity
  field_simp [hf,hg]
  <;> ring

lemma coherentJetBlock_majorant_sq (m k : ℕ) (r R : ℝ) :
    (((m+k+1:ℝ)^r * coherentJetBlockScalar m k)*R^k)^2 =
      coherentJetMajorant (m+k) m r R := by
  have hw : ((m+k+1:ℝ)^r)^2 = (m+k+1:ℝ)^(2*r) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity : (0:ℝ) ≤ m+k+1)]
    congr 1
    ring
  have hp : (R^k)^2 = R^(2*k) := by rw [← pow_mul,Nat.mul_comm k 2]
  rw [mul_pow,mul_pow,hw,coherentJetBlockScalar_sq,hp]
  simp only [coherentJetMajorant,Nat.add_sub_cancel_left,Nat.cast_add,Nat.cast_one]
  ring

lemma coherentJet_shifted_single_sum_norm_sq
    {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℂ (E n)]
    (m : ℕ) (s : Finset ℕ) (v : ∀ k, E (m+k)) :
    ‖∑ k ∈ s, lp.single 2 (m+k) (v k)‖^2 = ∑ k ∈ s, ‖v k‖^2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  simp only [sum_inner,inner_sum,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · rw [lp.inner_single_left,lp.single_apply_self,← norm_sq_eq_re_inner (𝕜 := ℂ)]
  · intro j hj hji
    rw [lp.inner_single_left,lp.single_apply_ne _ _ _ (by omega : m+j ≠ m+i)]
    simp only [inner_zero_right,map_zero]
  · exact fun h => (h hi).elim

lemma coherentJetWeightedInjection_copy (n : ℕ) (r : ℝ) (v : Sector n) :
    (numberGraphCopy Sector r).symm (coherentJetWeightedInjection n r v) =
      lp.single 2 n (((((n+1:ℝ)^r):ℝ):ℂ) • v) := by
  change (numberGraphCopy Sector r).symm
    (numberGraphCopy Sector r (((((n+1:ℝ)^r):ℝ):ℂ) • lp.single 2 n v)) = _
  rw [LinearIsometryEquiv.symm_apply_apply,← lp.single_smul]


lemma coherentJetWeightedInjection_sum_sq (m : ℕ) (r : ℝ)
    (s : Finset ℕ) (v : ∀ k, Sector (m+k)) :
    ‖∑ k ∈ s, coherentJetWeightedInjection (m+k) r (v k)‖^2 =
      ∑ k ∈ s, ‖coherentJetWeightedInjection (m+k) r (v k)‖^2 := by
  rw [← (numberGraphCopy Sector r).symm.norm_map]
  simp only [map_sum,coherentJetWeightedInjection_copy]
  rw [coherentJet_shifted_single_sum_norm_sq]
  apply Finset.sum_congr rfl
  intro k hk
  rw [coherentJetWeightedInjection_norm,norm_smul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos (by positivity) _)]

lemma coherentJetPolynomial_sum_sq (m : ℕ) (r : ℝ) (s : Finset ℕ)
    (g : OneBoson) (h : Fin m → OneBoson) :
    ‖∑ k ∈ s, coherentJetPolynomial m k r g h‖^2 =
      ∑ k ∈ s, ‖coherentJetPolynomial m k r g h‖^2 := by
  have he (k : ℕ) : coherentJetPolynomial m k r g h =
      coherentJetWeightedInjection (m+k) r
        ((coherentJetBlockScalar m k : ℂ) • coherentJetSectorTensor (m+k)
          (fun j => Sum.elim (fun _ : Fin k => g) h
            (((finSumFinEquiv : Fin m ⊕ Fin k ≃ Fin (m+k)).symm.trans (Equiv.sumComm _ _)) j))) := by
    rw [coherentJetPolynomial,coherentJetBlock_apply,map_smul]
  simp_rw [he]
  exact coherentJetWeightedInjection_sum_sq m r s _

lemma coherentJetPolynomial_apply_majorant (m k : ℕ) (r R : ℝ)
    (hR : 1 ≤ R) (g : OneBoson) (hg : ‖g‖ ≤ R) (h : Fin m → OneBoson) :
    ‖coherentJetPolynomial m k r g h‖^2 ≤
      coherentJetMajorant (m+k) m r R * (∏ i, ‖h i‖)^2 := by
  have hc : 0 ≤ (m+k+1:ℝ)^r * coherentJetBlockScalar m k :=
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (coherentJetBlockScalar_nonneg m k)
  have hp : 0 ≤ ∏ i, ‖h i‖ := Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  have hb : ‖coherentJetPolynomial m k r g h‖ ≤
      (((m+k+1:ℝ)^r * coherentJetBlockScalar m k)*R^k) * ∏ i, ‖h i‖ := by
    calc
      _ ≤ ‖coherentJetPolynomial m k r g‖ * ∏ i, ‖h i‖ :=
        (coherentJetPolynomial m k r g).le_opNorm h
      _ ≤ (((m+k+1:ℝ)^r * coherentJetBlockScalar m k)*‖g‖^k) * ∏ i, ‖h i‖ :=
        mul_le_mul_of_nonneg_right (coherentJetPolynomial_norm m k r g) hp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg g) hg k) hc) hp
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
  rw [mul_pow,coherentJetBlock_majorant_sq] at hs
  exact hs

lemma coherentJetPolynomial_sum_bound (m : ℕ) (r R : ℝ) (hR : 1 ≤ R)
    (s : Finset ℕ) (g : OneBoson) (hg : ‖g‖ ≤ R) :
    ‖∑ k ∈ s, coherentJetPolynomial m k r g‖ ≤
      Real.sqrt (∑ k ∈ s, coherentJetMajorant (m+k) m r R) := by
  apply ContinuousMultilinearMap.opNorm_le_bound (Real.sqrt_nonneg _)
  intro h
  have hp : 0 ≤ ∏ i, ‖h i‖ := Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hp)).mp
  simp only [ContinuousMultilinearMap.sum_apply]
  rw [coherentJetPolynomial_sum_sq,mul_pow,Real.sq_sqrt
    (Finset.sum_nonneg (fun k _ => (coherentJetMajorant_pos _ _ _ _ hR).le)),Finset.sum_mul]
  exact Finset.sum_le_sum (fun k _ => coherentJetPolynomial_apply_majorant m k r R hR g hg h)

/-- Squared finite-sum domination is the source's norm-completion argument. -/
lemma coherentJet_summable_of_square_bound
    {ι V : Type*} [NormedAddCommGroup V] [CompleteSpace V]
    (v : ι → V) (a : ι → ℝ) (hs : Summable a)
    (hb : ∀ s : Finset ι, ‖∑ i ∈ s, v i‖^2 ≤ ∑ i ∈ s, a i) : Summable v := by
  apply summable_iff_vanishing_norm.mpr
  intro ε hε
  obtain ⟨s,hs'⟩ := summable_iff_vanishing_norm.mp hs (ε^2) (sq_pos_of_pos hε)
  refine ⟨s,fun t ht => ?_⟩
  have ha := hs' t ht
  have he : ‖∑ i ∈ t, v i‖^2 < ε^2 :=
    (hb t).trans_lt ((le_abs_self _).trans_lt ha)
  nlinarith [norm_nonneg (∑ i ∈ t, v i)]

lemma coherentJetPolynomial_summable (m : ℕ) (r R : ℝ) (hr : 0 ≤ r) (hR : 1 ≤ R)
    (g : OneBoson) (hg : ‖g‖ ≤ R) : Summable (fun k => coherentJetPolynomial m k r g) := by
  have hs : Summable (fun k => coherentJetMajorant (m+k) m r R) := by
    simpa only [Nat.add_comm] using
      (summable_nat_add_iff m).mpr (coherentJetMajorant_summable m r R hr hR)
  apply coherentJet_summable_of_square_bound _ _ hs
  intro s
  have hb := coherentJetPolynomial_sum_bound m r R hR s g hg
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
  rwa [Real.sq_sqrt (Finset.sum_nonneg
    (fun k _ => (coherentJetMajorant_pos _ _ _ _ hR).le))] at hsq

/-- The source jet is the norm limit in the complete space of direction maps.
The isometric number-graph adapter is applied only after this completion. -/
def coherentJetCarrier (m : ℕ) (r : ℝ) (g : OneBoson) :
    ContinuousMultilinearMap ℂ (fun _ : Fin m => OneBoson) (NumberGraphCarrier Sector r) :=
  ∑' k, coherentJetPolynomial m k r g

lemma coherentJetCarrier_tendsto (m : ℕ) (r : ℝ) (hr : 0 ≤ r) (g : OneBoson) :
    Tendsto (fun L => ∑ k ∈ Finset.range L, coherentJetPolynomial m k r g)
      atTop (𝓝 (coherentJetCarrier m r g)) := by
  apply (coherentJetPolynomial_summable m r (max 1 ‖g‖) hr (le_max_left _ _) g (le_max_right _ _)).hasSum.tendsto_sum_nat

lemma coherentJetPolynomial_copy (m k : ℕ) (r : ℝ) (g : OneBoson) (h : Fin m → OneBoson) :
    (numberGraphCopy Sector r).symm (coherentJetPolynomial m k r g h) =
      lp.single 2 (m+k)
        (((((m+k+1:ℝ)^r * coherentJetBlockScalar m k):ℝ):ℂ) •
          coherentJetSectorTensor (m+k) (fun j => Sum.elim (fun _ : Fin k => g) h
            (((finSumFinEquiv : Fin m ⊕ Fin k ≃ Fin (m+k)).symm.trans (Equiv.sumComm _ _)) j))) := by
  rw [coherentJetPolynomial,coherentJetBlock_apply,map_smul,coherentJetWeightedInjection_copy,
    ← lp.single_smul,smul_smul]
  congr 2
  push_cast
  ring

lemma coherentJetCarrier_coordinate_below (m n : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (g : OneBoson) (h : Fin m → OneBoson) (hn : n < m) :
    ((numberGraphCopy Sector r).symm (coherentJetCarrier m r g h)) n = 0 := by
  have hc : Continuous (fun A : ContinuousMultilinearMap ℂ (fun _ : Fin m => OneBoson)
      (NumberGraphCarrier Sector r) => ((numberGraphCopy Sector r).symm (A h)) n) := by
    exact (lp.evalCLM ℂ Sector 2 n).continuous.comp
      ((numberGraphCopy Sector r).symm.continuous.comp (continuous_eval_const h))
  have ht := hc.continuousAt.tendsto.comp (coherentJetCarrier_tendsto m r hr g)
  have hz : (fun L => ((numberGraphCopy Sector r).symm
      ((∑ k ∈ Finset.range L, coherentJetPolynomial m k r g) h)) n) = fun _ => (0 : Sector n) := by
    funext L
    simp only [ContinuousMultilinearMap.sum_apply,map_sum,coherentJetPolynomial_copy,
      lp.coeFn_sum,Finset.sum_apply]
    exact Finset.sum_eq_zero (fun k _ => lp.single_apply_ne _ _ _ (by omega))
  simp only [Function.comp_def] at ht
  rw [hz] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

lemma coherentJetCarrier_coordinate (m k : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (g : OneBoson) (h : Fin m → OneBoson) :
    ((numberGraphCopy Sector r).symm (coherentJetCarrier m r g h)) (m+k) =
      ((numberGraphCopy Sector r).symm (coherentJetPolynomial m k r g h)) (m+k) := by
  have hc : Continuous (fun A : ContinuousMultilinearMap ℂ (fun _ : Fin m => OneBoson)
      (NumberGraphCarrier Sector r) => ((numberGraphCopy Sector r).symm (A h)) (m+k)) := by
    exact (lp.evalCLM ℂ Sector 2 (m+k)).continuous.comp
      ((numberGraphCopy Sector r).symm.continuous.comp (continuous_eval_const h))
  have ht := hc.continuousAt.tendsto.comp (coherentJetCarrier_tendsto m r hr g)
  have he : (fun L => ((numberGraphCopy Sector r).symm
      ((∑ j ∈ Finset.range L, coherentJetPolynomial m j r g) h)) (m+k)) =ᶠ[atTop]
      (fun _ => ((numberGraphCopy Sector r).symm (coherentJetPolynomial m k r g h)) (m+k)) := by
    filter_upwards [eventually_ge_atTop (k+1)] with L hL
    simp only [ContinuousMultilinearMap.sum_apply,map_sum,coherentJetPolynomial_copy,
      lp.coeFn_sum,Finset.sum_apply]
    apply Finset.sum_eq_single k
    · intro j hj hjk
      exact lp.single_apply_ne _ _ _ (by omega)
    · intro hk
      exact (hk (Finset.mem_range.mpr (by omega))).elim
  exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' he.symm)

lemma coherentJetMajorant_shifted_sum_bound (m : ℕ) (r R : ℝ)
    (hr : 0 ≤ r) (hR : 1 ≤ R) :
    (∑' k, coherentJetMajorant (m+k) m r R) ≤ coherentJetConstant m r R ^ 2 := by
  let b (n : ℕ) := if m ≤ n then coherentJetMajorant n m r R else 0
  have hs : Summable b := by
    apply Summable.of_norm_bounded (coherentJetMajorant_summable m r R hr hR)
    intro n
    dsimp only [b]
    split_ifs
    · exact (abs_of_pos (coherentJetMajorant_pos _ _ _ _ hR)).le
    · simpa only [norm_zero] using (coherentJetMajorant_pos n m r R hR).le
  have he := hs.sum_add_tsum_nat_add m
  have hp : (∑ n ∈ Finset.range m, b n) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp only [b,if_neg (by have := Finset.mem_range.mp hn; omega : ¬m ≤ n)]
  have ht : (fun k => b (k+m)) = fun k => coherentJetMajorant (m+k) m r R := by
    funext k
    simp [b,Nat.add_comm]
  rw [hp,zero_add,ht] at he
  rw [he]
  exact coherentJetMajorant_sum_bound m r R hr hR

lemma coherentJetCarrier_norm (m : ℕ) (r R : ℝ) (hr : 0 ≤ r) (hR : 1 ≤ R)
    (g : OneBoson) (hg : ‖g‖ ≤ R) :
    ‖coherentJetCarrier m r g‖ ≤ coherentJetConstant m r R := by
  have hs : Summable (fun k => coherentJetMajorant (m+k) m r R) := by
    simpa only [Nat.add_comm] using
      (summable_nat_add_iff m).mpr (coherentJetMajorant_summable m r R hr hR)
  have hb (L : ℕ) : ‖∑ k ∈ Finset.range L, coherentJetPolynomial m k r g‖ ≤
      coherentJetConstant m r R := by
    have hsum : (∑ k ∈ Finset.range L, coherentJetMajorant (m+k) m r R) ≤
        coherentJetConstant m r R ^ 2 :=
      (hs.sum_le_tsum (Finset.range L) (fun k _ => (coherentJetMajorant_pos _ _ _ _ hR).le)).trans
        (coherentJetMajorant_shifted_sum_bound m r R hr hR)
    apply (coherentJetPolynomial_sum_bound m r R hR (Finset.range L) g hg).trans
    exact (Real.sqrt_le_iff).mpr ⟨coherentJetConstant_nonneg m r R,hsum⟩
  exact le_of_tendsto (coherentJetCarrier_tendsto m r hr g).norm (Eventually.of_forall hb)

def coherentJet (m : ℕ) (r : ℝ) (hr : 0 ≤ r) (g : OneBoson) :
    ContinuousMultilinearMap ℂ (fun _ : Fin m => OneBoson) (NumberWeightedDomain Sector r hr) :=
  (numberDomainIsometry Sector r hr).symm.toContinuousLinearEquiv.toContinuousLinearMap.compContinuousMultilinearMap
    (coherentJetCarrier m r g)

lemma coherentJet_carrier (m : ℕ) (r : ℝ) (hr : 0 ≤ r) (g : OneBoson) (h : Fin m → OneBoson) :
    numberDomainIsometry Sector r hr (coherentJet m r hr g h) = coherentJetCarrier m r g h :=
  (numberDomainIsometry Sector r hr).apply_symm_apply _

lemma coherentJet_value_norm (m : ℕ) (r : ℝ) (hr : 0 ≤ r) (g : OneBoson) (h : Fin m → OneBoson) :
    ‖coherentJet m r hr g h‖ = ‖coherentJetCarrier m r g h‖ :=
  (numberDomainIsometry Sector r hr).symm.norm_map _

lemma coherentJet_norm (m : ℕ) (r R : ℝ) (hr : 0 ≤ r) (hR : 1 ≤ R)
    (g : OneBoson) (hg : ‖g‖ ≤ R) :
    ‖coherentJet m r hr g‖ ≤ coherentJetConstant m r R := by
  apply ContinuousMultilinearMap.opNorm_le_bound (coherentJetConstant_nonneg m r R)
  intro h
  rw [coherentJet_value_norm]
  exact ((coherentJetCarrier m r g).le_opNorm h).trans
    (mul_le_mul_of_nonneg_right (coherentJetCarrier_norm m r R hr hR g hg)
      (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))

set_option backward.isDefEq.respectTransparency.types false in
lemma coherentJet_ambient (m : ℕ) (r : ℝ) (hr : 0 ≤ r) (g : OneBoson) (h : Fin m → OneBoson) :
    (numberWeightedGraph Sector r hr).domain.subtype
      (show (numberWeightedGraph Sector r hr).domain from coherentJet m r hr g h) =
    (numberWeightedGraph Sector r hr).embedding (coherentJetCarrier m r g h) := by
  have he := (numberWeightedGraph Sector r hr).embedding_product
    (show (numberWeightedGraph Sector r hr).domain from coherentJet m r hr g h)
  have hp : (numberWeightedGraph Sector r hr).product
      (show (numberWeightedGraph Sector r hr).domain from coherentJet m r hr g h) =
      coherentJetCarrier m r g h := coherentJet_carrier m r hr g h
  rw [hp] at he
  exact he.symm

set_option backward.isDefEq.respectTransparency.types false in
lemma coherentJet_coordinate (m k : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (g : OneBoson) (h : Fin m → OneBoson) :
    ((numberWeightedGraph Sector r hr).domain.subtype
      (show (numberWeightedGraph Sector r hr).domain from coherentJet m r hr g h)) (m+k) =
    (coherentJetBlockScalar m k : ℂ) • coherentJetSectorTensor (m+k)
      (fun j => Sum.elim (fun _ : Fin k => g) h
        (((finSumFinEquiv : Fin m ⊕ Fin k ≃ Fin (m+k)).symm.trans (Equiv.sumComm _ _)) j)) := by
  rw [coherentJet_ambient,numberGraphEmbedding_apply]
  change (((((m+k:ℕ):ℝ)+1)^(-r):ℝ):ℂ) •
      (((numberGraphCopy Sector r).symm (coherentJetCarrier m r g h)) (m+k)) = _
  rw [coherentJetCarrier_coordinate m k r hr g h,coherentJetPolynomial_copy,lp.single_apply_self,smul_smul]
  congr 1
  push_cast
  rw [Real.rpow_neg (by positivity)]
  have hw : (m+k+1:ℝ)^r ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)
  push_cast
  norm_cast
  field_simp

set_option backward.isDefEq.respectTransparency.types false in
lemma coherentJet_coordinate_below (m n : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (g : OneBoson) (h : Fin m → OneBoson) (hn : n < m) :
    ((numberWeightedGraph Sector r hr).domain.subtype
      (show (numberWeightedGraph Sector r hr).domain from coherentJet m r hr g h)) n = 0 := by
  rw [coherentJet_ambient,numberGraphEmbedding_apply]
  change (((((n:ℝ)+1)^(-r)):ℝ):ℂ) •
      (((numberGraphCopy Sector r).symm (coherentJetCarrier m r g h)) n) = 0
  rw [coherentJetCarrier_coordinate_below m n r hr g h hn,smul_zero]

lemma coherentJetSectorTensor_diagonal (n : ℕ) (g : OneBoson) :
    coherentJetSectorTensor n (fun _ => g) = tensorPower n g := by
  cases n with
  | zero => rfl
  | succ n =>
    apply Subtype.ext
    exact symmetrizer_of_fixed (n+1) _ (diagonalTensor_fixed (n+1) g)

lemma coherentJetBlockScalar_zero (n : ℕ) :
    coherentJetBlockScalar 0 n = (Real.sqrt (n.factorial:ℝ))⁻¹ := by
  unfold coherentJetBlockScalar
  simp only [Nat.zero_add]
  have hf : (n.factorial:ℝ) ≠ 0 := by positivity
  have hs : Real.sqrt (n.factorial:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  field_simp

set_option backward.isDefEq.respectTransparency.types false in
lemma coherentJet_zero_ambient (r : ℝ) (hr : 0 ≤ r) (g : OneBoson) (h : Fin 0 → OneBoson) :
    (numberWeightedGraph Sector r hr).domain.subtype
      (show (numberWeightedGraph Sector r hr).domain from coherentJet 0 r hr g h) = exponentialVector g := by
  apply lp.ext
  funext n
  have hk := coherentJet_coordinate 0 n r hr g h
  have hc : ∀ a : Fin n ⊕ Fin 0, Sum.elim (fun _ : Fin n => g) h a = g := by
    rintro (i|i)
    · rfl
    · exact Fin.elim0 i
  simp only [zero_add] at hk
  simp_rw [hc] at hk
  rw [coherentJetSectorTensor_diagonal,coherentJetBlockScalar_zero] at hk
  rw [exponentialVector_apply]
  unfold exponentialRaw
  exact Eq.mp (congrArg (fun i : ℕ =>
    ((numberWeightedGraph Sector r hr).domain.subtype (coherentJet 0 r hr g h)) i =
      (((Real.sqrt (n.factorial:ℝ))⁻¹ : ℝ) : ℂ) • tensorPower i g) (Nat.zero_add n)) hk



set_option backward.isDefEq.respectTransparency.types false in
lemma coherentJet_exponential_weighted (r : ℝ) (hr : 0 ≤ r) (g : OneBoson) :
    exponentialVector g ∈ (shiftedNumberPower Sector r).domain := by
  rw [← coherentJet_zero_ambient r hr g (fun i => Fin.elim0 i)]
  exact (show (numberWeightedGraph Sector r hr).domain from
    coherentJet 0 r hr g (fun i => Fin.elim0 i)).property

lemma coherentJetPolynomial_symmetric (m k : ℕ) (r : ℝ) (g : OneBoson)
    (τ : Equiv.Perm (Fin m)) (h : Fin m → OneBoson) :
    coherentJetPolynomial m k r g (fun i => h (τ i)) = coherentJetPolynomial m k r g h := by
  let e : Fin (m+k) ≃ Fin k ⊕ Fin m :=
    (finSumFinEquiv : Fin m ⊕ Fin k ≃ Fin (m+k)).symm.trans (Equiv.sumComm _ _)
  let π : Equiv.Perm (Fin (m+k)) :=
    e.trans ((Equiv.sumCongr (Equiv.refl (Fin k)) τ).trans e.symm)
  let f : Fin (m+k) → OneBoson := fun j => Sum.elim (fun _ : Fin k => g) h (e j)
  have hf : (fun j => f (π j)) = fun j => Sum.elim (fun _ : Fin k => g) (fun i => h (τ i)) (e j) := by
    funext j
    dsimp only [f,π,Equiv.trans_apply]
    rw [Equiv.apply_symm_apply]
    cases e j <;> rfl
  have ht := coherentJetSectorTensor_permutation (m+k) f π.symm
  simp only [Equiv.symm_symm] at ht
  rw [hf] at ht
  simp only [coherentJetPolynomial,coherentJetBlock_apply]
  exact congrArg (fun v : Sector (m+k) =>
    (coherentJetBlockScalar m k : ℂ) • coherentJetWeightedInjection (m+k) r v) ht

lemma coherentJetCarrier_symmetric (m : ℕ) (r : ℝ) (hr : 0 ≤ r) (g : OneBoson)
    (τ : Equiv.Perm (Fin m)) (h : Fin m → OneBoson) :
    coherentJetCarrier m r g (fun i => h (τ i)) = coherentJetCarrier m r g h := by
  have h₁ : Continuous (fun A : ContinuousMultilinearMap ℂ (fun _ : Fin m => OneBoson)
      (NumberGraphCarrier Sector r) => A (fun i => h (τ i))) := by fun_prop
  have h₂ : Continuous (fun A : ContinuousMultilinearMap ℂ (fun _ : Fin m => OneBoson)
      (NumberGraphCarrier Sector r) => A h) := by fun_prop
  have ht₁ := h₁.continuousAt.tendsto.comp (coherentJetCarrier_tendsto m r hr g)
  have ht₂ := h₂.continuousAt.tendsto.comp (coherentJetCarrier_tendsto m r hr g)
  have he : (fun L => (∑ k ∈ Finset.range L, coherentJetPolynomial m k r g) (fun i => h (τ i))) =
      (fun L => (∑ k ∈ Finset.range L, coherentJetPolynomial m k r g) h) := by
    funext L
    simp only [ContinuousMultilinearMap.sum_apply,coherentJetPolynomial_symmetric]
  simp only [Function.comp_def] at ht₁ ht₂
  rw [he] at ht₁
  exact tendsto_nhds_unique ht₁ ht₂

lemma coherentJet_symmetric (m : ℕ) (r : ℝ) (hr : 0 ≤ r) (g : OneBoson)
    (τ : Equiv.Perm (Fin m)) (h : Fin m → OneBoson) :
    coherentJet m r hr g (fun i => h (τ i)) = coherentJet m r hr g h := by
  apply (numberDomainIsometry Sector r hr).injective
  rw [coherentJet_carrier,coherentJet_carrier,coherentJetCarrier_symmetric m r hr]

lemma coherentJet_tsum_sq_bound
    {ι V : Type*} [NormedAddCommGroup V] [CompleteSpace V]
    (v : ι → V) (a : ι → ℝ) (hv : Summable v) (ha : Summable a) (hpos : ∀ i, 0 ≤ a i)
    (hb : ∀ s : Finset ι, ‖∑ i ∈ s, v i‖^2 ≤ ∑ i ∈ s, a i) :
    ‖∑' i, v i‖^2 ≤ ∑' i, a i := by
  have ht : Tendsto (fun s : Finset ι => ∑ i ∈ s, v i) atTop (𝓝 (∑' i, v i)) := hv.hasSum
  apply le_of_tendsto (ht.norm.pow 2)
  exact Eventually.of_forall (fun s => (hb s).trans (ha.sum_le_tsum s (fun i _ => hpos i)))

lemma coherentJetCarrier_tail_sq (m L : ℕ) (r R : ℝ) (hr : 0 ≤ r) (hR : 1 ≤ R)
    (g : OneBoson) (hg : ‖g‖ ≤ R) :
    ‖coherentJetCarrier m r g-∑ k ∈ Finset.range L, coherentJetPolynomial m k r g‖^2 ≤
      ∑' k, coherentJetMajorant (m+(k+L)) m r R := by
  have hp := coherentJetPolynomial_summable m r R hr hR g hg
  have ha := coherentJetMajorant_summable m r R hr hR
  have hpT := (summable_nat_add_iff L).mpr hp
  have haT : Summable (fun k => coherentJetMajorant (m+(k+L)) m r R) := by
    simpa only [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using
      (summable_nat_add_iff (m+L)).mpr ha
  have hb (s : Finset ℕ) : ‖∑ k ∈ s, coherentJetPolynomial m (k+L) r g‖^2 ≤
      ∑ k ∈ s, coherentJetMajorant (m+(k+L)) m r R := by
    have hinj : Set.InjOn (fun k : ℕ => k+L) (s : Set ℕ) := fun i _ j _ h => Nat.add_right_cancel h
    have h := pow_le_pow_left₀ (norm_nonneg _)
      (coherentJetPolynomial_sum_bound m r R hR (s.image (fun k => k+L)) g hg) 2
    rw [Real.sq_sqrt (Finset.sum_nonneg
      (fun k _ => (coherentJetMajorant_pos _ _ _ _ hR).le))] at h
    simpa only [Finset.sum_image hinj] using h
  have ht := coherentJet_tsum_sq_bound _ _ hpT haT
    (fun k => (coherentJetMajorant_pos _ _ _ _ hR).le) hb
  have he := hp.sum_add_tsum_nat_add L
  have he' : coherentJetCarrier m r g-∑ k ∈ Finset.range L, coherentJetPolynomial m k r g =
      ∑' k, coherentJetPolynomial m (k+L) r g := by
    unfold coherentJetCarrier
    rw [← he]
    abel
  rw [he']
  exact ht

lemma coherentJetCarrier_uniform (m : ℕ) (r R : ℝ) (hr : 0 ≤ r) (hR : 1 ≤ R) :
    TendstoUniformlyOn (fun L g => ∑ k ∈ Finset.range L, coherentJetPolynomial m k r g)
      (coherentJetCarrier m r) atTop (Metric.closedBall (0 : OneBoson) R) := by
  have ht : Tendsto (fun L : ℕ => Real.sqrt (∑' k, coherentJetMajorant (m+(k+L)) m r R))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [Real.sqrt_zero,Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp
      (tendsto_sum_nat_add (fun k => coherentJetMajorant (m+k) m r R))
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with L hL
  intro g hg
  have hg' : ‖g‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hg
  rw [dist_eq_norm]
  apply lt_of_le_of_lt _ hL
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (tsum_nonneg (fun k => (coherentJetMajorant_pos _ _ _ _ hR).le))]
  exact coherentJetCarrier_tail_sq m L r R hr hR g hg'

lemma coherentJetCarrier_continuous (m : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    Continuous (coherentJetCarrier m r) := by
  apply continuous_iff_continuousAt.mpr
  intro g
  let R : ℝ := 1+‖g‖
  have hR : 1 ≤ R := by dsimp [R]; linarith [norm_nonneg g]
  have hc : ContinuousOn (coherentJetCarrier m r) (Metric.closedBall (0 : OneBoson) R) :=
    (coherentJetCarrier_uniform m r R hr hR).continuousOn
      (Eventually.frequently (Eventually.of_forall (fun L =>
        (continuous_finsetSum _ (fun k _ => coherentJetPolynomial_continuous m k r)).continuousOn)))
  apply hc.continuousAt
  apply Metric.closedBall_mem_nhds_of_mem
  change dist g 0 < R
  rw [dist_zero_right]
  dsimp [R]
  linarith

/-- The fixed bounded currying map used in the source integral identity. -/
def coherentJetCurry (m : ℕ) (r : ℝ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin (m+1) => OneBoson) (NumberGraphCarrier Sector r) →L[ℂ]
      (OneBoson →L[ℂ] ContinuousMultilinearMap ℂ (fun _ : Fin m => OneBoson) (NumberGraphCarrier Sector r)) :=
  (continuousMultilinearCurryLeftEquiv ℂ (fun _ : Fin (m+1) => OneBoson)
    (NumberGraphCarrier Sector r)).toContinuousLinearEquiv.toContinuousLinearMap

lemma coherentJetCurry_apply (m : ℕ) (r : ℝ)
    (B : ContinuousMultilinearMap ℂ (fun _ : Fin (m+1) => OneBoson) (NumberGraphCarrier Sector r))
    (h : OneBoson) (v : Fin m → OneBoson) :
    coherentJetCurry m r B h v = B (Fin.cons h v) := rfl

lemma coherentJetCurry_norm (m : ℕ) (r : ℝ)
    (B : ContinuousMultilinearMap ℂ (fun _ : Fin (m+1) => OneBoson) (NumberGraphCarrier Sector r)) :
    ‖coherentJetCurry m r B‖ = ‖B‖ :=
  (continuousMultilinearCurryLeftEquiv ℂ (fun _ : Fin (m+1) => OneBoson)
    (NumberGraphCarrier Sector r)).norm_map B

lemma coherentJetCurry_bound (m : ℕ) (r : ℝ)
    (B : ContinuousMultilinearMap ℂ (fun _ : Fin (m+1) => OneBoson) (NumberGraphCarrier Sector r))
    (h : OneBoson) : ‖coherentJetCurry m r B h‖ ≤ ‖B‖*‖h‖ := by
  simpa only [coherentJetCurry_norm] using (coherentJetCurry m r B).le_opNorm h

lemma coherentJetCarrier_derivative_continuous (m : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    Continuous (fun g => coherentJetCurry m r (coherentJetCarrier (m+1) r g)) :=
  (coherentJetCurry m r).continuous.comp (coherentJetCarrier_continuous (m+1) r hr)

/-- The source already-proved number estimates supply every input domain for
successive creators; the original maximal operators are used at each step. -/
def coherentExponentialAll (g : OneBoson) : EveryOrdinaryNumberVector :=
  ⟨exponentialVector g,fun r hr => coherentJet_exponential_weighted r hr g⟩

def coherentCreatorProduct (g : OneBoson) : (m : ℕ) → (Fin m → OneBoson) → EveryOrdinaryNumberVector
  | 0,_ => coherentExponentialAll g
  | m+1,h => ordinaryCreationAll (h 0) (coherentCreatorProduct g m (Fin.tail h))

lemma coherentCreatorProduct_zero (g : OneBoson) (h : Fin 0 → OneBoson) :
    (coherentCreatorProduct g 0 h).val = exponentialVector g := rfl

lemma coherentCreatorProduct_succ_graph (g : OneBoson) (m : ℕ) (h : Fin (m+1) → OneBoson) :
    ((coherentCreatorProduct g m (Fin.tail h)).val,(coherentCreatorProduct g (m+1) h).val) ∈
      (ordinaryCreation (h 0)).graph :=
  (ordinaryCreation (h 0)).mem_graph (ordinaryCreationAllInput (h 0) (coherentCreatorProduct g m (Fin.tail h)))

lemma coherentCreatorProduct_preserves (g : OneBoson) (m : ℕ) (h : Fin m → OneBoson)
    (r : ℝ) (hr : 0 ≤ r) :
    (coherentCreatorProduct g m h).val ∈ (numberPower Sector r).domain :=
  (everyOrdinaryNumberDomain_iff _).mp (coherentCreatorProduct g m h).property r hr

lemma coherentCreatorProduct_coordinate_below (g : OneBoson) (m : ℕ) (h : Fin m → OneBoson)
    (n : ℕ) (hn : n < m) : (coherentCreatorProduct g m h).val n = 0 := by
  induction m generalizing n with
  | zero => omega
  | succ m ih =>
    cases n with
    | zero =>
      exact ordinaryCreation_zero (h 0)
        (ordinaryCreationAllInput (h 0) (coherentCreatorProduct g m (Fin.tail h)))
    | succ n =>
      change ordinaryCreation (h 0)
        (ordinaryCreationAllInput (h 0) (coherentCreatorProduct g m (Fin.tail h))) (n+1) = 0
      rw [ordinaryCreation_succ]
      change sectorCreation ordinarySectorKernel (ordinaryKernel (h 0)) n
        ((coherentCreatorProduct g m (Fin.tail h)).val n) = 0
      rw [ih (Fin.tail h) n (by omega),map_zero]

lemma coherentJetBlockScalar_sqrt (m k : ℕ) :
    coherentJetBlockScalar m k = Real.sqrt ((m+k).factorial:ℝ)/(k.factorial:ℝ) := by
  unfold coherentJetBlockScalar
  have hk : (k.factorial:ℝ) ≠ 0 := by positivity
  have hs : Real.sqrt ((m+k).factorial:ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have he : ((m+k).factorial:ℝ) =
      Real.sqrt ((m+k).factorial:ℝ)*Real.sqrt ((m+k).factorial:ℝ) := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (m+k).factorial)]
  calc
    _ = (Real.sqrt ((m+k).factorial:ℝ)*Real.sqrt ((m+k).factorial:ℝ))/
        ((k.factorial:ℝ)*Real.sqrt ((m+k).factorial:ℝ)) := congrArg
          (fun t : ℝ => t/((k.factorial:ℝ)*Real.sqrt ((m+k).factorial:ℝ))) he
    _ = _ := by
      field_simp [hk,hs]
      <;> ring

lemma coherentJetBlockScalar_creator_step (m k : ℕ) :
    Real.sqrt (m+k+1:ℝ)*coherentJetBlockScalar m k = coherentJetBlockScalar (m+1) k := by
  rw [coherentJetBlockScalar_sqrt,coherentJetBlockScalar_sqrt,
    show (m+1)+k = (m+k)+1 by omega,Nat.factorial_succ,Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg (α := ℝ) (m+k+1))]
  push_cast
  ring

def coherentJetAmbient (m : ℕ) (g : OneBoson) (h : Fin m → OneBoson) : Carrier :=
  (numberWeightedGraph Sector 0 le_rfl).domain.subtype
    (show (numberWeightedGraph Sector 0 le_rfl).domain from coherentJet m 0 le_rfl g h)

set_option backward.isDefEq.respectTransparency.types false in
lemma coherentJet_ambient_independent (m : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (g : OneBoson) (h : Fin m → OneBoson) :
    (numberWeightedGraph Sector r hr).domain.subtype
      (show (numberWeightedGraph Sector r hr).domain from coherentJet m r hr g h) =
    coherentJetAmbient m g h := by
  change (numberWeightedGraph Sector r hr).domain.subtype
      (show (numberWeightedGraph Sector r hr).domain from coherentJet m r hr g h) =
    (numberWeightedGraph Sector 0 le_rfl).domain.subtype
      (show (numberWeightedGraph Sector 0 le_rfl).domain from coherentJet m 0 le_rfl g h)
  apply lp.ext
  funext n
  by_cases hn : n < m
  · rw [coherentJet_coordinate_below m n r hr g h hn,
      coherentJet_coordinate_below m n 0 le_rfl g h hn]
  · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (le_of_not_gt hn)
    rw [coherentJet_coordinate,coherentJet_coordinate]

set_option backward.isDefEq.respectTransparency.types false in
def coherentJetAll (m : ℕ) (g : OneBoson) (h : Fin m → OneBoson) : EveryOrdinaryNumberVector := by
  refine ⟨coherentJetAmbient m g h,?_⟩
  intro r hr
  rw [← coherentJet_ambient_independent m r hr g h]
  exact (show (numberWeightedGraph Sector r hr).domain from coherentJet m r hr g h).property

lemma coherentJetAll_zero (g : OneBoson) (h : Fin 0 → OneBoson) :
    coherentJetAll 0 g h = coherentExponentialAll g := by
  apply Subtype.ext
  exact coherentJet_zero_ambient 0 le_rfl g h

def coherentJetFiniteDerivative (m : ℕ) (r : ℝ) (L : ℕ) (g : OneBoson) :
    OneBoson →L[ℂ] ContinuousMultilinearMap ℂ (fun _ : Fin m => OneBoson) (NumberGraphCarrier Sector r) :=
  ∑ n ∈ Finset.Icc m L, coherentJetPolynomialDerivative m (n-m) r g

set_option backward.isDefEq.respectTransparency.types false in
lemma coherentJetFinite_hasFDerivAt (m : ℕ) (r : ℝ) (L : ℕ) (g : OneBoson) :
    HasFDerivAt (coherentJetFinite m r L) (coherentJetFiniteDerivative m r L g) g := by
  unfold coherentJetFinite coherentJetFiniteDerivative
  convert (HasFDerivAt.fun_sum (u := Finset.Icc m L)
      (fun n _ => coherentJetPolynomial_hasFDerivAt m (n-m) r g)) using 1

lemma coherentJetSectorTensor_update_equal (n : ℕ) (f : Fin n → OneBoson)
    (i j : Fin n) (x : OneBoson) (hij : f i = f j) :
    coherentJetSectorTensor n (Function.update f i x) = coherentJetSectorTensor n (Function.update f j x) := by
  have hf : f ∘ (Equiv.swap i j : Fin n → Fin n) = f := by
    funext k
    by_cases hki : k = i
    · subst k
      simpa only [Function.comp_apply,Equiv.swap_apply_left] using hij.symm
    · by_cases hkj : k = j
      · subst k
        simpa only [Function.comp_apply,Equiv.swap_apply_right] using hij
      · simp only [Function.comp_apply,Equiv.swap_apply_of_ne_of_ne hki hkj]
  have he := Function.update_comp_eq_of_injective f (Equiv.swap i j).injective j x
  rw [Equiv.swap_apply_right,hf] at he
  have ht := coherentJetSectorTensor_permutation n (Function.update f i x) (Equiv.swap i j)
  simp only [Equiv.symm_swap] at ht
  change coherentJetSectorTensor n (Function.update f i x ∘ (Equiv.swap i j : Fin n → Fin n)) = _ at ht
  rw [he] at ht
  exact ht.symm

lemma coherentJetBlockScalar_derivative_step (m k : ℕ) :
    (k+1:ℝ)*coherentJetBlockScalar m (k+1) = coherentJetBlockScalar (m+1) k := by
  have hk : (k.factorial:ℝ) ≠ 0 := by positivity
  have hkp : (k+1:ℝ) ≠ 0 := by positivity
  have hs : Real.sqrt ((m+(k+1)).factorial:ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hfac : ((k+1).factorial:ℝ) = (k+1:ℝ)*(k.factorial:ℝ) := by
    rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  unfold coherentJetBlockScalar
  rw [show (m+1)+k = m+(k+1) by omega,hfac]
  field_simp [hk,hkp,hs]
  <;> ring

lemma coherentJet_factors_append (m k : ℕ) (z : Fin k → OneBoson) (h : Fin m → OneBoson) :
    (fun j => Sum.elim z h
      (((finSumFinEquiv : Fin m ⊕ Fin k ≃ Fin (m+k)).symm.trans (Equiv.sumComm _ _)) j)) =
    Fin.append h z := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [Equiv.trans_apply,finSumFinEquiv_symm_apply_castAdd,Fin.append_left]
    rfl
  · rw [Equiv.trans_apply,finSumFinEquiv_symm_apply_natAdd,Fin.append_right]
    rfl

lemma coherentJetBlock_apply_append (m k : ℕ) (r : ℝ) (z : Fin k → OneBoson) (h : Fin m → OneBoson) :
    coherentJetBlock m k r z h = (coherentJetBlockScalar m k : ℂ) •
      coherentJetWeightedInjection (m+k) r (coherentJetSectorTensor (m+k) (Fin.append h z)) := by
  rw [coherentJetBlock_apply,coherentJet_factors_append]

lemma coherentJet_append_update (m k : ℕ) (v : Fin m → OneBoson) (z : Fin k → OneBoson)
    (i : Fin k) (x : OneBoson) :
    Fin.append v (Function.update z i x) = Function.update (Fin.append v z) (Fin.natAdd m i) x := by
  funext j
  refine Fin.addCases (fun a => ?_) (fun b => ?_) j
  · have hn : Fin.castAdd k a ≠ Fin.natAdd m i := by
      intro he
      have hv := congrArg Fin.val he
      simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
      omega
    simp only [Fin.append_left,Function.update_of_ne hn]
  · by_cases hbi : b = i
    · subst b
      simp only [Fin.append_right,Function.update_self]
    · have hn : Fin.natAdd m b ≠ Fin.natAdd m i := by
        intro he
        exact hbi (Fin.ext (Nat.add_left_cancel (congrArg Fin.val he)))
      simp only [Fin.append_right,Function.update_of_ne hbi,Function.update_of_ne hn]

lemma coherentJetBlock_insertion_equal (m k : ℕ) (r : ℝ) (g h : OneBoson)
    (i j : Fin k) (v : Fin m → OneBoson) :
    coherentJetBlock m k r (Function.update (fun _ => g) i h) v =
      coherentJetBlock m k r (Function.update (fun _ => g) j h) v := by
  rw [coherentJetBlock_apply_append,coherentJetBlock_apply_append,
    coherentJet_append_update,coherentJet_append_update]
  apply congrArg (fun u : Sector (m+k) =>
    (coherentJetBlockScalar m k : ℂ) • coherentJetWeightedInjection (m+k) r u)
  apply coherentJetSectorTensor_update_equal
  simp only [Fin.append_right]

lemma coherentJetPolynomialDerivative_insertion (m k : ℕ) (r : ℝ) (g h : OneBoson) :
    coherentJetPolynomialDerivative m (k+1) r g h =
      (k+1) • coherentJetBlock m (k+1) r (Function.update (fun _ => g) 0 h) := by
  apply ContinuousMultilinearMap.ext
  intro v
  rw [coherentJetPolynomialDerivative_apply]
  have he (i : Fin (k+1)) :
      coherentJetBlock m (k+1) r (Function.update (fun _ => g) i h) v =
      coherentJetBlock m (k+1) r (Function.update (fun _ => g) 0 h) v :=
    coherentJetBlock_insertion_equal m (k+1) r g h i 0 v
  simp_rw [he]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    ContinuousMultilinearMap.smul_apply]

/-- Move the first varying slot to the first direction slot. This is the
finite permutation in the source insertion derivative, including zero arities. -/
def coherentJetInsertionEquiv (m k : ℕ) : Fin m ⊕ Fin (k+1) ≃ Fin (m+1) ⊕ Fin k where
  toFun := Sum.elim (fun i => Sum.inl i.succ)
    (Fin.cases (Sum.inl 0) (fun j => Sum.inr j))
  invFun := Sum.elim (Fin.cases (Sum.inr 0) (fun i => Sum.inl i))
    (fun j => Sum.inr j.succ)
  left_inv a := by
    cases a with
    | inl i => rfl
    | inr j => exact Fin.cases rfl (fun _ => rfl) j
  right_inv a := by
    cases a with
    | inl i => exact Fin.cases rfl (fun _ => rfl) i
    | inr j => rfl

lemma coherentJetInsertionEquiv_factors (m k : ℕ) (g h : OneBoson) (v : Fin m → OneBoson)
    (i : Fin m ⊕ Fin (k+1)) :
    Sum.elim (Fin.cons h v) (fun _ : Fin k => g) (coherentJetInsertionEquiv m k i) =
      Sum.elim v (Function.update (fun _ : Fin (k+1) => g) 0 h) i := by
  cases i with
  | inl j => rfl
  | inr j =>
    refine Fin.cases ?_ (fun a => ?_) j
    · simp only [coherentJetInsertionEquiv,Equiv.coe_fn_mk,Fin.cases_zero,Sum.elim_inr,Sum.elim_inl,
        Fin.cons_zero,Function.update_self]
    · simp only [coherentJetInsertionEquiv,Equiv.coe_fn_mk,Fin.cases_succ,Sum.elim_inr,
        Function.update_of_ne (Fin.succ_ne_zero a)]

lemma coherentJet_append_finSum {m k : ℕ} (v : Fin m → OneBoson) (z : Fin k → OneBoson)
    (i : Fin m ⊕ Fin k) :
    Fin.append v z (finSumFinEquiv i) = Sum.elim v z i := by
  cases i with
  | inl j => simp only [finSumFinEquiv_apply_left,Fin.append_left,Sum.elim_inl]
  | inr j => simp only [finSumFinEquiv_apply_right,Fin.append_right,Sum.elim_inr]

lemma coherentJetTensorInjection_reindex {n p : ℕ} (hn : n = p) (r : ℝ)
    (e : Fin n ≃ Fin p) (f : Fin n → OneBoson) (g : Fin p → OneBoson)
    (hfg : ∀ i, f i = g (e i)) :
    coherentJetWeightedInjection n r (coherentJetSectorTensor n f) =
      coherentJetWeightedInjection p r (coherentJetSectorTensor p g) := by
  cases hn
  have hf : (fun i => g (e i)) = f := funext (fun i => (hfg i).symm)
  have ht := coherentJetSectorTensor_permutation n g e.symm
  simp only [Equiv.symm_symm] at ht
  rw [hf] at ht
  exact congrArg (coherentJetWeightedInjection n r) ht

lemma coherentJet_insertion_tensor (m k : ℕ) (r : ℝ) (g h : OneBoson) (v : Fin m → OneBoson) :
    coherentJetWeightedInjection (m+(k+1)) r
      (coherentJetSectorTensor (m+(k+1))
        (Fin.append v (Function.update (fun _ : Fin (k+1) => g) 0 h))) =
    coherentJetWeightedInjection ((m+1)+k) r
      (coherentJetSectorTensor ((m+1)+k) (Fin.append (Fin.cons h v) (fun _ : Fin k => g))) := by
  let old : Fin m ⊕ Fin (k+1) ≃ Fin (m+(k+1)) := finSumFinEquiv
  let new : Fin (m+1) ⊕ Fin k ≃ Fin ((m+1)+k) := finSumFinEquiv
  let e : Fin (m+(k+1)) ≃ Fin ((m+1)+k) := old.symm.trans ((coherentJetInsertionEquiv m k).trans new)
  apply coherentJetTensorInjection_reindex (by omega) r e
  intro i
  obtain ⟨j,rfl⟩ := old.surjective i
  change Fin.append v (Function.update (fun _ : Fin (k+1) => g) 0 h) (old j) =
    Fin.append (Fin.cons h v) (fun _ : Fin k => g) (new (coherentJetInsertionEquiv m k (old.symm (old j))))
  rw [Equiv.symm_apply_apply]
  change Fin.append v (Function.update (fun _ : Fin (k+1) => g) 0 h) (finSumFinEquiv j) =
    Fin.append (Fin.cons h v) (fun _ : Fin k => g) (finSumFinEquiv (coherentJetInsertionEquiv m k j))
  rw [coherentJet_append_finSum,coherentJet_append_finSum]
  exact (coherentJetInsertionEquiv_factors m k g h v j).symm

lemma coherentJetPolynomialDerivative_next_apply (m k : ℕ) (r : ℝ) (g h : OneBoson)
    (v : Fin m → OneBoson) :
    coherentJetPolynomialDerivative m (k+1) r g h v =
      coherentJetPolynomial (m+1) k r g (Fin.cons h v) := by
  rw [coherentJetPolynomialDerivative_insertion,ContinuousMultilinearMap.smul_apply,
    coherentJetPolynomial,coherentJetBlock_apply_append,coherentJetBlock_apply_append]
  rw [← Nat.cast_smul_eq_nsmul ℂ,smul_smul,coherentJet_insertion_tensor]
  congr 1
  exact_mod_cast coherentJetBlockScalar_derivative_step m k

lemma coherentJetPolynomialDerivative_next (m k : ℕ) (r : ℝ) (g : OneBoson) :
    coherentJetPolynomialDerivative m (k+1) r g =
      coherentJetCurry m r (coherentJetPolynomial (m+1) k r g) := by
  apply ContinuousLinearMap.ext
  intro h
  apply ContinuousMultilinearMap.ext
  intro v
  exact coherentJetPolynomialDerivative_next_apply m k r g h v

lemma coherentJetFiniteDerivative_next (m : ℕ) (r : ℝ) (L : ℕ) (g : OneBoson) :
    coherentJetFiniteDerivative m r L g = coherentJetCurry m r (coherentJetFinite (m+1) r L g) := by
  unfold coherentJetFiniteDerivative coherentJetFinite
  rw [map_sum]
  have hsub : Finset.Icc (m+1) L ⊆ Finset.Icc m L := by
    intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  calc
    _ = ∑ n ∈ Finset.Icc (m+1) L, coherentJetPolynomialDerivative m (n-m) r g := by
      symm
      apply Finset.sum_subset hsub
      intro n hn hnot
      have he : n = m := by
        simp only [Finset.mem_Icc] at hn hnot
        omega
      subst n
      simp only [Nat.sub_self,coherentJetPolynomialDerivative_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      have he : n-m = (n-(m+1))+1 := by
        have hnm := (Finset.mem_Icc.mp hn).1
        omega
      rw [he,coherentJetPolynomialDerivative_next]

set_option backward.isDefEq.respectTransparency.types false in
lemma coherentJetFinite_hasFDerivAt_next (m : ℕ) (r : ℝ) (L : ℕ) (g : OneBoson) :
    HasFDerivAt (coherentJetFinite m r L)
      (coherentJetCurry m r (coherentJetFinite (m+1) r L g)) g := by
  have hd := coherentJetFinite_hasFDerivAt m r L g
  rw [coherentJetFiniteDerivative_next] at hd
  exact hd

lemma coherentJetFinite_continuous (m : ℕ) (r : ℝ) (L : ℕ) :
    Continuous (coherentJetFinite m r L) := by
  unfold coherentJetFinite
  exact continuous_finsetSum _ (fun n _ => coherentJetPolynomial_continuous m (n-m) r)

set_option backward.isDefEq.respectTransparency.types false in
lemma coherentJetFinite_line_hasDerivAt (m : ℕ) (r : ℝ) (L : ℕ) (g h : OneBoson) (t : ℝ) :
    HasDerivAt (fun s : ℝ => coherentJetFinite m r L (g+s • h))
      (coherentJetCurry m r (coherentJetFinite (m+1) r L (g+t • h)) h) t := by
  have hc : HasDerivAt (fun s : ℝ => g+s • h) h t := by
    simpa only [id_eq,one_smul] using ((hasDerivAt_id t).smul_const h).const_add g
  have hp := (coherentJetFinite_hasFDerivAt_next m r L (g+t • h)).restrictScalars ℝ
  convert hp.comp_hasDerivAt t hc using 1 <;> rfl

lemma coherentJetFinite_line_derivative_continuous (m : ℕ) (r : ℝ) (L : ℕ) (g h : OneBoson) :
    Continuous (fun t : ℝ => coherentJetCurry m r (coherentJetFinite (m+1) r L (g+t • h)) h) := by
  have hc : Continuous (fun t : ℝ => g+t • h) := by fun_prop
  have hf := (coherentJetCurry m r).continuous.comp
    ((coherentJetFinite_continuous (m+1) r L).comp hc)
  exact hf.clm_apply continuous_const

lemma coherentJetFinite_integral_increment (m : ℕ) (r : ℝ) (L : ℕ) (g h : OneBoson) :
    coherentJetFinite m r L (g+h)-coherentJetFinite m r L g =
      ∫ t in (0:ℝ)..1, coherentJetCurry m r (coherentJetFinite (m+1) r L (g+t • h)) h := by
  have hc := coherentJetFinite_line_derivative_continuous m r L g h
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0:ℝ)) (b := 1) (fun t _ => coherentJetFinite_line_hasDerivAt m r L g h t)
    (hc.intervalIntegrable 0 1)
  simpa only [one_smul,zero_smul,add_zero] using he.symm

lemma coherentJetFinite_eq_sum (m L : ℕ) (r : ℝ) (g : OneBoson) :
    coherentJetFinite m r L g = ∑ k ∈ Finset.range (L+1-m), coherentJetPolynomial m k r g := by
  unfold coherentJetFinite
  apply Finset.sum_bij (fun n _ => n-m)
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    simp only [Finset.mem_range]
    omega
  · intro n hn j hj he
    simp only [Finset.mem_Icc] at hn hj
    omega
  · intro k hk
    refine ⟨m+k,?_,by omega⟩
    simp only [Finset.mem_range] at hk
    simp only [Finset.mem_Icc]
    omega
  · intro n hn
    rfl

lemma coherentJetFiniteIndex_tendsto (m : ℕ) :
    Tendsto (fun L : ℕ => L+1-m) atTop atTop := by
  apply tendsto_atTop.mpr
  intro N
  filter_upwards [eventually_ge_atTop (N+m)] with L hL
  omega

lemma coherentJetFinite_tendsto (m : ℕ) (r : ℝ) (hr : 0 ≤ r) (g : OneBoson) :
    Tendsto (fun L => coherentJetFinite m r L g) atTop (𝓝 (coherentJetCarrier m r g)) := by
  have ht := (coherentJetCarrier_tendsto m r hr g).comp (coherentJetFiniteIndex_tendsto m)
  simpa only [Function.comp_def,coherentJetFinite_eq_sum] using ht

lemma coherentJetFinite_uniform (m : ℕ) (r R : ℝ) (hr : 0 ≤ r) (hR : 1 ≤ R) :
    TendstoUniformlyOn (fun L g => coherentJetFinite m r L g) (coherentJetCarrier m r)
      atTop (Metric.closedBall (0 : OneBoson) R) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have he := Metric.tendstoUniformlyOn_iff.mp (coherentJetCarrier_uniform m r R hr hR) ε hε
  filter_upwards [(coherentJetFiniteIndex_tendsto m).eventually he] with L hL
  intro g hg
  simpa only [coherentJetFinite_eq_sum] using hL g hg

lemma coherentJet_line_derivatives_uniform (m : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (g h : OneBoson) (a b : ℝ) :
    TendstoUniformlyOn
      (fun L t => coherentJetCurry m r (coherentJetFinite (m+1) r L (g+t • h)) h)
      (fun t => coherentJetCurry m r (coherentJetCarrier (m+1) r (g+t • h)) h)
      atTop (Set.uIcc a b) := by
  let C : ℝ := |a|+|b|+1
  let R : ℝ := 1+‖g‖+C*‖h‖
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hR : 1 ≤ R := by dsimp [R]; nlinarith [norm_nonneg g,mul_nonneg hC (norm_nonneg h)]
  have hball : Set.uIcc a b ⊆ (fun t : ℝ => g+t • h) ⁻¹' Metric.closedBall 0 R := by
    intro t ht
    have ht' : min a b ≤ t ∧ t ≤ max a b := ht
    have habs : ‖t‖ ≤ C := by
      rw [Real.norm_eq_abs]
      apply abs_le.mpr
      constructor
      · apply le_trans (le_min ?_ ?_) ht'.1
        · dsimp [C]; linarith [neg_abs_le a,abs_nonneg b]
        · dsimp [C]; linarith [neg_abs_le b,abs_nonneg a]
      · apply le_trans ht'.2 (max_le ?_ ?_)
        · dsimp [C]; linarith [le_abs_self a,abs_nonneg b]
        · dsimp [C]; linarith [le_abs_self b,abs_nonneg a]
    change dist (g+t • h) 0 ≤ R
    rw [dist_zero_right]
    calc
      _ ≤ ‖g‖+‖t‖*‖h‖ := by simpa only [norm_smul] using norm_add_le g (t • h)
      _ ≤ ‖g‖+C*‖h‖ := add_le_add (le_refl ‖g‖) (mul_le_mul_of_nonneg_right habs (norm_nonneg h))
      _ ≤ R := by dsimp [R]; linarith
  let A := (coherentJetCurry m r).flip h
  have ha (B : ContinuousMultilinearMap ℂ (fun _ : Fin (m+1) => OneBoson) (NumberGraphCarrier Sector r)) :
      A B = coherentJetCurry m r B h := rfl
  have hu := A.uniformContinuous.comp_tendstoUniformlyOn (coherentJetFinite_uniform (m+1) r R hr hR)
  have hv := (hu.comp (fun t : ℝ => g+t • h)).mono hball
  simpa only [Function.comp_def,ha] using hv

/-- The manuscript's real-parameter uniform-derivative bridge passes the
finite integral identity to the complete multilinear-norm carrier. -/
lemma coherentJetCarrier_integral_increment (m : ℕ) (r : ℝ) (hr : 0 ≤ r) (g h : OneBoson) :
    coherentJetCarrier m r (g+h)-coherentJetCarrier m r g =
      ∫ t in (0:ℝ)..1, coherentJetCurry m r (coherentJetCarrier (m+1) r (g+t • h)) h := by
  let d : ℝ → ContinuousMultilinearMap ℂ (fun _ : Fin m => OneBoson) (NumberGraphCarrier Sector r) :=
    fun t => coherentJetCurry m r (coherentJetCarrier (m+1) r (g+t • h)) h
  have hu := GW.Analysis.uniformDerivativeLimit_on_interval
    (J := (Set.univ : Set ℝ)) isOpen_univ (t₀ := (0:ℝ)) (by trivial)
    (cN := fun L t => coherentJetFinite m r L (g+t • h))
    (dN := fun L t => coherentJetCurry m r (coherentJetFinite (m+1) r L (g+t • h)) h)
    (d := d) (c₀ := coherentJetCarrier m r g)
    (fun L t _ => coherentJetFinite_line_hasDerivAt m r L g h t)
    (fun L => (coherentJetFinite_line_derivative_continuous m r L g h).continuousOn)
    (by simpa only [zero_smul,add_zero] using coherentJetFinite_tendsto m r hr g)
    (fun a b _ => coherentJet_line_derivatives_uniform m r hr g h a b)
    (0:ℝ) 1 (by simp [connectedComponentIn_univ])
  have h₁ := coherentJetFinite_tendsto m r hr (g+h)
  have h₂ : Tendsto (fun L => coherentJetFinite m r L (g+h)) atTop
      (𝓝 (GW.Analysis.integratedDerivative 0 (coherentJetCarrier m r g) d 1)) := by
    simpa only [one_smul] using hu.tendsto_at right_mem_uIcc
  have he := tendsto_nhds_unique h₁ h₂
  rw [he,GW.Analysis.integratedDerivative]
  dsimp only [d]
  abel

lemma coherentJet_segment_norm (R : ℝ) (g h : OneBoson)
    (hg : ‖g‖ ≤ R) (hgh : ‖g+h‖ ≤ R) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖g+t • h‖ ≤ R := by
  have he : g+t • h = (1-t) • g+t • (g+h) := by
    rw [smul_add,sub_smul,one_smul]
    abel
  calc
    _ = ‖(1-t) • g+t • (g+h)‖ := congrArg norm he
    _ ≤ ‖(1-t) • g‖+‖t • (g+h)‖ := norm_add_le _ _
    _ = (1-t)*‖g‖+t*‖g+h‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr ht1),abs_of_nonneg ht]
    _ ≤ (1-t)*R+t*R := add_le_add
      (mul_le_mul_of_nonneg_left hg (sub_nonneg.mpr ht1))
      (mul_le_mul_of_nonneg_left hgh ht)
    _ = R := by ring

lemma coherentJetCarrier_lipschitz_increment (m : ℕ) (r R : ℝ) (hr : 0 ≤ r) (hR : 1 ≤ R)
    (g h : OneBoson) (hg : ‖g‖ ≤ R) (hgh : ‖g+h‖ ≤ R) :
    ‖coherentJetCarrier m r (g+h)-coherentJetCarrier m r g‖ ≤ coherentJetConstant (m+1) r R*‖h‖ := by
  rw [coherentJetCarrier_integral_increment m r hr g h]
  have hb (t : ℝ) (ht : t ∈ Set.uIoc (0:ℝ) 1) :
      ‖coherentJetCurry m r (coherentJetCarrier (m+1) r (g+t • h)) h‖ ≤
        coherentJetConstant (m+1) r R*‖h‖ := by
    have ht01 : 0 ≤ t ∧ t ≤ 1 := by simpa [Set.uIcc] using uIoc_subset_uIcc ht
    exact (coherentJetCurry_bound m r _ h).trans
      (mul_le_mul_of_nonneg_right
        (coherentJetCarrier_norm (m+1) r R hr hR (g+t • h)
          (coherentJet_segment_norm R g h hg hgh t ht01.1 ht01.2)) (norm_nonneg h))
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa only [sub_zero,abs_one,mul_one] using hi

lemma coherentJetCarrier_quadratic_remainder (m : ℕ) (r R : ℝ) (hr : 0 ≤ r) (hR : 1 ≤ R)
    (g h : OneBoson) (hg : ‖g‖ ≤ R) (hgh : ‖g+h‖ ≤ R) :
    ‖coherentJetCarrier m r (g+h)-coherentJetCarrier m r g-
      coherentJetCurry m r (coherentJetCarrier (m+1) r g) h‖ ≤
        (1/2:ℝ)*coherentJetConstant (m+2) r R*‖h‖^2 := by
  let A := (coherentJetCurry m r).flip h
  let d : ℝ → ContinuousMultilinearMap ℂ (fun _ : Fin m => OneBoson) (NumberGraphCarrier Sector r) :=
    fun t => A (coherentJetCarrier (m+1) r (g+t • h))
  let d0 := A (coherentJetCarrier (m+1) r g)
  have hd : Continuous d := A.continuous.comp
    ((coherentJetCarrier_continuous (m+1) r hr).comp (by fun_prop))
  have he : coherentJetCarrier m r (g+h)-coherentJetCarrier m r g-d0 =
      ∫ t in (0:ℝ)..1, (d t-d0) := by
    rw [coherentJetCarrier_integral_increment m r hr g h]
    rw [intervalIntegral.integral_sub (hd.intervalIntegrable 0 1)
      ((continuous_const : Continuous (fun _ : ℝ => d0)).intervalIntegrable 0 1)]
    simp only [intervalIntegral.integral_const,sub_zero,one_smul]
    <;> rfl
  change ‖coherentJetCarrier m r (g+h)-coherentJetCarrier m r g-d0‖ ≤ _
  rw [he]
  have hb (t : ℝ) (ht : t ∈ Set.Ioc (0:ℝ) 1) :
      ‖d t-d0‖ ≤ t*coherentJetConstant (m+2) r R*‖h‖^2 := by
    have ht0 : 0 ≤ t := ht.1.le
    have hgt := coherentJet_segment_norm R g h hg hgh t ht0 ht.2
    have hj := coherentJetCarrier_lipschitz_increment (m+1) r R hr hR g (t • h) hg hgt
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht0] at hj
    have he' : d t-d0 = A (coherentJetCarrier (m+1) r (g+t • h)-coherentJetCarrier (m+1) r g) :=
      (A.map_sub _ _).symm
    rw [he']
    calc
      _ ≤ ‖coherentJetCarrier (m+1) r (g+t • h)-coherentJetCarrier (m+1) r g‖*‖h‖ :=
        coherentJetCurry_bound m r _ h
      _ ≤ (coherentJetConstant (m+2) r R*(t*‖h‖))*‖h‖ :=
        mul_le_mul_of_nonneg_right hj (norm_nonneg h)
      _ = _ := by ring
  have hbound : IntervalIntegrable (fun t : ℝ => t*coherentJetConstant (m+2) r R*‖h‖^2) volume 0 1 :=
    (by fun_prop : Continuous (fun t : ℝ => t*coherentJetConstant (m+2) r R*‖h‖^2)).intervalIntegrable 0 1
  have hi := intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (0:ℝ) ≤ 1)
    (Eventually.of_forall (fun t ht => hb t ht)) hbound
  have hnum : (∫ t in (0:ℝ)..1, t*coherentJetConstant (m+2) r R*‖h‖^2) =
      (1/2:ℝ)*coherentJetConstant (m+2) r R*‖h‖^2 := by
    rw [intervalIntegral.integral_mul_const,intervalIntegral.integral_mul_const,integral_id]
    norm_num
  exact hi.trans_eq hnum

/-- The source definite-radius, definite-delta argument gives the full complex
Fréchet derivative in multilinear operator norm. -/
lemma coherentJetCarrier_hasFDerivAt (m : ℕ) (r : ℝ) (hr : 0 ≤ r) (g : OneBoson) :
    HasFDerivAt (coherentJetCarrier m r)
      (coherentJetCurry m r (coherentJetCarrier (m+1) r g)) g := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero,Asymptotics.isLittleO_iff]
  intro ε hε
  let R : ℝ := 1+‖g‖
  let C : ℝ := coherentJetConstant (m+2) r R
  have hC : 0 ≤ C := coherentJetConstant_nonneg _ _ _
  let δ : ℝ := min 1 (2*ε/(C+1))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos (by positivity) (by linarith))
  filter_upwards [Metric.ball_mem_nhds (0 : OneBoson) hδ] with h hh
  have hhδ : ‖h‖ < δ := by simpa only [Metric.mem_ball,dist_zero_right] using hh
  have hh1 : ‖h‖ ≤ 1 := (hhδ.trans_le (min_le_left _ _)).le
  have hhsmall : ‖h‖ < 2*ε/(C+1) := hhδ.trans_le (min_le_right _ _)
  have hlinear : (1/2:ℝ)*C*‖h‖ ≤ ε := by
    have he := (lt_div_iff₀ (show 0 < C+1 by linarith)).mp hhsmall
    nlinarith [norm_nonneg h]
  have hgh : ‖g+h‖ ≤ R := (norm_add_le g h).trans (by dsimp [R]; linarith)
  have hrem := coherentJetCarrier_quadratic_remainder m r R hr
    (by dsimp [R]; linarith [norm_nonneg g]) g h
    (by dsimp [R]; linarith) hgh
  calc
    _ ≤ (1/2:ℝ)*C*‖h‖^2 := hrem
    _ = ((1/2:ℝ)*C*‖h‖)*‖h‖ := by ring
    _ ≤ ε*‖h‖ := mul_le_mul_of_nonneg_right hlinear (norm_nonneg h)


/-- Postcomposition by the actual onto graph-domain isometry, on whole
multilinear maps rather than just their ambient images. -/
def coherentJetDomainTransport (m : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    ContinuousMultilinearMap ℂ (fun _ : Fin m => OneBoson) (NumberGraphCarrier Sector r) →L[ℂ]
      ContinuousMultilinearMap ℂ (fun _ : Fin m => OneBoson) (NumberWeightedDomain Sector r hr) :=
  ContinuousLinearMap.compContinuousMultilinearMapL ℂ (fun _ : Fin m => OneBoson)
    (NumberGraphCarrier Sector r) (NumberWeightedDomain Sector r hr)
    (numberDomainIsometry Sector r hr).symm.toContinuousLinearEquiv.toContinuousLinearMap

lemma coherentJetDomainTransport_norm (m : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (A : ContinuousMultilinearMap ℂ (fun _ : Fin m => OneBoson) (NumberGraphCarrier Sector r)) :
    ‖coherentJetDomainTransport m r hr A‖ = ‖A‖ :=
  (numberDomainIsometry Sector r hr).symm.toLinearIsometry.norm_compContinuousMultilinearMap A

def coherentJetWeightedCurry (m : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    ContinuousMultilinearMap ℂ (fun _ : Fin (m+1) => OneBoson) (NumberWeightedDomain Sector r hr) →L[ℂ]
      (OneBoson →L[ℂ] ContinuousMultilinearMap ℂ (fun _ : Fin m => OneBoson) (NumberWeightedDomain Sector r hr)) :=
  (continuousMultilinearCurryLeftEquiv ℂ (fun _ : Fin (m+1) => OneBoson)
    (NumberWeightedDomain Sector r hr)).toContinuousLinearEquiv.toContinuousLinearMap

lemma coherentJetDomainTransport_apply (m : ℕ) (r : ℝ) (hr : 0 ≤ r) (g : OneBoson) :
    coherentJetDomainTransport m r hr (coherentJetCarrier m r g) = coherentJet m r hr g := rfl

lemma coherentJet_transport_derivative (m : ℕ) (r : ℝ) (hr : 0 ≤ r) (g : OneBoson) :
    (coherentJetDomainTransport m r hr).comp
      (coherentJetCurry m r (coherentJetCarrier (m+1) r g)) =
      coherentJetWeightedCurry m r hr (coherentJet (m+1) r hr g) := by
  ext h v
  rfl

lemma coherentJet_hasFDerivAt (m : ℕ) (r : ℝ) (hr : 0 ≤ r) (g : OneBoson) :
    HasFDerivAt (coherentJet m r hr)
      (coherentJetWeightedCurry m r hr (coherentJet (m+1) r hr g)) g := by
  have h := (coherentJetDomainTransport m r hr).hasFDerivAt.comp g
    (coherentJetCarrier_hasFDerivAt m r hr g)
  rw [coherentJet_transport_derivative] at h
  convert h using 1 <;> rfl

lemma coherentJet_derivative_continuous (m : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    Continuous (fun g => coherentJetWeightedCurry m r hr (coherentJet (m+1) r hr g)) := by
  have h := (coherentJetDomainTransport (m+1) r hr).continuous.comp
    (coherentJetCarrier_continuous (m+1) r hr)
  exact (coherentJetWeightedCurry m r hr).continuous.comp h

lemma coherentJet_quadratic_remainder (m : ℕ) (r R : ℝ) (hr : 0 ≤ r) (hR : 1 ≤ R)
    (g h : OneBoson) (hg : ‖g‖ ≤ R) (hgh : ‖g+h‖ ≤ R) :
    ‖coherentJet m r hr (g+h)-coherentJet m r hr g-
      coherentJetWeightedCurry m r hr (coherentJet (m+1) r hr g) h‖ ≤
        (1/2:ℝ)*coherentJetConstant (m+2) r R*‖h‖^2 := by
  have he : coherentJet m r hr (g+h)-coherentJet m r hr g-
      coherentJetWeightedCurry m r hr (coherentJet (m+1) r hr g) h =
      coherentJetDomainTransport m r hr (coherentJetCarrier m r (g+h)-coherentJetCarrier m r g-
        coherentJetCurry m r (coherentJetCarrier (m+1) r g) h) := by
    ext v
    simp only [map_sub]
    rfl
  rw [he,coherentJetDomainTransport_norm]
  exact coherentJetCarrier_quadratic_remainder m r R hr hR g h hg hgh


lemma coherentJetTensor_kernel (n : ℕ) (h : Fin n → OneBoson) :
    (ordinarySectorKernel n (coherentJetSectorTensor n h) : AmbientSector n) =
      symmetrizer n (rawTensor n h) := by
  cases n with
  | zero =>
    change (kernelVacuum (1:ℂ) : AmbientSector 0) = symmetrizer 0 (rawTensor 0 h)
    rw [rawTensor_zero,symmetrizer_of_fixed 0 _
      ((ordinaryKernelFixed_iff 0 _).mp (kernelVacuum_fixed _))]
    apply Lp.ext
    filter_upwards [kernelVacuum_ae (1:ℂ),vacuumAdapter_ae (1:ℂ)] with k hk hv
    exact hk.trans hv.symm
  | succ n => rfl

lemma coherentJetTensor_create (n : ℕ) (f : OneBoson) (h : Fin n → OneBoson) :
    sectorCreation ordinarySectorKernel (ordinaryKernel f) n (coherentJetSectorTensor n h) =
      (Real.sqrt (n+1:ℕ) : ℂ) • coherentJetSectorTensor (n+1) (Fin.cons f h) := by
  apply (ordinarySectorKernel (n+1)).injective
  simp only [sectorCreation,ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.apply_symm_apply,map_smul]
  apply Subtype.ext
  rw [kernelCreation_value,ordinaryKernelSymmetrizer,coherentJetTensor_kernel,
    creationRaw_symmetrizer_absorb,ordinaryKernelCreationRaw,creationPrepend_tensor]
  change _ = (Real.sqrt (n+1:ℕ) : ℂ) •
    (ordinarySectorKernel (n+1) (coherentJetSectorTensor (n+1) (Fin.cons f h)) : AmbientSector (n+1))
  rw [coherentJetTensor_kernel]

def coherentJetFactors (n m : ℕ) (h : Fin m → OneBoson) (g : OneBoson) : Fin n → OneBoson :=
  fun i => if hi : i.val < m then h ⟨i.val,hi⟩ else g

def coherentJetCoefficient (n m : ℕ) : ℝ := Real.sqrt (n.factorial:ℝ)/((n-m).factorial:ℝ)

lemma coherentJetCoefficient_step (n m : ℕ) :
    Real.sqrt (n+1:ℕ)*coherentJetCoefficient n m = coherentJetCoefficient (n+1) (m+1) := by
  unfold coherentJetCoefficient
  rw [Nat.succ_sub_succ_eq_sub,Nat.factorial_succ,Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg (α := ℝ) (n+1))]
  ring

lemma coherentJetCoefficient_zero (n : ℕ) :
    coherentJetCoefficient n 0 = (Real.sqrt (n.factorial:ℝ))⁻¹ := by
  unfold coherentJetCoefficient
  rw [Nat.sub_zero]
  have hs : Real.sqrt (n.factorial:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hf : (n.factorial:ℝ) ≠ 0 := by positivity
  have he := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n.factorial)
  field_simp
  nlinarith

lemma coherentJetFactors_cons (n m : ℕ) (h : Fin (m+1) → OneBoson) (g : OneBoson) :
    Fin.cons (h 0) (coherentJetFactors n m (Fin.tail h) g) =
      coherentJetFactors (n+1) (m+1) h g := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [coherentJetFactors]
  · simp only [Fin.cons_succ,coherentJetFactors,Fin.val_succ]
    by_cases hj : j.val < m
    · rw [dif_pos hj,dif_pos (by omega)]
      rfl
    · rw [dif_neg hj,dif_neg (by omega)]

lemma coherentCreatorProduct_coordinate (g : OneBoson) (m : ℕ) (h : Fin m → OneBoson)
    (n : ℕ) (hn : m ≤ n) :
    (coherentCreatorProduct g m h).val n =
      (coherentJetCoefficient n m : ℂ) • coherentJetSectorTensor n (coherentJetFactors n m h g) := by
  induction m generalizing n with
  | zero =>
    rw [coherentCreatorProduct_zero,exponentialVector_apply]
    have hf : coherentJetFactors n 0 h g = fun _ => g := by
      funext i
      simp [coherentJetFactors]
    rw [hf,coherentJetSectorTensor_diagonal,coherentJetCoefficient_zero]
    rfl
  | succ m ih =>
    cases n with
    | zero => omega
    | succ n =>
      change ordinaryCreation (h 0)
        (ordinaryCreationAllInput (h 0) (coherentCreatorProduct g m (Fin.tail h))) (n+1) = _
      rw [ordinaryCreation_succ]
      change sectorCreation ordinarySectorKernel (ordinaryKernel (h 0)) n
        ((coherentCreatorProduct g m (Fin.tail h)).val n) = _
      rw [ih (Fin.tail h) n (by omega),map_smul,coherentJetTensor_create,smul_smul,
        ← Complex.ofReal_mul,mul_comm (coherentJetCoefficient n m),coherentJetCoefficient_step,
        coherentJetFactors_cons]


lemma coherentJetFactors_append (m k : ℕ) (h : Fin m → OneBoson) (g : OneBoson) :
    coherentJetFactors (m+k) m h g = Fin.append h (fun _ : Fin k => g) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [coherentJetFactors,Fin.val_castAdd,Fin.append_left,dif_pos j.isLt]
  · simp only [coherentJetFactors,Fin.val_natAdd,Fin.append_right]
    rw [dif_neg (by omega)]

lemma coherentJetAmbient_coordinate (g : OneBoson) (m : ℕ) (h : Fin m → OneBoson)
    (n : ℕ) (hn : m ≤ n) :
    coherentJetAmbient m g h n =
      (coherentJetCoefficient n m : ℂ) • coherentJetSectorTensor n (coherentJetFactors n m h g) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  change ((numberWeightedGraph Sector 0 le_rfl).domain.subtype (coherentJet m 0 le_rfl g h)) (m+k) = _
  rw [coherentJet_coordinate,coherentJet_factors_append,coherentJetFactors_append,
    coherentJetBlockScalar_sqrt]
  simp only [coherentJetCoefficient,Nat.add_sub_cancel_left]

lemma coherentCreatorProduct_eq_ambient (g : OneBoson) (m : ℕ) (h : Fin m → OneBoson) :
    (coherentCreatorProduct g m h).val = coherentJetAmbient m g h := by
  apply lp.ext
  funext n
  by_cases hn : n < m
  · rw [coherentCreatorProduct_coordinate_below g m h n hn]
    exact (coherentJet_coordinate_below m n 0 le_rfl g h hn).symm
  · rw [coherentCreatorProduct_coordinate g m h n (le_of_not_gt hn),
      coherentJetAmbient_coordinate g m h n (le_of_not_gt hn)]

lemma coherentJet_creator_product (m : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (g : OneBoson) (h : Fin m → OneBoson) :
    (numberWeightedGraph Sector r hr).domain.subtype
      (show (numberWeightedGraph Sector r hr).domain from coherentJet m r hr g h) =
      (coherentCreatorProduct g m h).val := by
  rw [coherentJet_ambient_independent,coherentCreatorProduct_eq_ambient]

def coherentExponentialWeighted (r : ℝ) (hr : 0 ≤ r) (g : OneBoson) :
    NumberWeightedDomain Sector r hr := coherentJet 0 r hr g (fun i => Fin.elim0 i)

lemma coherentExponentialWeighted_ambient (r : ℝ) (hr : 0 ≤ r) (g : OneBoson) :
    (numberWeightedGraph Sector r hr).domain.subtype
      (show (numberWeightedGraph Sector r hr).domain from coherentExponentialWeighted r hr g) = exponentialVector g :=
  coherentJet_zero_ambient r hr g _

/-- The proved CJ3 and continuity identities themselves form the source's
all-finite-order derivative witness. The smooth infinity order is used,
without any analytic-order assertion. -/
lemma coherentExponentialWeighted_hasFTaylorSeries (r : ℝ) (hr : 0 ≤ r) :
    HasFTaylorSeriesUpTo (⊤ : ℕ∞) (coherentExponentialWeighted r hr)
      (fun g m => coherentJet m r hr g) := by
  constructor
  · intro g
    change coherentJet 0 r hr g 0 = coherentJet 0 r hr g (fun i => Fin.elim0 i)
    exact congrArg (coherentJet 0 r hr g) (Subsingleton.elim _ _)
  · intro m hm g
    convert coherentJet_hasFDerivAt m r hr g using 1 <;> rfl
  · intro m hm
    exact (coherentJetDomainTransport m r hr).continuous.comp (coherentJetCarrier_continuous m r hr)

lemma coherentExponentialWeighted_contDiff (k : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    ContDiff ℂ k (coherentExponentialWeighted r hr) := by
  apply HasFTaylorSeriesUpTo.contDiff (n := (k : ℕ∞))
  exact (coherentExponentialWeighted_hasFTaylorSeries r hr).of_le (by simp)

lemma coherentExponentialWeighted_iteratedFDeriv (m : ℕ) (r : ℝ) (hr : 0 ≤ r) (g : OneBoson) :
    iteratedFDeriv ℂ m (coherentExponentialWeighted r hr) g = coherentJet m r hr g :=
  ((coherentExponentialWeighted_hasFTaylorSeries r hr).eq_iteratedFDeriv (by simp) g).symm


end GW.Fock
