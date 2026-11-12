module
public import GW.Model.ModelFrohlichEstimates
@[expose] public section
noncomputable section
namespace GW.Model

def formCutoffWitness (α ε : ℝ) : ℝ := 1 + 224*unitBallVolume*α/ε^2

def operatorCutoffWitness (α η : ℝ) : ℝ :=
  1 + max (max (504*unitBallVolume*α/η^2) (81*(convolutionConstant*α)^2/η^4))
    (168*Real.sqrt 2*unitBallVolume*α/η)

def convolutionCutoffWitness (α τ : ℝ) : ℝ := 1 + (convolutionConstant*α)^2/τ^4

def standardGrossCutoff (α : ℝ) : ℝ := operatorCutoffWitness α (1/8)

lemma formCutoffWitness_ge_one (α ε : ℝ) (hα : 0 ≤ α) : 1 ≤ formCutoffWitness α ε := by
  unfold formCutoffWitness
  linarith [div_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 224) unitBallVolume_pos.le) hα)
    (sq_nonneg ε)]

lemma operatorCutoffWitness_ge_one (α η : ℝ) (hα : 0 ≤ α) : 1 ≤ operatorCutoffWitness α η := by
  unfold operatorCutoffWitness
  apply le_add_of_nonneg_right
  exact (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) unitBallVolume_pos.le) hα) (sq_nonneg η)).trans
    ((le_max_left _ _).trans (le_max_left _ _))

lemma convolutionCutoffWitness_ge_one (α τ : ℝ) : 1 ≤ convolutionCutoffWitness α τ := by
  unfold convolutionCutoffWitness
  apply le_add_of_nonneg_right
  positivity

lemma formCutoffWitness_bound (α ε K : ℝ) (hα : 0 ≤ α) (hε : 0 < ε)
    (hK : formCutoffWitness α ε ≤ K) :
    2*Real.sqrt (coefficientDTail α K) ≤ ε/2 := by
  have hKpos : 0 < K := zero_lt_one.trans_le ((formCutoffWitness_ge_one α ε hα).trans hK)
  have hth : 224*unitBallVolume*α/ε^2 ≤ K := by
    unfold formCutoffWitness at hK
    linarith
  have hth' := (div_le_iff₀ (sq_pos_of_pos hε)).mp hth
  have hb : 14*unitBallVolume*α/K ≤ (ε/4)^2 := by
    apply (div_le_iff₀ hKpos).mpr
    nlinarith only [hth']
  have hr := Real.sqrt_le_sqrt ((coefficientDTail_bound α K hα hKpos).trans hb)
  rw [Real.sqrt_sq (by positivity)] at hr
  linarith

lemma sqrt_mul_rpow_quarter_fourth (a K : ℝ) (ha : 0 ≤ a) (hK : 0 < K) :
    (Real.sqrt a * K^(-(1/4):ℝ))^4 = a^2/K := by
  rw [mul_pow,show (4:ℕ) = 2*2 by decide,pow_mul (Real.sqrt a),
    Real.sq_sqrt ha,← Real.rpow_natCast _ (2*2),← Real.rpow_mul hK.le]
  have he : -(1/4:ℝ) * ((2*2:ℕ):ℝ) = -1 := by norm_num
  rw [he,Real.rpow_neg_one,div_eq_mul_inv]

lemma convolution_half_square (a K : ℝ) (hK : 0 < K) :
    (a * K^(-(1/2):ℝ))^2 = a^2/K := by
  rw [mul_pow,← Real.rpow_natCast (K^(-(1/2):ℝ)) 2,← Real.rpow_mul hK.le]
  have he : -(1/2:ℝ) * (2:ℕ) = -1 := by norm_num
  rw [he,Real.rpow_neg_one,div_eq_mul_inv]

lemma operatorCutoffWitness_bound (α η K : ℝ) (hα : 0 ≤ α) (hη : 0 < η)
    (hK : operatorCutoffWitness α η ≤ K) :
    2*Real.sqrt (14*unitBallVolume*α/K) +
      Real.sqrt (convolutionConstant*α)*K^(-(1/4):ℝ) +
      56*Real.sqrt 2*unitBallVolume*α/K ≤ η := by
  have hKpos : 0 < K := zero_lt_one.trans_le ((operatorCutoffWitness_ge_one α η hα).trans hK)
  let a := 504*unitBallVolume*α/η^2
  let b := 81*(convolutionConstant*α)^2/η^4
  let c := 168*Real.sqrt 2*unitBallVolume*α/η
  have hmax : max (max a b) c ≤ K := by
    change 1 + max (max a b) c ≤ K at hK
    linarith
  have ha := (div_le_iff₀ (sq_pos_of_pos hη)).mp ((le_max_left a b).trans ((le_max_left (max a b) c).trans hmax))
  have hb := (div_le_iff₀ (pow_pos hη 4)).mp ((le_max_right a b).trans ((le_max_left (max a b) c).trans hmax))
  have hc := (div_le_iff₀ hη).mp ((le_max_right (max a b) c).trans hmax)
  have ha' : 14*unitBallVolume*α/K ≤ (η/6)^2 := by
    apply (div_le_iff₀ hKpos).mpr
    nlinarith only [ha]
  have h₁ : 2*Real.sqrt (14*unitBallVolume*α/K) ≤ η/3 := by
    have h := Real.sqrt_le_sqrt ha'
    rw [Real.sqrt_sq (by positivity)] at h
    linarith
  have hb' : (convolutionConstant*α)^2/K ≤ (η/3)^4 := by
    apply (div_le_iff₀ hKpos).mpr
    nlinarith only [hb]
  have h₂ : Real.sqrt (convolutionConstant*α)*K^(-(1/4):ℝ) ≤ η/3 := by
    apply le_of_pow_le_pow_left₀ (n := 4) (by decide) (by positivity)
    rw [sqrt_mul_rpow_quarter_fourth _ K (mul_nonneg convolutionConstant_nonneg hα) hKpos]
    exact hb'
  have h₃ : 56*Real.sqrt 2*unitBallVolume*α/K ≤ η/3 := by
    apply (div_le_iff₀ hKpos).mpr
    nlinarith only [hc]
  linarith

lemma convolutionCutoffWitness_bound (α τ K : ℝ) (hα : 0 ≤ α) (hτ : 0 < τ)
    (hK : convolutionCutoffWitness α τ ≤ K) :
    Real.sqrt (coefficientTTail α K) ≤ τ := by
  have hKpos : 0 < K := zero_lt_one.trans_le ((convolutionCutoffWitness_ge_one α τ).trans hK)
  have ht : (convolutionConstant*α)^2/τ^4 ≤ K := by
    unfold convolutionCutoffWitness at hK
    linarith
  have ht' := (div_le_iff₀ (pow_pos hτ 4)).mp ht
  have hb : convolutionConstant*α*K^(-(1/2):ℝ) ≤ τ^2 := by
    apply (sq_le_sq₀ (mul_nonneg (mul_nonneg convolutionConstant_nonneg hα) (Real.rpow_nonneg hKpos.le _)) (sq_nonneg τ)).mp
    rw [convolution_half_square _ K hKpos,← pow_mul]
    exact (div_le_iff₀ hKpos).mpr (by simpa [mul_comm] using ht')
  have hr := Real.sqrt_le_sqrt ((coefficientTTail_bound α K hα hKpos).trans hb)
  rwa [Real.sqrt_sq hτ.le] at hr

lemma standardGrossCutoff_ge_one (α : ℝ) (hα : 0 ≤ α) : 1 ≤ standardGrossCutoff α :=
  operatorCutoffWitness_ge_one α (1/8) hα

lemma standardGrossCutoff_bound (α K : ℝ) (hα : 0 ≤ α) (hK : standardGrossCutoff α ≤ K) :
    2*Real.sqrt (14*unitBallVolume*α/K) +
      Real.sqrt (convolutionConstant*α)*K^(-(1/4):ℝ) +
      56*Real.sqrt 2*unitBallVolume*α/K ≤ 1/8 :=
  operatorCutoffWitness_bound α (1/8) K hα (by norm_num) hK

lemma cutoffWitness_zero (ε η τ : ℝ) :
    formCutoffWitness 0 ε = 1 ∧ operatorCutoffWitness 0 η = 1 ∧ convolutionCutoffWitness 0 τ = 1 := by
  simp [formCutoffWitness,operatorCutoffWitness,convolutionCutoffWitness]

end GW.Model
