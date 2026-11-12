module
public import GW.Regularity.RegRemainder
public import GW.Gross.MainGrossForm
@[expose] public section

-- Compiled component Adapters03
noncomputable section
open MeasureTheory Filter GW.Regularity
open scoped Topology ENNReal BigOperators
namespace GW.Fock
open GW.Gross

def regularFieldMoment (r : ℝ) (f : OneBoson)
    (hf : MemLp (fun k : GW.Space => ((‖k‖^r : ℝ) : ℂ)*f k) 2 (volume : Measure GW.Space)) : OneBoson :=
  hf.toLp _

lemma regularField_coefficient_norm (ε r : ℝ) (hε : 0 < ε) (f : OneBoson)
    (hf : MemLp (fun k : GW.Space => ((‖k‖^r : ℝ) : ℂ)*f k) 2 (volume : Measure GW.Space)) :
    ‖fractionalRemainderCoefficientMap ε r hε f‖ ≤ ‖regularFieldMoment r f hf‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [fractionalRemainderCoefficient_ae ε r hε f,hf.coeFn_toLp] with k hG hM
  change (rho ε r ‖k‖ : ℂ)*f k = fractionalRemainderCoefficientMap ε r hε f k at hG
  change regularFieldMoment r f hf k = ((‖k‖^r : ℝ) : ℂ)*f k at hM
  rw [← hG,hM,norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
    Real.norm_of_nonneg (rho_bounds (r := r) hε (norm_nonneg k)).1,
    Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  exact mul_le_mul_of_nonneg_right ((rho_bounds (r := r) hε (norm_nonneg k)).2.trans (min_le_left _ _))
    (norm_nonneg _)

def regularFieldGraphMap (f : OneBoson) : FreeGraphDomain →L[ℂ] Physical :=
  (grossFormFieldMap f).comp commutatorGraphRootMap

lemma regularFieldGraphMap_value (f : OneBoson) (u : FreeGraphDomain) :
    regularFieldGraphMap f u = commutatorAnnihilatorGraphMap f u+commutatorCreatorGraphMap f u := rfl

lemma regularFieldGraphMap_graph (f : OneBoson) (u : FreeGraphDomain) :
    (freeGraphDomainInclusion u,regularFieldGraphMap f u) ∈
      (generalizedField (phaseMultiplicationKernel f)).graph := by
  simpa only [regularFieldGraphMap,ContinuousLinearMap.comp_apply,commutatorGraphRootMap_value] using
    grossFormFieldMap_graph f (commutatorGraphRootMap u)

lemma regularFieldGraphMap_bound (f : OneBoson) (u : FreeGraphDomain) :
    ‖regularFieldGraphMap f u‖ ≤ 2*‖f‖*‖commutatorGraphRootMap u‖ :=
  grossFormFieldMap_bound f (commutatorGraphRootMap u)

lemma regularField_remainder_identity (ε r : ℝ) (hε : 0 < ε) (f : OneBoson) (u : FreeGraphDomain) :
    radialRegularizer ε r hε (regularFieldGraphMap f u) =
      regularFieldGraphMap (fractionalRemainderCoefficientMap ε r hε f) u +
        (fractionalRemainderMinus ε r hε f u+fractionalRemainderPlus ε r hε f u) := by
  rw [regularFieldGraphMap_value,map_add,fractionalRemainderMinus_identity,fractionalRemainderPlus_identity,
    regularFieldGraphMap_value]
  abel

lemma regularField_mixed_minus_le_plus (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (u : FreeGraphDomain) :
    ‖fractionalRemainderMixedOperator false r (fractionalRemainderMixedInput false r hr hr1 u)‖ ≤
      ‖fractionalRemainderMixedOperator true r (fractionalRemainderMixedInput true r hr hr1 u)‖ := by
  obtain ⟨hm,hb⟩ := physicalSectorMultiplier_domination (fractionalRemainderMixedSymbol false r)
    (fractionalRemainderMixedSymbol true r) (fractionalRemainderMixedSymbol_measurable false r) zero_le_one
    (fun n q => by
      rw [abs_of_nonneg (fractionalRemainderMixedSymbol_nonneg false r n q),
        abs_of_nonneg (fractionalRemainderMixedSymbol_nonneg true r n q),one_mul]
      change ‖q‖^r*Real.sqrt ((n:ℝ)+0) ≤ ‖q‖^r*Real.sqrt ((n:ℝ)+1)
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith : (n:ℝ)+0 ≤ (n:ℝ)+1))
        (Real.rpow_nonneg (norm_nonneg _) _))
    (fractionalRemainderMixedInput true r hr hr1 u)
  simpa only [fractionalRemainderMixedOperator,fractionalRemainderMixedInput,one_mul] using hb

end GW.Fock

-- Compiled component Family02
noncomputable section
open MeasureTheory Filter GW.Regularity
open scoped Topology ENNReal BigOperators
namespace GW.Fock

lemma regularField_coefficient_family_bound (ε r : ℝ) (hε : 0 < ε) (fs : Fin 3 → OneBoson)
    (hf : ∀ j, MemLp (fun k : GW.Space => ((‖k‖^r : ℝ) : ℂ)*fs j k) 2 (volume : Measure GW.Space)) :
    annihilationEscapeAmplitude (fun j => fractionalRemainderCoefficientMap ε r hε (fs j)) ≤
      annihilationEscapeAmplitude (fun j => regularFieldMoment r (fs j) (hf j)) := by
  have h := annihilationEscape_family_mul_bound
    (fun j => fractionalRemainderCoefficientMap ε r hε (fs j))
    (fun j => regularFieldMoment r (fs j) (hf j)) 1 zero_le_one
    (fun j => by simpa only [mul_one] using regularField_coefficient_norm ε r hε (fs j) (hf j))
  simpa only [mul_one,annihilationEscapeAmplitude] using h

lemma regularField_family_bound (fs : Fin 3 → OneBoson) (u : FreeGraphDomain) :
    ‖annihilationEscapeFamily (fun j => regularFieldGraphMap (fs j) u)‖ ≤
      2*annihilationEscapeAmplitude fs*‖commutatorGraphRootMap u‖ := by
  have h := annihilationEscape_family_mul_bound
    (fun j => regularFieldGraphMap (fs j) u) fs (2*‖commutatorGraphRootMap u‖) (by positivity)
    (fun j => (regularFieldGraphMap_bound (fs j) u).trans_eq (by ring))
  exact h.trans_eq (by ring)

lemma regularField_uniform_family_bound (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r) (hr1 : r ≤ 1)
    (fs : Fin 3 → OneBoson)
    (hf : ∀ j, MemLp (fun k : GW.Space => ((‖k‖^r : ℝ) : ℂ)*fs j k) 2 (volume : Measure GW.Space))
    (u : FreeGraphDomain) :
    ‖annihilationEscapeFamily (fun j => radialRegularizer ε r hε (regularFieldGraphMap (fs j) u))‖ ≤
      2*annihilationEscapeAmplitude (fun j => regularFieldMoment r (fs j) (hf j))*‖commutatorGraphRootMap u‖ +
      2*annihilationEscapeAmplitude fs*
        ‖fractionalRemainderMixedOperator true r (fractionalRemainderMixedInput true r hr.le hr1 u)‖ := by
  let g := fun j => fractionalRemainderCoefficientMap ε r hε (fs j)
  let A := annihilationEscapeFamily (fun j => regularFieldGraphMap (g j) u)
  let B := annihilationEscapeFamily (fun j => fractionalRemainderMinus ε r hε (fs j) u)
  let D := annihilationEscapeFamily (fun j => fractionalRemainderPlus ε r hε (fs j) u)
  have he : annihilationEscapeFamily (fun j => radialRegularizer ε r hε (regularFieldGraphMap (fs j) u)) = A+(B+D) := by
    apply PiLp.ext
    intro j
    exact regularField_remainder_identity ε r hε (fs j) u
  have hA := (regularField_family_bound g u).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (regularField_coefficient_family_bound ε r hε fs hf)
      (by norm_num : (0:ℝ) ≤ 2)) (norm_nonneg _))
  have hB := (fractionalRemainderMinus_family_bound ε r hε hr hr1 fs u).trans
    (mul_le_mul_of_nonneg_left (regularField_mixed_minus_le_plus r hr.le hr1 u) (norm_nonneg _))
  have hD := fractionalRemainderPlus_family_bound ε r hε hr hr1 fs u
  rw [he]
  exact ((norm_add_le A (B+D)).trans (add_le_add le_rfl (norm_add_le B D))).trans
    ((add_le_add hA (add_le_add hB hD)).trans_eq (by ring))

lemma regularField_family_closed_bound (r : ℝ) (v : Fin 3 → Physical) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ ε : ℝ, ∀ hε : 0 < ε,
      ‖annihilationEscapeFamily (fun j => radialRegularizer ε r hε (v j))‖ ≤ C) :
    ∃ hv : ∀ j, v j ∈ (electronRadialPower r).domain,
      ‖annihilationEscapeFamily (fun j => electronRadialPower r ⟨v j,hv j⟩)‖ ≤ C := by
  have hv : ∀ j, v j ∈ (electronRadialPower r).domain :=
    (radialRegularizer_family_domain_iff r v).mpr ⟨C^2,sq_nonneg _,fun ε hε => by
      have h := pow_le_pow_left₀ (norm_nonneg _) (hb ε hε) 2
      simpa only [PiLp.norm_sq_eq_of_L2,annihilationEscapeFamily,WithLp.ofLp_toLp] using h⟩
  refine ⟨hv,?_⟩
  apply (sq_le_sq₀ (norm_nonneg _) hC).mp
  rw [PiLp.norm_sq_eq_of_L2]
  let z (j : Fin 3) : (physicalSectorMultiplier (fun _ q => ‖q‖^r)).domain := ⟨v j,hv j⟩
  have ht := (radialRegularizer_family_sq_norm_tendsto r z).comp radialRegularizerStep_tendsto
  apply le_of_tendsto ht
  filter_upwards [Eventually.of_forall (fun n : ℕ =>
    pow_le_pow_left₀ (norm_nonneg _) (hb (radialRegularizerStep n) (radialRegularizerStep_pos n)) 2)] with n hn
  simpa only [radialRegularizerTotal,dif_pos (radialRegularizerStep_pos n),Function.comp_apply,z,
    PiLp.norm_sq_eq_of_L2,annihilationEscapeFamily,WithLp.ofLp_toLp] using hn

end GW.Fock

-- Compiled component Main02
noncomputable section
open MeasureTheory Filter GW.Regularity
open scoped Topology ENNReal BigOperators
namespace GW.Fock

/-- Source regular-field domain membership and sharp three-component estimate,
for the actual original phase-field restriction to the original H2. -/
theorem reg_regular_field (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (fs : Fin 3 → OneBoson)
    (hf : ∀ j, MemLp (fun k : GW.Space => ((‖k‖^r : ℝ) : ℂ)*fs j k) 2 (volume : Measure GW.Space))
    (u : FreeGraphDomain) :
    ∃ hv : ∀ j, regularFieldGraphMap (fs j) u ∈ (electronRadialPower r).domain,
      ‖annihilationEscapeFamily (fun j => electronRadialPower r ⟨regularFieldGraphMap (fs j) u,hv j⟩)‖ ≤
        2*annihilationEscapeAmplitude (fun j => regularFieldMoment r (fs j) (hf j))*
          ‖physicalShiftedNumberPower (1/2) (fiberPhysicalRootInput (commutatorGraphRootMap u))‖ +
        2*annihilationEscapeAmplitude fs*
          ‖fractionalRemainderMixedOperator true r (fractionalRemainderMixedInput true r hr.le hr1 u)‖ := by
  rw [fiberPhysicalRoot_norm]
  apply regularField_family_closed_bound r (fun j => regularFieldGraphMap (fs j) u)
    _ (by unfold annihilationEscapeAmplitude; positivity)
  intro ε hε
  exact regularField_uniform_family_bound ε r hε hr hr1 fs hf u

end GW.Fock
