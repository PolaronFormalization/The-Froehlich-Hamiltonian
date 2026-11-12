module
public import GW.Fock.FockSmoothProductCore
public import GW.Analysis.BridgeShear
public import GW.Analysis.BridgeSymmetrizer
public import GW.Fock.FockGeneralized
public import GW.Fock.FockFrankSchlein
public import GW.Operators.BasicFree
@[expose] public section

-- Compiled component Step01
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal
namespace GW.Fock


lemma sectorFourier_permutation (n : ℕ) (τ : Equiv.Perm (Fin n))
    (U : Lp (AmbientSector n) 2 (volume : Measure GW.Space)) :
    GW.Analysis.physicalFourierUnitary ((permutationL2 n τ).toContinuousLinearMap.compLp U) =
      (permutationL2 n τ).toContinuousLinearMap.compLp (GW.Analysis.physicalFourierUnitary U) :=
  smoothProduct_fourier_postcomp (permutationL2 n τ).toContinuousLinearMap U

lemma sectorFourier_symmetrizer (n : ℕ)
    (U : Lp (AmbientSector n) 2 (volume : Measure GW.Space)) :
    GW.Analysis.physicalFourierUnitary ((symmetrizer n).compLp U) =
      (symmetrizer n).compLp (GW.Analysis.physicalFourierUnitary U) :=
  smoothProduct_fourier_postcomp (symmetrizer n) U

lemma sectorFourier_positive_inclusion (n : ℕ) (U : Lp (Sector (n+1)) 2 (volume : Measure GW.Space)) :
    GW.Analysis.physicalFourierUnitary ((sectorInclusion n).toContinuousLinearMap.compLp U) =
      (sectorInclusion n).toContinuousLinearMap.compLp (GW.Analysis.physicalFourierUnitary U) :=
  smoothProduct_fourier_postcomp (sectorInclusion n).toContinuousLinearMap U

lemma sectorFourier_vacuum_inclusion (U : Lp ℂ 2 (volume : Measure GW.Space)) :
    GW.Analysis.physicalFourierUnitary (vacuumAdapterIsometry.toContinuousLinearMap.compLp U) =
      vacuumAdapterIsometry.toContinuousLinearMap.compLp (GW.Analysis.physicalFourierUnitary U) :=
  smoothProduct_fourier_postcomp vacuumAdapterIsometry.toContinuousLinearMap U

def sectorElectronFourier (n : ℕ) :
    Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure n)) ≃ₗᵢ[ℂ]
      Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure n)) :=
  (((productUnitary (volume : Measure GW.Space) (sectorMeasure n)).symm).trans
    (GW.Analysis.physicalFourierUnitary :
      Lp (AmbientSector n) 2 (volume : Measure GW.Space) ≃ₗᵢ[ℂ]
        Lp (AmbientSector n) 2 (volume : Measure GW.Space))).trans
    (productUnitary (volume : Measure GW.Space) (sectorMeasure n))

set_option backward.isDefEq.respectTransparency.types false in
lemma sectorElectronFourier_symmetrizer (n : ℕ)
    (U : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure n))) :
    sectorElectronFourier n (productSymmetrizer (volume : Measure GW.Space) n U) =
      productSymmetrizer (volume : Measure GW.Space) n (sectorElectronFourier n U) := by
  let T := productUnitary (volume : Measure GW.Space) (sectorMeasure n) (E := ℂ)
  change T (GW.Analysis.physicalFourierUnitary
      (T.symm (T ((symmetrizer n).compLp (T.symm U))))) =
    T ((symmetrizer n).compLp (T.symm (T (GW.Analysis.physicalFourierUnitary (T.symm U)))))
  rw [LinearIsometryEquiv.symm_apply_apply,LinearIsometryEquiv.symm_apply_apply]
  exact congrArg T (sectorFourier_symmetrizer n (T.symm U))



def sectorFourierReorder (n : ℕ) :
    (GW.Space × Coordinates n) × GW.Space ≃ᵐ GW.Space × (GW.Space × Coordinates n) :=
  (MeasurableEquiv.prodAssoc : (GW.Space × Coordinates n) × GW.Space ≃ᵐ GW.Space × (Coordinates n × GW.Space)).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl GW.Space)
      (MeasurableEquiv.prodComm : Coordinates n × GW.Space ≃ᵐ GW.Space × Coordinates n))

lemma sectorFourierReorder_preserving (n : ℕ) :
    MeasurePreserving (sectorFourierReorder n)
      (((volume : Measure GW.Space).prod (sectorMeasure n)).prod (volume : Measure GW.Space))
      ((volume : Measure GW.Space).prod ((volume : Measure GW.Space).prod (sectorMeasure n))) := by
  have hh := ((MeasurePreserving.id (volume : Measure GW.Space)).prod
    (Measure.measurePreserving_swap (μ := sectorMeasure n) (ν := (volume : Measure GW.Space)))).comp
      (measurePreserving_prodAssoc (volume : Measure GW.Space) (sectorMeasure n) (volume : Measure GW.Space))
  convert! hh using 1 <;> rfl

def sectorFourierReorderUnitary (n : ℕ) :
    Lp ℂ 2 ((volume : Measure GW.Space).prod ((volume : Measure GW.Space).prod (sectorMeasure n))) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (((volume : Measure GW.Space).prod (sectorMeasure n)).prod (volume : Measure GW.Space)) :=
  vectorPullback (sectorFourierReorder n) (sectorFourierReorder_preserving n)

lemma sectorFourierReorder_ae (n : ℕ)
    (U : Lp ℂ 2 ((volume : Measure GW.Space).prod ((volume : Measure GW.Space).prod (sectorMeasure n)))) :
    sectorFourierReorderUnitary n U =ᵐ[((volume : Measure GW.Space).prod (sectorMeasure n)).prod (volume : Measure GW.Space)]
      fun p => U (p.1.1,(p.2,p.1.2)) :=
  vectorPullback_ae (sectorFourierReorder n) (sectorFourierReorder_preserving n) U

def sectorFourierSplit (n : ℕ) :
    Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure (n+1))) ≃ₗᵢ[ℂ]
      Lp ℂ 2 ((volume : Measure GW.Space).prod ((volume : Measure GW.Space).prod (sectorMeasure n))) :=
  vectorPullback (MeasurableEquiv.prodCongr (MeasurableEquiv.refl GW.Space) (splitCoordinates n 0).symm)
    ((MeasurePreserving.id (volume : Measure GW.Space)).prod (splitCoordinates_inverse_preserving n 0))

def sectorFourierRawAnnihilation (n : ℕ) (f : GW.OnePhonon) :
    Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure (n+1))) →L[ℂ]
      Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure n)) :=
  (spectatorContraction ((volume : Measure GW.Space).prod (sectorMeasure n)) (volume : Measure GW.Space) f).comp
    ((sectorFourierReorderUnitary n).toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((GW.Analysis.momentumShearWithL2 (E := ℂ) (sectorMeasure n) (-1)).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (sectorFourierSplit n).toContinuousLinearEquiv.toContinuousLinearMap))

lemma sectorFourierRawAnnihilation_norm (n : ℕ) (f : GW.OnePhonon) :
    ‖sectorFourierRawAnnihilation n f‖ ≤ ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
  intro U
  change ‖spectatorContractionClass ((volume : Measure GW.Space).prod (sectorMeasure n)) (volume : Measure GW.Space) f
    (sectorFourierReorderUnitary n (GW.Analysis.momentumShearWithL2 (E := ℂ) (sectorMeasure n) (-1) (sectorFourierSplit n U)))‖ ≤ _
  have hh := spectatorContractionClass_norm ((volume : Measure GW.Space).prod (sectorMeasure n)) (volume : Measure GW.Space) f
    (sectorFourierReorderUnitary n (GW.Analysis.momentumShearWithL2 (E := ℂ) (sectorMeasure n) (-1) (sectorFourierSplit n U)))
  simpa only [LinearIsometryEquiv.norm_map] using hh

def sectorFourierRawCreation (n : ℕ) (f : GW.OnePhonon) :
    Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure n)) →L[ℂ]
      Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure (n+1))) :=
  (sectorFourierSplit n).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((GW.Analysis.momentumShearWithL2 (E := ℂ) (sectorMeasure n) 1).toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((sectorFourierReorderUnitary n).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (productFunctionMap ((volume : Measure GW.Space).prod (sectorMeasure n)) (volume : Measure GW.Space) f)))

lemma sectorFourierRawCreation_norm (n : ℕ) (f : GW.OnePhonon)
    (U : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure n))) :
    ‖sectorFourierRawCreation n f U‖ = ‖f‖*‖U‖ := by
  change ‖(sectorFourierSplit n).symm (GW.Analysis.momentumShearWithL2 (E := ℂ) (sectorMeasure n) 1
    ((sectorFourierReorderUnitary n).symm
      (productFunction ((volume : Measure GW.Space).prod (sectorMeasure n)) (volume : Measure GW.Space) U f)))‖ = _
  rw [LinearIsometryEquiv.norm_map,LinearIsometryEquiv.norm_map,LinearIsometryEquiv.norm_map,productFunction_norm,mul_comm]


lemma sectorFourierSplit_ae (n : ℕ)
    (U : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure (n+1)))) :
    sectorFourierSplit n U =ᵐ[(volume : Measure GW.Space).prod ((volume : Measure GW.Space).prod (sectorMeasure n))]
      fun p => U (p.1,(splitCoordinates n 0).symm p.2) :=
  vectorPullback_ae (MeasurableEquiv.prodCongr (MeasurableEquiv.refl GW.Space) (splitCoordinates n 0).symm)
    ((MeasurePreserving.id (volume : Measure GW.Space)).prod (splitCoordinates_inverse_preserving n 0)) U

def sectorFourierAnnInput (n : ℕ)
    (U : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure (n+1)))) :
    Lp ℂ 2 (((volume : Measure GW.Space).prod (sectorMeasure n)).prod (volume : Measure GW.Space)) :=
  sectorFourierReorderUnitary n (GW.Analysis.momentumShearWithL2 (E := ℂ) (sectorMeasure n) (-1) (sectorFourierSplit n U))

set_option backward.isDefEq.respectTransparency.types false in
lemma sectorFourierAnnInput_ae (n : ℕ)
    (U : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure (n+1)))) :
    sectorFourierAnnInput n U =ᵐ[((volume : Measure GW.Space).prod (sectorMeasure n)).prod (volume : Measure GW.Space)]
      fun p => U (p.1.1-p.2,(splitCoordinates n 0).symm (p.2,p.1.2)) := by
  let X := sectorFourierSplit n U
  let Y := GW.Analysis.momentumShearWithL2 (E := ℂ) (sectorMeasure n) (-1) X
  have hr := sectorFourierReorder_preserving n
  have hs := GW.Analysis.momentumShearWith_preserving (sectorMeasure n) (-1)
  filter_upwards [sectorFourierReorder_ae n Y,
    hr.quasiMeasurePreserving.ae (GW.Analysis.momentumShearWithL2_ae (E := ℂ) (sectorMeasure n) (-1) X),
    (hs.comp hr).quasiMeasurePreserving.ae (sectorFourierSplit_ae n U)] with p hR hS hX
  calc
    sectorFourierAnnInput n U p = Y (p.1.1,(p.2,p.1.2)) := hR
    _ = X (p.1.1+(-1:ℝ) • p.2,(p.2,p.1.2)) := hS
    _ = U (p.1.1+(-1:ℝ) • p.2,(splitCoordinates n 0).symm (p.2,p.1.2)) := hX
    _ = _ := by rw [neg_one_smul,sub_eq_add_neg]

set_option backward.isDefEq.respectTransparency.types false in
lemma sectorFourierRawAnnihilation_ae (n : ℕ) (f : GW.OnePhonon)
    (U : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure (n+1)))) :
    sectorFourierRawAnnihilation n f U =ᵐ[(volume : Measure GW.Space).prod (sectorMeasure n)] fun p =>
      ∫ k : GW.Space, (starRingEnd ℂ) (f k)*U (p.1-k,(splitCoordinates n 0).symm (k,p.2)) ∂volume := by
  have hi := Measure.ae_ae_of_ae_prod (sectorFourierAnnInput_ae n U)
  have hc := spectatorContractionClass_ae ((volume : Measure GW.Space).prod (sectorMeasure n)) (volume : Measure GW.Space) f
    (sectorFourierAnnInput n U)
  filter_upwards [hi,hc] with p hi hc
  change spectatorContractionClass ((volume : Measure GW.Space).prod (sectorMeasure n)) (volume : Measure GW.Space) f
    (sectorFourierAnnInput n U) p = _
  rw [hc]
  change (∫ k : GW.Space, (starRingEnd ℂ) (f k) • sectorFourierAnnInput n U (p,k) ∂volume) = _
  apply integral_congr_ae
  filter_upwards [hi] with k hk
  change (starRingEnd ℂ) (f k)*sectorFourierAnnInput n U (p,k) = _
  exact congrArg (fun z : ℂ => (starRingEnd ℂ) (f k)*z) hk

lemma sectorFourierRawAnnihilation_integrable (n : ℕ) (f : GW.OnePhonon)
    (U : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure (n+1)))) :
    ∀ᵐ p ∂((volume : Measure GW.Space).prod (sectorMeasure n)),
      Integrable (fun k : GW.Space => (starRingEnd ℂ) (f k)*
        U (p.1-k,(splitCoordinates n 0).symm (k,p.2))) (volume : Measure GW.Space) := by
  have hi := Measure.ae_ae_of_ae_prod (sectorFourierAnnInput_ae n U)
  filter_upwards [hi,product_slice_memLp ((volume : Measure GW.Space).prod (sectorMeasure n))
    (volume : Measure GW.Space) (sectorFourierAnnInput n U)] with p hi hp
  have hh := slice_contraction_integrable (volume : Measure GW.Space) f hp
  apply hh.congr
  filter_upwards [hi] with k hk
  change (starRingEnd ℂ) (f k)*sectorFourierAnnInput n U (p,k) = _
  exact congrArg (fun z : ℂ => (starRingEnd ℂ) (f k)*z) hk



lemma sectorFourier_pullback_symm_ae {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν)
    (U : Lp ℂ 2 μ) :
    (vectorPullback e he).symm U =ᵐ[ν] fun y => U (e.symm y) := by
  have hh := vectorPullback_ae e he ((vectorPullback e he).symm U)
  rw [LinearIsometryEquiv.apply_symm_apply] at hh
  have hp := (he.symm e).quasiMeasurePreserving.ae hh
  filter_upwards [hp] with y hy
  exact (hy.trans (congrArg ((vectorPullback e he).symm U) (e.apply_symm_apply y))).symm

lemma sectorFourierSplit_symm_ae (n : ℕ)
    (U : Lp ℂ 2 ((volume : Measure GW.Space).prod ((volume : Measure GW.Space).prod (sectorMeasure n)))) :
    (sectorFourierSplit n).symm U =ᵐ[(volume : Measure GW.Space).prod (sectorMeasure (n+1))]
      fun p => U (p.1,splitCoordinates n 0 p.2) := by
  have hh := sectorFourier_pullback_symm_ae
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl GW.Space) (splitCoordinates n 0).symm)
    ((MeasurePreserving.id (volume : Measure GW.Space)).prod (splitCoordinates_inverse_preserving n 0)) U
  exact hh

lemma sectorFourierReorder_symm_ae (n : ℕ)
    (U : Lp ℂ 2 (((volume : Measure GW.Space).prod (sectorMeasure n)).prod (volume : Measure GW.Space))) :
    (sectorFourierReorderUnitary n).symm U =ᵐ[(volume : Measure GW.Space).prod ((volume : Measure GW.Space).prod (sectorMeasure n))]
      fun p => U ((p.1,p.2.2),p.2.1) :=
  sectorFourier_pullback_symm_ae (sectorFourierReorder n) (sectorFourierReorder_preserving n) U

set_option backward.isDefEq.respectTransparency.types false in
lemma sectorFourierRawCreation_ae (n : ℕ) (f : GW.OnePhonon)
    (U : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure n))) :
    sectorFourierRawCreation n f U =ᵐ[(volume : Measure GW.Space).prod (sectorMeasure (n+1))]
      fun p => f (p.2 0)*U (p.1+p.2 0,fun i => p.2 ((0 : Fin (n+1)).succAbove i)) := by
  let X := productFunction ((volume : Measure GW.Space).prod (sectorMeasure n)) (volume : Measure GW.Space) U f
  let Y := (sectorFourierReorderUnitary n).symm X
  let Z := GW.Analysis.momentumShearWithL2 (E := ℂ) (sectorMeasure n) 1 Y
  let s := MeasurableEquiv.prodCongr (MeasurableEquiv.refl GW.Space) (splitCoordinates n 0)
  have hs : MeasurePreserving s ((volume : Measure GW.Space).prod (sectorMeasure (n+1)))
      ((volume : Measure GW.Space).prod ((volume : Measure GW.Space).prod (sectorMeasure n))) :=
    (MeasurePreserving.id (volume : Measure GW.Space)).prod (splitCoordinates_preserving n 0)
  have ht := (GW.Analysis.momentumShearWith_preserving (sectorMeasure n) 1).comp hs
  have hr := (sectorFourierReorder_preserving n).symm (sectorFourierReorder n)
  filter_upwards [sectorFourierSplit_symm_ae n Z,
    hs.quasiMeasurePreserving.ae (GW.Analysis.momentumShearWithL2_ae (E := ℂ) (sectorMeasure n) 1 Y),
    ht.quasiMeasurePreserving.ae (sectorFourierReorder_symm_ae n X),
    (hr.comp ht).quasiMeasurePreserving.ae
      (productFunction_ae ((volume : Measure GW.Space).prod (sectorMeasure n)) (volume : Measure GW.Space) U f)]
    with p hS hT hR hP
  change (sectorFourierSplit n).symm Z p = _
  rw [hS]
  calc
    Z (p.1,splitCoordinates n 0 p.2) = Y (p.1+(1:ℝ) • p.2 0,splitCoordinates n 0 p.2) := hT
    _ = X ((p.1+(1:ℝ) • p.2 0,fun i => p.2 ((0 : Fin (n+1)).succAbove i)),p.2 0) := hR
    _ = U (p.1+(1:ℝ) • p.2 0,fun i => p.2 ((0 : Fin (n+1)).succAbove i)) • f (p.2 0) := hP
    _ = _ := by rw [one_smul,smul_eq_mul,mul_comm]


lemma sectorFourier_finite_vector_sum_ae {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (s : Finset I) (v : I → Lp E 2 (volume : Measure GW.Space)) :
    (∑ i ∈ s, v i) =ᵐ[(volume : Measure GW.Space)] fun x => ∑ i ∈ s, v i x := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero E 2 (volume : Measure GW.Space)] with x hx
    exact hx
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (v i) (∑ j ∈ s,v j),ih] with x hx hs
    simp only [Pi.add_apply] at hx
    rw [hx,hs]


lemma sectorFourier_productPermutation_intertwines (n : ℕ) (τ : Equiv.Perm (Fin n))
    (U : Lp (AmbientSector n) 2 (volume : Measure GW.Space)) :
    productUnitary (volume : Measure GW.Space) (sectorMeasure n)
      ((permutationL2 n τ).toContinuousLinearMap.compLp U) =
    productPermutation (volume : Measure GW.Space) n τ
      (productUnitary (volume : Measure GW.Space) (sectorMeasure n) U) :=
  productUnitary_spectator (volume : Measure GW.Space) (sectorMeasure n)
    (coordinatePermutation n τ) (coordinatePermutation_preserving n τ) U

lemma sectorFourier_product_spectator_average (n : ℕ)
    (Z : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure (n+1))))
    (hZ : ∀ h : fixesZero n, productPermutation (volume : Measure GW.Space) (n+1) h Z = Z) :
    productSymmetrizer (volume : Measure GW.Space) (n+1) Z =
      (((n+1 : ℕ) : ℂ)⁻¹) • ∑ j : Fin (n+1),
        productPermutation (volume : Measure GW.Space) (n+1) (swapZero n j) Z := by
  let T := productUnitary (volume : Measure GW.Space) (sectorMeasure (n+1)) (E := ℂ)
  let G := T.symm Z
  have hG (h : fixesZero n) : (permutationL2 (n+1) h).toContinuousLinearMap.compLp G = G := by
    apply T.injective
    rw [sectorFourier_productPermutation_intertwines]
    change productPermutation (volume : Measure GW.Space) (n+1) h (T (T.symm Z)) = T (T.symm Z)
    rw [LinearIsometryEquiv.apply_symm_apply,hZ h]
  have hGa (h : fixesZero n) : ∀ᵐ x ∂(volume : Measure GW.Space), permutationL2 (n+1) h (G x) = G x := by
    have hh := (permutationL2 (n+1) h).toContinuousLinearMap.coeFn_compLp G
    rw [hG h] at hh
    filter_upwards [hh] with x hx
    exact hx.symm
  have hEq : (symmetrizer (n+1)).compLp G =
      (((n+1 : ℕ) : ℂ)⁻¹) • ∑ j : Fin (n+1),
        (permutationL2 (n+1) (swapZero n j)).toContinuousLinearMap.compLp G := by
    apply Lp.ext
    filter_upwards [(symmetrizer (n+1)).coeFn_compLp G,
      Lp.coeFn_smul (((n+1 : ℕ) : ℂ)⁻¹)
        (∑ j : Fin (n+1), (permutationL2 (n+1) (swapZero n j)).toContinuousLinearMap.compLp G),
      sectorFourier_finite_vector_sum_ae Finset.univ
        (fun j : Fin (n+1) => (permutationL2 (n+1) (swapZero n j)).toContinuousLinearMap.compLp G),
      ae_all_iff.mpr (fun j : Fin (n+1) => (permutationL2 (n+1) (swapZero n j)).toContinuousLinearMap.coeFn_compLp G),
      ae_all_iff.mpr hGa] with x hs hc hsum hj hh
    rw [hs,hc,Pi.smul_apply,hsum]
    simp_rw [hj]
    exact symmetrizer_spectator_average n (G x) hh
  change T ((symmetrizer (n+1)).compLp G) = _
  rw [hEq,map_smul,map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hh := sectorFourier_productPermutation_intertwines (n+1) (swapZero n j) G
  change T ((permutationL2 (n+1) (swapZero n j)).toContinuousLinearMap.compLp G) = _ at hh
  change _ = productPermutation (volume : Measure GW.Space) (n+1) (swapZero n j) (T (T.symm Z)) at hh
  rw [LinearIsometryEquiv.apply_symm_apply] at hh
  exact hh



set_option backward.isDefEq.respectTransparency.types false in
lemma sectorFourierRawCreation_fixed (n : ℕ) (f : GW.OnePhonon)
    (U : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure n)))
    (hU : ∀ τ : Equiv.Perm (Fin n), productPermutation (volume : Measure GW.Space) n τ U = U)
    (h : fixesZero n) :
    productPermutation (volume : Measure GW.Space) (n+1) h (sectorFourierRawCreation n f U) =
      sectorFourierRawCreation n f U := by
  let τ := spectatorRestriction n h
  have hu := productPermutation_ae (volume : Measure GW.Space) n τ U
  rw [hU τ] at hu
  let s := MeasurableEquiv.prodCongr (MeasurableEquiv.refl GW.Space) (splitCoordinates n 0)
  have hs : MeasurePreserving s ((volume : Measure GW.Space).prod (sectorMeasure (n+1)))
      ((volume : Measure GW.Space).prod ((volume : Measure GW.Space).prod (sectorMeasure n))) :=
    (MeasurePreserving.id (volume : Measure GW.Space)).prod (splitCoordinates_preserving n 0)
  have ht := (GW.Analysis.momentumShearWith_preserving (sectorMeasure n) 1).comp hs
  have hr := (sectorFourierReorder_preserving n).symm (sectorFourierReorder n)
  have hp := (Measure.quasiMeasurePreserving_fst
    (μ := (volume : Measure GW.Space).prod (sectorMeasure n)) (ν := (volume : Measure GW.Space))).comp
      (hr.comp ht).quasiMeasurePreserving
  have htail := hp.ae hu
  have hc := (MeasurePreserving.id (volume : Measure GW.Space)).prod (coordinatePermutation_preserving (n+1) h)
  apply Lp.ext
  filter_upwards [productPermutation_ae (volume : Measure GW.Space) (n+1) h (sectorFourierRawCreation n f U),
    hc.quasiMeasurePreserving.ae (sectorFourierRawCreation_ae n f U),
    sectorFourierRawCreation_ae n f U,htail] with p hP hC hZ hT
  have hmap : Prod.map id (coordinatePermutation (n+1) h) p =
      (p.1,fun i => p.2 ((h : Equiv.Perm (Fin (n+1))) i)) :=
    Prod.ext rfl (coordinatePermutation_eq (n+1) h p.2)
  rw [hmap] at hC
  rw [hP,hC,hZ]
  have hz : (h : Equiv.Perm (Fin (n+1))) 0 = 0 := h.property
  simp only [coordinatePermutation_apply,hz]
  congr 1
  have he : (fun i : Fin n => p.2 ((h : Equiv.Perm (Fin (n+1))) ((0 : Fin (n+1)).succAbove i))) =
      fun i => p.2 ((0 : Fin (n+1)).succAbove (τ i)) := by
    funext i
    simp only [τ,Fin.zero_succAbove,spectatorRestriction_apply]
  rw [he]
  change U (p.1+(1:ℝ) • p.2 0,fun i => p.2 ((0 : Fin (n+1)).succAbove i)) =
    U (p.1+(1:ℝ) • p.2 0,fun i => p.2 ((0 : Fin (n+1)).succAbove (τ i))) at hT
  simpa only [one_smul] using hT.symm



set_option backward.isDefEq.respectTransparency.types false in
lemma sectorFourier_shifted_spectator_invariance (n : ℕ) (j : Fin (n+1)) (τ : Equiv.Perm (Fin n))
    (U : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure n)))
    (hU : productPermutation (volume : Measure GW.Space) n τ U = U) :
    ∀ᵐ p ∂((volume : Measure GW.Space).prod (sectorMeasure (n+1))),
      U (p.1+p.2 j,fun i => p.2 (j.succAbove (τ i))) = U (p.1+p.2 j,fun i => p.2 (j.succAbove i)) := by
  have hu := productPermutation_ae (volume : Measure GW.Space) n τ U
  rw [hU] at hu
  let s := MeasurableEquiv.prodCongr (MeasurableEquiv.refl GW.Space) (splitCoordinates n j)
  have hs : MeasurePreserving s ((volume : Measure GW.Space).prod (sectorMeasure (n+1)))
      ((volume : Measure GW.Space).prod ((volume : Measure GW.Space).prod (sectorMeasure n))) :=
    (MeasurePreserving.id (volume : Measure GW.Space)).prod (splitCoordinates_preserving n j)
  have ht := (GW.Analysis.momentumShearWith_preserving (sectorMeasure n) 1).comp hs
  have hr := (sectorFourierReorder_preserving n).symm (sectorFourierReorder n)
  have hp := (Measure.quasiMeasurePreserving_fst
    (μ := (volume : Measure GW.Space).prod (sectorMeasure n)) (ν := (volume : Measure GW.Space))).comp
      (hr.comp ht).quasiMeasurePreserving
  filter_upwards [hp.ae hu] with p hP
  change U (p.1+(1:ℝ) • p.2 j,fun i => p.2 (j.succAbove i)) =
    U (p.1+(1:ℝ) • p.2 j,fun i => p.2 (j.succAbove (τ i))) at hP
  simpa only [one_smul] using hP.symm

set_option backward.isDefEq.respectTransparency.types false in
lemma sectorFourierRawCreation_swap_ae (n : ℕ) (j : Fin (n+1)) (f : GW.OnePhonon)
    (U : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure n)))
    (hU : ∀ τ : Equiv.Perm (Fin n), productPermutation (volume : Measure GW.Space) n τ U = U) :
    productPermutation (volume : Measure GW.Space) (n+1) (swapZero n j) (sectorFourierRawCreation n f U) =ᵐ[
      (volume : Measure GW.Space).prod (sectorMeasure (n+1))]
      fun p => f (p.2 j)*U (p.1+p.2 j,fun i => p.2 (j.succAbove i)) := by
  let τ := swapSpectatorOrder n j
  have hc := (MeasurePreserving.id (volume : Measure GW.Space)).prod
    (coordinatePermutation_preserving (n+1) (swapZero n j))
  filter_upwards [productPermutation_ae (volume : Measure GW.Space) (n+1) (swapZero n j)
      (sectorFourierRawCreation n f U),
    hc.quasiMeasurePreserving.ae (sectorFourierRawCreation_ae n f U),
    sectorFourier_shifted_spectator_invariance n j τ U (hU τ)] with p hP hC hU
  have hmap : Prod.map id (coordinatePermutation (n+1) (swapZero n j)) p =
      (p.1,fun i => p.2 (swapZero n j i)) :=
    Prod.ext rfl (coordinatePermutation_eq (n+1) (swapZero n j) p.2)
  rw [hmap] at hC
  rw [hP,hC]
  simp only [coordinatePermutation_apply,swapZero_zero]
  congr 1
  have he : (fun i : Fin n => p.2 (swapZero n j ((0 : Fin (n+1)).succAbove i))) =
      fun i => p.2 (j.succAbove (τ i)) := by
    funext i
    simp only [τ,Fin.zero_succAbove,swapSpectatorOrder_apply]
  rw [he]
  exact hU

def sectorFourierCreationExpression (n : ℕ) (f : GW.OnePhonon)
    (U : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure n))) :
    Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure (n+1))) :=
  (Real.sqrt (n+1 : ℕ) : ℂ) • productSymmetrizer (volume : Measure GW.Space) (n+1)
    (sectorFourierRawCreation n f U)

lemma sectorFourierCreationExpression_sum (n : ℕ) (f : GW.OnePhonon)
    (U : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure n)))
    (hU : ∀ τ : Equiv.Perm (Fin n), productPermutation (volume : Measure GW.Space) n τ U = U) :
    sectorFourierCreationExpression n f U = (Real.sqrt (n+1 : ℕ) : ℂ)⁻¹ •
      ∑ j : Fin (n+1), productPermutation (volume : Measure GW.Space) (n+1) (swapZero n j)
        (sectorFourierRawCreation n f U) := by
  unfold sectorFourierCreationExpression
  rw [sectorFourier_product_spectator_average n _ (sectorFourierRawCreation_fixed n f U hU),smul_smul]
  congr 1
  have h := congrArg (fun r : ℝ => (r : ℂ)) (creation_sqrt_coefficient n)
  push_cast at h
  simpa only [Nat.cast_add,Nat.cast_one] using h

lemma sectorFourierCreationExpression_ae (n : ℕ) (f : GW.OnePhonon)
    (U : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure n)))
    (hU : ∀ τ : Equiv.Perm (Fin n), productPermutation (volume : Measure GW.Space) n τ U = U) :
    sectorFourierCreationExpression n f U =ᵐ[(volume : Measure GW.Space).prod (sectorMeasure (n+1))]
      fun p => (Real.sqrt (n+1 : ℕ) : ℂ)⁻¹ * ∑ j : Fin (n+1),
        f (p.2 j)*U (p.1+p.2 j,fun i => p.2 (j.succAbove i)) := by
  rw [sectorFourierCreationExpression_sum n f U hU]
  filter_upwards [Lp.coeFn_smul (Real.sqrt (n+1 : ℕ) : ℂ)⁻¹
      (∑ j : Fin (n+1), productPermutation (volume : Measure GW.Space) (n+1) (swapZero n j)
        (sectorFourierRawCreation n f U)),
    finite_lp_sum_ae ((volume : Measure GW.Space).prod (sectorMeasure (n+1))) Finset.univ
      (fun j : Fin (n+1) => productPermutation (volume : Measure GW.Space) (n+1) (swapZero n j)
        (sectorFourierRawCreation n f U)),
    ae_all_iff.mpr (fun j : Fin (n+1) => sectorFourierRawCreation_swap_ae n j f U hU)] with p hs hsum hj
  rw [hs,Pi.smul_apply,hsum,smul_eq_mul]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => hj j)

lemma sectorFourierProductSymmetrizer_norm (n : ℕ)
    (U : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure n))) :
    ‖productSymmetrizer (volume : Measure GW.Space) n U‖ ≤ ‖U‖ := by
  let T := productUnitary (volume : Measure GW.Space) (sectorMeasure n) (E := ℂ)
  change ‖T ((symmetrizer n).compLp (T.symm U))‖ ≤ ‖U‖
  rw [LinearIsometryEquiv.norm_map]
  have hh : ‖(symmetrizer n).compLp (T.symm U)‖ ≤ 1*‖T.symm U‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [(symmetrizer n).coeFn_compLp (T.symm U)] with x hx
    rw [hx,one_mul]
    exact symmetrizer_norm_le n _
  simpa only [one_mul,LinearIsometryEquiv.norm_map] using hh

lemma sectorFourierCreationExpression_bound (n : ℕ) (f : GW.OnePhonon)
    (U : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure n))) :
    ‖sectorFourierCreationExpression n f U‖ ≤ Real.sqrt (n+1 : ℕ)*‖f‖*‖U‖ := by
  change ‖(Real.sqrt (n+1 : ℕ) : ℂ) • productSymmetrizer (volume : Measure GW.Space) (n+1)
    (sectorFourierRawCreation n f U)‖ ≤ _
  rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ Real.sqrt (n+1 : ℕ)*‖sectorFourierRawCreation n f U‖ :=
      mul_le_mul_of_nonneg_left (sectorFourierProductSymmetrizer_norm (n+1) _) (Real.sqrt_nonneg _)
    _ = _ := by rw [sectorFourierRawCreation_norm,mul_assoc]


end GW.Fock

-- Compiled component Transport02
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal
namespace GW.Fock
open GW.Analysis

def sectorFourierElectronMap : ElectronL2 →L[ℂ] ElectronL2 :=
  (physicalFourierUnitary (H := ℂ)).toContinuousLinearEquiv.toContinuousLinearMap

lemma sectorElectronFourier_tensor (n : ℕ) (γ : ElectronL2) (v : AmbientSector n) :
    sectorElectronFourier n (productFunction volume (sectorMeasure n) γ v) =
      productFunction volume (sectorMeasure n) (physicalFourierUnitary γ) v := by
  change productUnitary volume (sectorMeasure n)
    (physicalFourierUnitary ((productUnitary volume (sectorMeasure n)).symm
      (productFunction volume (sectorMeasure n) γ v))) = _
  rw [← productUnitary_tensor,LinearIsometryEquiv.symm_apply_apply,tensorEmbedding_apply,
    smoothProduct_fourier_postcomp,← tensorEmbedding_apply,productUnitary_tensor]

lemma sectorElectronFourier_kernel_tensor (n : ℕ) (γ : ElectronL2) (v : AmbientSector n) :
    physicalKernelProduct n (sectorElectronFourier n (productFunction volume (sectorMeasure n) γ v)) =
      amplify (sectorMeasure n) sectorFourierElectronMap
        (physicalKernelProduct n (productFunction volume (sectorMeasure n) γ v)) := by
  have h₁ := fiberPhysicalKernelProduct_tensor n (physicalFourierUnitary γ) v
  have h₂ := congrArg (amplify (sectorMeasure n) sectorFourierElectronMap)
    (fiberPhysicalKernelProduct_tensor n γ v)
  have h₃ := amplify_tensor (sectorMeasure n) sectorFourierElectronMap v γ
  exact (congrArg (physicalKernelProduct n) (sectorElectronFourier_tensor n γ v)).trans
    (h₁.trans (h₃.symm.trans h₂.symm))

lemma sectorElectronFourier_kernel_product (n : ℕ)
    (u : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure n))) :
    physicalKernelProduct n (sectorElectronFourier n u) =
      amplify (sectorMeasure n) sectorFourierElectronMap
        (physicalKernelProduct n u) := by
  let A := (physicalKernelProduct n).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (sectorElectronFourier n).toContinuousLinearEquiv.toContinuousLinearMap
  let B := (amplify (sectorMeasure n) sectorFourierElectronMap).comp
    (physicalKernelProduct n).toContinuousLinearEquiv.toContinuousLinearMap
  have he : A = B := by
    apply product_map_ext (volume : Measure GW.Space) (sectorMeasure n)
    intro S T hS hT hSf hTf e
    have h := sectorElectronFourier_kernel_tensor n (indicatorConstLp 2 hS hSf (1:ℂ))
      (indicatorConstLp 2 hT hTf e)
    change A (productFunction volume (sectorMeasure n) (indicatorConstLp 2 hS hSf (1:ℂ))
      (indicatorConstLp 2 hT hTf e)) = B (productFunction volume (sectorMeasure n)
        (indicatorConstLp 2 hS hSf (1:ℂ)) (indicatorConstLp 2 hT hTf e)) at h
    simpa only [productFunction_indicator] using h
  exact congrArg (fun L => L u) he

lemma sectorFourier_phase_kernel (f : OneBoson) (γ : ElectronL2) :
    kernelProductIdentification
      (amplify (volume : Measure GW.Space)
        sectorFourierElectronMap (phaseMultiplicationKernel f γ)) =
      frankSchleinShearedFourier f γ :=
  frankSchlein_phaseKernel_fourier f γ

end GW.Fock

-- Compiled component Kernel02
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Fock

section KernelCovariance
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

lemma sectorFourier_kernelCreation_postcomp (F : BosonKernel E) (T : E →L[ℂ] E)
    (n : ℕ) (u : KernelSector E n) :
    kernelCreationRaw ((amplify (volume : Measure GW.Space) T).comp F) n u =
      amplify (sectorMeasure (n+1)) T (kernelCreationRaw F n u) := by
  apply (kernelSplit (E := E) n).injective
  have h₁ : kernelSplit n (kernelCreationRaw ((amplify (volume : Measure GW.Space) T).comp F) n u) =
      amplify (sectorMeasure n) ((amplify (volume : Measure GW.Space) T).comp F) u :=
    (kernelSplit (E := E) n).apply_symm_apply _
  have h₂ : kernelSplit n (kernelCreationRaw F n u) = amplify (sectorMeasure n) F u :=
    (kernelSplit (E := E) n).apply_symm_apply _
  have h₃ := frankSchlein_kernelSplit_natural T n (kernelCreationRaw F n u)
  exact h₁.trans ((frankSchlein_amplify_comp (sectorMeasure n)
    (amplify (volume : Measure GW.Space) T) F u).trans
      ((congrArg (amplify (sectorMeasure n) (amplify (volume : Measure GW.Space) T)) h₂.symm).trans h₃.symm))

lemma sectorFourier_kernelCreation_precomp (F : BosonKernel E) (T : E →L[ℂ] E)
    (n : ℕ) (u : KernelSector E n) :
    kernelCreationRaw (F.comp T) n u = kernelCreationRaw F n (amplify (sectorMeasure n) T u) :=
  congrArg (kernelSplit (E := E) n).symm (frankSchlein_amplify_comp (sectorMeasure n) F T u)

lemma sectorFourier_kernelSymmetrizer_postcomp (T : E →L[ℂ] E) (n : ℕ) (u : KernelSector E n) :
    amplify (sectorMeasure n) T (kernelSymmetrizer n u) =
      kernelSymmetrizer n (amplify (sectorMeasure n) T u) := by
  rw [fiberKernelSymmetrizer_average,fiberKernelSymmetrizer_average,map_smul,map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro τ _
  exact (vectorPullback_amplify (coordinatePermutation n τ) (coordinatePermutation_preserving n τ) T u).symm

def sectorFourierConjugateKernel (U : E ≃ₗᵢ[ℂ] E) (F : BosonKernel E) : BosonKernel E :=
  (amplify (volume : Measure GW.Space) U.toContinuousLinearEquiv.toContinuousLinearMap).comp
    (F.comp U.symm.toContinuousLinearEquiv.toContinuousLinearMap)

lemma sectorFourier_amplify_inverse {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (U : E ≃ₗᵢ[ℂ] E) (u : Lp E 2 μ) :
    amplify μ U.symm.toContinuousLinearEquiv.toContinuousLinearMap
      (amplify μ U.toContinuousLinearEquiv.toContinuousLinearMap u) = u := by
  apply Lp.ext
  filter_upwards [amplify_ae μ U.symm.toContinuousLinearEquiv.toContinuousLinearMap
      (amplify μ U.toContinuousLinearEquiv.toContinuousLinearMap u),
    amplify_ae μ U.toContinuousLinearEquiv.toContinuousLinearMap u] with x h₁ h₂
  rw [h₁,h₂]
  exact U.symm_apply_apply (u x)

lemma sectorFourier_kernelCreation_covariance (U : E ≃ₗᵢ[ℂ] E) (F : BosonKernel E)
    (n : ℕ) (u : KernelSector E n) :
    kernelCreationRaw (sectorFourierConjugateKernel U F) n
      (amplify (sectorMeasure n) U.toContinuousLinearEquiv.toContinuousLinearMap u) =
    amplify (sectorMeasure (n+1)) U.toContinuousLinearEquiv.toContinuousLinearMap (kernelCreationRaw F n u) := by
  rw [sectorFourierConjugateKernel,sectorFourier_kernelCreation_postcomp,
    sectorFourier_kernelCreation_precomp,sectorFourier_amplify_inverse]

lemma sectorFourier_fixedCreation_covariance (U : E ≃ₗᵢ[ℂ] E) (F : BosonKernel E)
    (n : ℕ) (u : kernelFixed (E := E) n) :
    kernelCreation (sectorFourierConjugateKernel U F) n
      (frankSchleinFixedAmplify U.toContinuousLinearEquiv.toContinuousLinearMap n u) =
    frankSchleinFixedAmplify U.toContinuousLinearEquiv.toContinuousLinearMap (n+1) (kernelCreation F n u) := by
  apply Subtype.ext
  change (Real.sqrt (n+1 : ℕ) : ℂ) • kernelSymmetrizer (n+1)
    (kernelCreationRaw (sectorFourierConjugateKernel U F) n
      (amplify (sectorMeasure n) U.toContinuousLinearEquiv.toContinuousLinearMap u.val)) =
    amplify (sectorMeasure (n+1)) U.toContinuousLinearEquiv.toContinuousLinearMap
      ((Real.sqrt (n+1 : ℕ) : ℂ) • kernelSymmetrizer (n+1) (kernelCreationRaw F n u.val))
  rw [sectorFourier_kernelCreation_covariance,map_smul,sectorFourier_kernelSymmetrizer_postcomp]

end KernelCovariance
end GW.Fock

-- Compiled component Insert01
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Fock
open GW.Analysis

def sectorFourierInsertEquiv (n : ℕ) :
    GW.Space × Coordinates (n+1) ≃ᵐ (GW.Space × GW.Space) × Coordinates n :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl GW.Space) (splitCoordinates n 0)).trans
    (MeasurableEquiv.prodAssoc : (GW.Space × GW.Space) × Coordinates n ≃ᵐ GW.Space × (GW.Space × Coordinates n)).symm

lemma sectorFourierInsertEquiv_preserving (n : ℕ) :
    MeasurePreserving (sectorFourierInsertEquiv n)
      ((volume : Measure GW.Space).prod (sectorMeasure (n+1)))
      (((volume : Measure GW.Space).prod volume).prod (sectorMeasure n)) := by
  exact ((measurePreserving_prodAssoc (volume : Measure GW.Space) volume (sectorMeasure n)).symm
    (MeasurableEquiv.prodAssoc : (GW.Space × GW.Space) × Coordinates n ≃ᵐ GW.Space × (GW.Space × Coordinates n))).comp
    ((MeasurePreserving.id (volume : Measure GW.Space)).prod (splitCoordinates_preserving n 0))

def sectorFourierInsert (n : ℕ) (v : AmbientSector n) :
    ElectronBosonProduct →L[ℂ] Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure (n+1))) :=
  (vectorPullback (sectorFourierInsertEquiv n) (sectorFourierInsertEquiv_preserving n)).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (productFunctionMap ((volume : Measure GW.Space).prod volume) (sectorMeasure n) v)

lemma sectorFourierInsert_ae (n : ℕ) (v : AmbientSector n) (Φ : ElectronBosonProduct) :
    sectorFourierInsert n v Φ =ᵐ[(volume : Measure GW.Space).prod (sectorMeasure (n+1))]
      fun p => Φ (p.1,p.2 0)*v (fun i => p.2 i.succ) := by
  filter_upwards [vectorPullback_ae (sectorFourierInsertEquiv n) (sectorFourierInsertEquiv_preserving n)
      (productFunction ((volume : Measure GW.Space).prod volume) (sectorMeasure n) Φ v),
    (sectorFourierInsertEquiv_preserving n).quasiMeasurePreserving.ae
      (productFunction_ae ((volume : Measure GW.Space).prod volume) (sectorMeasure n) Φ v)] with p h₁ h₂
  change vectorPullback (sectorFourierInsertEquiv n) (sectorFourierInsertEquiv_preserving n)
    (productFunction ((volume : Measure GW.Space).prod volume) (sectorMeasure n) Φ v) p = _
  rw [h₁]
  exact h₂

lemma sectorFourierInsert_tensor (n : ℕ) (v : AmbientSector n) (γ h : OneBoson) :
    sectorFourierInsert n v (productFunction volume volume γ h) =
      productFunction volume (sectorMeasure (n+1)) γ (prependProduct n h v) := by
  have hp := (Measure.quasiMeasurePreserving_fst
    (μ := (volume : Measure GW.Space).prod volume) (ν := sectorMeasure n)).comp
      (sectorFourierInsertEquiv_preserving n).quasiMeasurePreserving
  apply Lp.ext
  filter_upwards [sectorFourierInsert_ae n v (productFunction volume volume γ h),
    hp.ae (productFunction_ae (volume : Measure GW.Space) volume γ h),
    productFunction_ae (volume : Measure GW.Space) (sectorMeasure (n+1)) γ (prependProduct n h v),
    (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure GW.Space)) (ν := sectorMeasure (n+1))).ae
      (prependProduct_ae n h v)] with p hI hP hT hV
  rw [hI,hT,hV]
  change productFunction volume volume γ h (p.1,p.2 0) = γ p.1 • h (p.2 0) at hP
  rw [hP]
  simp only [smul_eq_mul]
  ring

end GW.Fock

-- Compiled component InsertKernel01
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Fock

lemma sectorFourierInsert_kernel_tensor (n : ℕ) (v : AmbientSector n) (γ h : OneBoson) :
    physicalKernelProduct (n+1) (sectorFourierInsert n v (productFunction volume volume γ h)) =
      (kernelSplit (E := ElectronL2) n).symm
        (tensorEmbedding (sectorMeasure n) v
          (kernelProductIdentification.symm (productFunction volume volume γ h))) := by
  have hi : kernelProductIdentification.symm (productFunction volume volume γ h) = tensorEmbedding volume h γ := by
    apply kernelProductIdentification.injective
    exact (kernelProductIdentification.apply_symm_apply _).trans (fiberKernel_tensor_product h γ).symm
  have h₁ := congrArg (physicalKernelProduct (n+1)) (sectorFourierInsert_tensor n v γ h)
  have h₂ := fiberPhysicalKernelProduct_tensor (n+1) γ (prependProduct n h v)
  have h₃ : tensorEmbedding (sectorMeasure (n+1)) (prependProduct n h v) γ =
      (kernelSplit (E := ElectronL2) n).symm (tensorEmbedding (sectorMeasure n) v (tensorEmbedding volume h γ)) := by
    have hs := congrArg (kernelSplit (E := ElectronL2) n).symm (fiberKernelSplit_prepend_tensor n h v γ)
    simpa only [LinearIsometryEquiv.symm_apply_apply] using hs
  have h₄ := congrArg (fun c : Lp ElectronL2 2 (volume : Measure GW.Space) =>
    (kernelSplit (E := ElectronL2) n).symm (tensorEmbedding (sectorMeasure n) v c)) hi
  exact h₁.trans (h₂.trans (h₃.trans h₄.symm))

lemma sectorFourierInsert_kernel (n : ℕ) (v : AmbientSector n) (Φ : ElectronBosonProduct) :
    physicalKernelProduct (n+1) (sectorFourierInsert n v Φ) =
      (kernelSplit (E := ElectronL2) n).symm
        (tensorEmbedding (sectorMeasure n) v (kernelProductIdentification.symm Φ)) := by
  let A := (physicalKernelProduct (n+1)).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (sectorFourierInsert n v)
  let B := (kernelSplit (E := ElectronL2) n).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((tensorEmbedding (E := Lp ElectronL2 2 (volume : Measure GW.Space)) (sectorMeasure n) v).comp
      kernelProductIdentification.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  have he : A = B := by
    apply product_map_ext (volume : Measure GW.Space) (volume : Measure GW.Space)
    intro S T hS hT hSf hTf e
    have h := sectorFourierInsert_kernel_tensor n v (indicatorConstLp 2 hS hSf (1:ℂ))
      (indicatorConstLp 2 hT hTf e)
    change A (productFunction volume volume (indicatorConstLp 2 hS hSf (1:ℂ)) (indicatorConstLp 2 hT hTf e)) =
      B (productFunction volume volume (indicatorConstLp 2 hS hSf (1:ℂ)) (indicatorConstLp 2 hT hTf e)) at h
    simpa only [productFunction_indicator] using h
  exact congrArg (fun L => L Φ) he

end GW.Fock

-- Compiled component RawIdentification02
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Fock
open GW.Analysis

def sectorFourierPhaseKernel (f : OneBoson) : BosonKernel ElectronL2 :=
  sectorFourierConjugateKernel (physicalFourierUnitary (H := ℂ)) (phaseMultiplicationKernel f)
def sectorFourierSingleExpression (f : OneBoson) (γ : ElectronL2) : ElectronBosonProduct :=
  frankSchleinShearedFourier f (physicalFourierUnitary.symm γ)
lemma sectorFourierPhaseKernel_product (f : OneBoson) (γ : ElectronL2) :
    kernelProductIdentification (sectorFourierPhaseKernel f γ) = sectorFourierSingleExpression f γ :=
  frankSchlein_phaseKernel_fourier f (physicalFourierUnitary.symm γ)
lemma sectorFourierSingleExpression_ae (f : OneBoson) (γ : ElectronL2) :
    sectorFourierSingleExpression f γ =ᵐ[(volume : Measure GW.Space).prod volume]
      fun p => f p.2*γ (p.1+p.2) := by
  have h := frankSchleinShearedFourier_ae f (physicalFourierUnitary.symm γ)
  simpa only [sectorFourierSingleExpression,LinearIsometryEquiv.apply_symm_apply] using h

lemma sectorFourierRawCreation_tensor_insert (n : ℕ) (f : OneBoson) (γ : ElectronL2) (v : AmbientSector n) :
    sectorFourierRawCreation n f (productFunction volume (sectorMeasure n) γ v) =
      sectorFourierInsert n v (sectorFourierSingleExpression f γ) := by
  let s := MeasurableEquiv.prodCongr (MeasurableEquiv.refl GW.Space) (splitCoordinates n 0)
  have hs : MeasurePreserving s ((volume : Measure GW.Space).prod (sectorMeasure (n+1)))
      ((volume : Measure GW.Space).prod ((volume : Measure GW.Space).prod (sectorMeasure n))) :=
    (MeasurePreserving.id (volume : Measure GW.Space)).prod (splitCoordinates_preserving n 0)
  have ht := (momentumShearWith_preserving (sectorMeasure n) 1).comp hs
  have hr := (sectorFourierReorder_preserving n).symm (sectorFourierReorder n)
  have hp := (Measure.quasiMeasurePreserving_fst
    (μ := (volume : Measure GW.Space).prod (sectorMeasure n)) (ν := (volume : Measure GW.Space))).comp
    (hr.comp ht).quasiMeasurePreserving
  have hΦ := (Measure.quasiMeasurePreserving_fst
    (μ := (volume : Measure GW.Space).prod volume) (ν := sectorMeasure n)).comp
    (sectorFourierInsertEquiv_preserving n).quasiMeasurePreserving
  apply Lp.ext
  filter_upwards [sectorFourierRawCreation_ae n f (productFunction volume (sectorMeasure n) γ v),
    sectorFourierInsert_ae n v (sectorFourierSingleExpression f γ),
    hp.ae (productFunction_ae (volume : Measure GW.Space) (sectorMeasure n) γ v),
    hΦ.ae (sectorFourierSingleExpression_ae f γ)] with p hR hI hP hS
  change productFunction volume (sectorMeasure n) γ v
      (p.1+(1:ℝ) • p.2 0,fun i => p.2 ((0 : Fin (n+1)).succAbove i)) =
    γ (p.1+(1:ℝ) • p.2 0) • v (fun i => p.2 ((0 : Fin (n+1)).succAbove i)) at hP
  change sectorFourierSingleExpression f γ (p.1,p.2 0) = f (p.2 0)*γ (p.1+p.2 0) at hS
  simp only [one_smul,Fin.zero_succAbove,smul_eq_mul] at hP hR
  rw [hR,hI,hP,hS]
  ring

lemma sectorFourierRawCreation_kernel_tensor (n : ℕ) (f : OneBoson) (γ : ElectronL2) (v : AmbientSector n) :
    physicalKernelProduct (n+1) (sectorFourierRawCreation n f (productFunction volume (sectorMeasure n) γ v)) =
      kernelCreationRaw (sectorFourierPhaseKernel f) n (physicalKernelProduct n (productFunction volume (sectorMeasure n) γ v)) := by
  have hi : kernelProductIdentification.symm (sectorFourierSingleExpression f γ) = sectorFourierPhaseKernel f γ :=
    (congrArg kernelProductIdentification.symm (sectorFourierPhaseKernel_product f γ)).symm.trans
      (kernelProductIdentification.symm_apply_apply _)
  have h₁ := congrArg (physicalKernelProduct (n+1)) (sectorFourierRawCreation_tensor_insert n f γ v)
  have h₂ := sectorFourierInsert_kernel n v (sectorFourierSingleExpression f γ)
  have h₃ := congrArg (fun c : Lp ElectronL2 2 (volume : Measure GW.Space) =>
    (kernelSplit (E := ElectronL2) n).symm (tensorEmbedding (sectorMeasure n) v c)) hi
  have h₄ : (kernelSplit (E := ElectronL2) n).symm (tensorEmbedding (sectorMeasure n) v (sectorFourierPhaseKernel f γ)) =
      kernelCreationRaw (sectorFourierPhaseKernel f) n (tensorEmbedding (sectorMeasure n) v γ) :=
    (congrArg (kernelSplit (E := ElectronL2) n).symm
      (amplify_tensor (sectorMeasure n) (sectorFourierPhaseKernel f) v γ)).symm
  have h₅ := congrArg (kernelCreationRaw (sectorFourierPhaseKernel f) n) (fiberPhysicalKernelProduct_tensor n γ v).symm
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

lemma sectorFourierRawCreation_kernel (n : ℕ) (f : OneBoson)
    (u : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure n))) :
    physicalKernelProduct (n+1) (sectorFourierRawCreation n f u) =
      kernelCreationRaw (sectorFourierPhaseKernel f) n (physicalKernelProduct n u) := by
  let A := (physicalKernelProduct (n+1)).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (sectorFourierRawCreation n f)
  let B := (kernelCreationRaw (sectorFourierPhaseKernel f) n).comp
    (physicalKernelProduct n).toContinuousLinearEquiv.toContinuousLinearMap
  have he : A = B := by
    apply product_map_ext (volume : Measure GW.Space) (sectorMeasure n)
    intro S T hS hT hSf hTf e
    have h := sectorFourierRawCreation_kernel_tensor n f (indicatorConstLp 2 hS hSf (1:ℂ))
      (indicatorConstLp 2 hT hTf e)
    change A (productFunction volume (sectorMeasure n) (indicatorConstLp 2 hS hSf (1:ℂ)) (indicatorConstLp 2 hT hTf e)) =
      B (productFunction volume (sectorMeasure n) (indicatorConstLp 2 hS hSf (1:ℂ)) (indicatorConstLp 2 hT hTf e)) at h
    simpa only [productFunction_indicator] using h
  exact congrArg (fun L => L u) he

end GW.Fock

-- Compiled component Physical02
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Fock
open GW.Analysis

lemma sectorFourier_fixedInclusion_value {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (n : ℕ) (u : kernelFixed (E := E) n) :
    (kernelFixedInclusion (E := E) n).toContinuousLinearMap u = (u : KernelSector E n) := rfl

def sectorFourierSectorInclusion (n : ℕ) : Sector n →L[ℂ] AmbientSector n :=
  (kernelFixedInclusion (E := ℂ) n).toContinuousLinearMap.comp
    (ordinarySectorKernel n).toContinuousLinearEquiv.toContinuousLinearMap

def sectorFourierProductMap (n : ℕ) : ElectronSector n →L[ℂ]
    Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure n)) :=
  (productUnitary (E := ℂ) (volume : Measure GW.Space) (sectorMeasure n)).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (amplify (volume : Measure GW.Space) (sectorFourierSectorInclusion n))

lemma sectorFourierProductMap_tensor (n : ℕ) (γ : ElectronL2) (v : Sector n) :
    sectorFourierProductMap n (tensorEmbedding volume γ v) =
      productFunction volume (sectorMeasure n) γ (sectorFourierSectorInclusion n v) := by
  change productUnitary volume (sectorMeasure n) (amplify volume (sectorFourierSectorInclusion n) (tensorEmbedding volume γ v)) = _
  rw [amplify_tensor,productUnitary_tensor]

lemma sectorFourierProductMap_kernel_tensor (n : ℕ) (γ : ElectronL2) (v : Sector n) :
    physicalKernelProduct n (sectorFourierProductMap n (tensorEmbedding volume γ v)) =
      (physicalSectorKernel n (tensorEmbedding volume γ v) : KernelSector ElectronL2 n) := by
  have h₁ := congrArg (physicalKernelProduct n) (sectorFourierProductMap_tensor n γ v)
  have h₂ := fiberPhysicalKernelProduct_tensor n γ (sectorFourierSectorInclusion n v)
  have h₃ := fiberPhysicalSectorKernel_tensor n γ v
  exact h₁.trans (h₂.trans h₃.symm)

lemma sectorFourierProductMap_kernel (n : ℕ) (u : ElectronSector n) :
    physicalKernelProduct n (sectorFourierProductMap n u) = (physicalSectorKernel n u : KernelSector ElectronL2 n) := by
  let A := (physicalKernelProduct n).toContinuousLinearEquiv.toContinuousLinearMap.comp (sectorFourierProductMap n)
  let B := (kernelFixedInclusion (E := ElectronL2) n).toContinuousLinearMap.comp
    (physicalSectorKernel n).toContinuousLinearEquiv.toContinuousLinearMap
  change A u = B u
  apply Lp.induction (p := 2) (μ := (volume : Measure GW.Space)) (by norm_num)
    (fun u => A u = B u) ?_ ?_ (isClosed_eq A.continuous B.continuous) u
  · intro v S hS hfinite
    have h := sectorFourierProductMap_kernel_tensor n (indicatorConstLp 2 hS hfinite.ne (1:ℂ)) v
    simpa only [A,B,ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe,sectorFourier_fixedInclusion_value,tensorEmbedding_apply,compLp_indicatorConst,
      ContinuousLinearMap.toSpanSingleton_apply,one_smul,Lp.simpleFunc.coe_indicatorConst] using h
  · intro f g hfm hgm _ hf hg
    exact (A.map_add (hfm.toLp f) (hgm.toLp g)).trans
      ((congrArg₂ (fun x y => x+y) hf hg).trans (B.map_add (hfm.toLp f) (hgm.toLp g)).symm)

lemma sectorFourierProductMap_fourier (n : ℕ) (u : ElectronSector n) :
    sectorElectronFourier n (sectorFourierProductMap n u) =
      sectorFourierProductMap n (physicalFourierUnitary u) := by
  let P := productUnitary (E := ℂ) (volume : Measure GW.Space) (sectorMeasure n)
  change P (physicalFourierUnitary (P.symm (P ((sectorFourierSectorInclusion n).compLp u)))) =
    P ((sectorFourierSectorInclusion n).compLp (physicalFourierUnitary u))
  rw [LinearIsometryEquiv.symm_apply_apply]
  exact congrArg P (smoothProduct_fourier_postcomp (sectorFourierSectorInclusion n) u)

lemma sectorFourier_physical (n : ℕ) (u : ElectronSector n) :
    physicalSectorKernel n (physicalFourierUnitary u) =
      frankSchleinFixedAmplify sectorFourierElectronMap n (physicalSectorKernel n u) := by
  apply Subtype.ext
  change (physicalSectorKernel n (physicalFourierUnitary u) : KernelSector ElectronL2 n) =
    amplify (sectorMeasure n) sectorFourierElectronMap (physicalSectorKernel n u : KernelSector ElectronL2 n)
  have h₁ := (sectorFourierProductMap_kernel n (physicalFourierUnitary u)).symm
  have h₂ := congrArg (physicalKernelProduct n) (sectorFourierProductMap_fourier n u).symm
  have h₃ := sectorElectronFourier_kernel_product n (sectorFourierProductMap n u)
  have h₄ := congrArg (amplify (sectorMeasure n) sectorFourierElectronMap) (sectorFourierProductMap_kernel n u)
  exact h₁.trans (h₂.trans (h₃.trans h₄))

lemma sectorFourierCreationExpression_kernel (n : ℕ) (f : OneBoson)
    (u : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure n))) :
    physicalKernelProduct (n+1) (sectorFourierCreationExpression n f u) =
      (Real.sqrt (n+1 : ℕ) : ℂ) • kernelSymmetrizer (n+1)
        (kernelCreationRaw (sectorFourierPhaseKernel f) n (physicalKernelProduct n u)) := by
  have h₁ := (physicalKernelProduct (n+1)).map_smul (Real.sqrt (n+1 : ℕ) : ℂ)
    (productSymmetrizer volume (n+1) (sectorFourierRawCreation n f u))
  have h₂ := congrArg (fun z : KernelSector ElectronL2 (n+1) => (Real.sqrt (n+1 : ℕ) : ℂ) • z)
    (fiberPhysicalKernelProduct_symmetrizer (n+1) (sectorFourierRawCreation n f u))
  have h₃ := congrArg (fun z : KernelSector ElectronL2 (n+1) =>
      (Real.sqrt (n+1 : ℕ) : ℂ) • kernelSymmetrizer (n+1) z) (sectorFourierRawCreation_kernel n f u)
  exact h₁.trans (h₂.trans h₃)

end GW.Fock

-- Compiled component CreationIdentification01
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Fock
open GW.Analysis

lemma sectorFourier_creation_identification (n : ℕ) (f : OneBoson) (u : ElectronSector n) :
    sectorFourierProductMap (n+1) (physicalFourierUnitary (generalizedCreationSector (phaseMultiplicationKernel f) n u)) =
      sectorFourierCreationExpression n f (sectorFourierProductMap n (physicalFourierUnitary u)) := by
  apply (physicalKernelProduct (n+1)).injective
  let z := frankSchleinFixedAmplify sectorFourierElectronMap n (physicalSectorKernel n u)
  have hz : physicalKernelProduct n (sectorFourierProductMap n (physicalFourierUnitary u)) =
      (z : KernelSector ElectronL2 n) :=
    (sectorFourierProductMap_kernel n (physicalFourierUnitary u)).trans
      (congrArg (fun v : kernelFixed (E := ElectronL2) n => (v : KernelSector ElectronL2 n)) (sectorFourier_physical n u))
  have h₁ := sectorFourierProductMap_kernel (n+1)
    (physicalFourierUnitary (generalizedCreationSector (phaseMultiplicationKernel f) n u))
  have h₂ := congrArg (fun v : kernelFixed (E := ElectronL2) (n+1) => (v : KernelSector ElectronL2 (n+1)))
    (sectorFourier_physical (n+1) (generalizedCreationSector (phaseMultiplicationKernel f) n u))
  have h₃ := congrArg (amplify (sectorMeasure (n+1)) sectorFourierElectronMap)
    (fiberGeneralizedCreation_intertwines (phaseMultiplicationKernel f) n u)
  have h₄ := congrArg (fun v : kernelFixed (E := ElectronL2) (n+1) => (v : KernelSector ElectronL2 (n+1)))
    (sectorFourier_fixedCreation_covariance (physicalFourierUnitary (H := ℂ))
      (phaseMultiplicationKernel f) n (physicalSectorKernel n u)).symm
  have h₅ := sectorFourierCreationExpression_kernel n f (sectorFourierProductMap n (physicalFourierUnitary u))
  have h₆ := congrArg (fun v : KernelSector ElectronL2 n =>
      (Real.sqrt (n+1 : ℕ) : ℂ) • kernelSymmetrizer (n+1) (kernelCreationRaw (sectorFourierPhaseKernel f) n v)) hz
  have h₇ : (Real.sqrt (n+1 : ℕ) : ℂ) • kernelSymmetrizer (n+1)
      (kernelCreationRaw (sectorFourierPhaseKernel f) n (z : KernelSector ElectronL2 n)) =
      (kernelCreation (sectorFourierPhaseKernel f) n z : KernelSector ElectronL2 (n+1)) :=
    (kernelCreation_value (sectorFourierPhaseKernel f) n z).symm
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans (h₆.trans h₇)).symm)))

end GW.Fock

-- Compiled component RawAdjoint01
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Fock
open GW.Analysis

lemma sectorFourier_tensor_scalar {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : Lp ℂ 2 μ) (c : ℂ) : tensorEmbedding μ f c = c • f := by
  apply Lp.ext
  filter_upwards [tensorEmbedding_ae μ f c,Lp.coeFn_smul c f] with x h₁ h₂
  rw [h₁,h₂]
  simp only [Pi.smul_apply,smul_eq_mul]
  exact mul_comm _ _

lemma sectorFourier_product_contraction_pairing {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (γ : Lp ℂ 2 μ) (f : Lp ℂ 2 ν) (v : Lp ℂ 2 (μ.prod ν)) :
    ⟪productFunction μ ν γ f,v⟫_ℂ = ⟪γ,spectatorContraction μ ν f v⟫_ℂ := by
  let P := productUnitary (E := ℂ) μ ν
  have h₁ := P.inner_map_map (tensorEmbedding μ γ f) (P.symm v)
  rw [productUnitary_tensor,LinearIsometryEquiv.apply_symm_apply] at h₁
  have h₂ : ⟪γ,spectatorContraction μ ν f v⟫_ℂ = ⟪tensorEmbedding μ γ f,P.symm v⟫_ℂ := by
    rw [spectatorContraction_identification,L2.inner_def,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [amplify_ae μ (contraction (E := ℂ) ν f) (P.symm v),tensorEmbedding_ae μ γ f] with x hA hT
    rw [hA,hT]
    simpa only [sectorFourier_tensor_scalar] using contraction_pairing ν f (γ x) (P.symm v x)
  exact h₁.trans h₂.symm

lemma sectorFourier_raw_pairing (n : ℕ) (f : OneBoson)
    (u : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure n)))
    (v : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure (n+1)))) :
    ⟪sectorFourierRawCreation n f u,v⟫_ℂ = ⟪u,sectorFourierRawAnnihilation n f v⟫_ℂ := by
  let A := sectorFourierSplit n
  let S := momentumShearWithL2 (E := ℂ) (sectorMeasure n) 1
  let R := sectorFourierReorderUnitary n
  let z := productFunction ((volume : Measure GW.Space).prod (sectorMeasure n)) volume u f
  have h₁ : ⟪A.symm (S (R.symm z)),v⟫_ℂ = ⟪S (R.symm z),A v⟫_ℂ := A.symm.inner_map_eq_flip _ _
  have h₂ := S.inner_map_eq_flip (R.symm z) (A v)
  have h₃ : ⟪R.symm z,S.symm (A v)⟫_ℂ = ⟪z,R (S.symm (A v))⟫_ℂ := R.symm.inner_map_eq_flip _ _
  have h₄ := sectorFourier_product_contraction_pairing
    ((volume : Measure GW.Space).prod (sectorMeasure n)) (volume : Measure GW.Space) u f (R (S.symm (A v)))
  have hS : S.symm (A v) = momentumShearWithL2 (E := ℂ) (sectorMeasure n) (-1) (A v) := by
    change (momentumShearWithL2 (E := ℂ) (sectorMeasure n) 1).symm (A v) = _
    rw [momentumShearWithL2_inverse]
  have h₅ := congrArg (fun w => ⟪u,spectatorContraction
    ((volume : Measure GW.Space).prod (sectorMeasure n)) (volume : Measure GW.Space) f (R w)⟫_ℂ) hS
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

lemma sectorFourierRawAnnihilation_kernel (n : ℕ) (f : OneBoson)
    (v : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure (n+1)))) :
    physicalKernelProduct n (sectorFourierRawAnnihilation n f v) =
      kernelAnnihilationRaw (sectorFourierPhaseKernel f) n (physicalKernelProduct (n+1) v) := by
  apply ext_inner_left ℂ
  intro z
  let u := (physicalKernelProduct n).symm z
  have h₁ := (physicalKernelProduct n).inner_map_map u (sectorFourierRawAnnihilation n f v)
  have h₂ := (sectorFourier_raw_pairing n f u v).symm
  have h₃ := ((physicalKernelProduct (n+1)).inner_map_map (sectorFourierRawCreation n f u) v).symm
  have h₄ := congrArg (fun w : KernelSector ElectronL2 (n+1) => ⟪w,physicalKernelProduct (n+1) v⟫_ℂ)
    (sectorFourierRawCreation_kernel n f u)
  have h₅ := kernelRaw_pairing (sectorFourierPhaseKernel f) n (physicalKernelProduct n u) (physicalKernelProduct (n+1) v)
  have h := h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))
  simpa only [u,LinearIsometryEquiv.apply_symm_apply] using h

end GW.Fock

-- Compiled component AnnihilationIdentification02
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Fock
open GW.Analysis

section AnnihilationCovariance
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
lemma sectorFourier_kernelAnnihilation_precomp (F : BosonKernel E) (T : E →L[ℂ] E)
    (n : ℕ) (u : KernelSector E (n+1)) :
    kernelAnnihilationRaw (F.comp T) n u =
      amplify (sectorMeasure n) T.adjoint (kernelAnnihilationRaw F n u) := by
  change amplify (sectorMeasure n) (F.comp T).adjoint (kernelSplit n u) =
    amplify (sectorMeasure n) T.adjoint (amplify (sectorMeasure n) F.adjoint (kernelSplit n u))
  rw [ContinuousLinearMap.adjoint_comp]
  exact frankSchlein_amplify_comp (sectorMeasure n) T.adjoint F.adjoint (kernelSplit n u)
lemma sectorFourier_kernelAnnihilation_covariance (U : E ≃ₗᵢ[ℂ] E) (F : BosonKernel E)
    (n : ℕ) (u : KernelSector E (n+1)) :
    kernelAnnihilationRaw (sectorFourierConjugateKernel U F) n
      (amplify (sectorMeasure (n+1)) U.toContinuousLinearEquiv.toContinuousLinearMap u) =
    amplify (sectorMeasure n) U.toContinuousLinearEquiv.toContinuousLinearMap (kernelAnnihilationRaw F n u) := by
  have hU : U.toContinuousLinearEquiv.toContinuousLinearMap.adjoint =
      U.symm.toContinuousLinearEquiv.toContinuousLinearMap := U.adjoint_eq_symm
  have hV : U.symm.toContinuousLinearEquiv.toContinuousLinearMap.adjoint =
      U.toContinuousLinearEquiv.toContinuousLinearMap := by
    simpa only [LinearIsometryEquiv.symm_symm] using U.symm.adjoint_eq_symm
  rw [sectorFourierConjugateKernel,frankSchlein_kernelAnnihilation_factor,hU,
    sectorFourier_amplify_inverse,sectorFourier_kernelAnnihilation_precomp,hV]
lemma sectorFourier_fixedAnnihilation_covariance (U : E ≃ₗᵢ[ℂ] E) (F : BosonKernel E)
    (n : ℕ) (u : kernelFixed (E := E) (n+1)) :
    kernelAnnihilation (sectorFourierConjugateKernel U F) n
      (frankSchleinFixedAmplify U.toContinuousLinearEquiv.toContinuousLinearMap (n+1) u) =
    frankSchleinFixedAmplify U.toContinuousLinearEquiv.toContinuousLinearMap n (kernelAnnihilation F n u) := by
  apply Subtype.ext
  change (Real.sqrt (n+1 : ℕ) : ℂ) • kernelAnnihilationRaw (sectorFourierConjugateKernel U F) n
    (amplify (sectorMeasure (n+1)) U.toContinuousLinearEquiv.toContinuousLinearMap u.val) =
    amplify (sectorMeasure n) U.toContinuousLinearEquiv.toContinuousLinearMap
      ((Real.sqrt (n+1 : ℕ) : ℂ) • kernelAnnihilationRaw F n u.val)
  rw [sectorFourier_kernelAnnihilation_covariance,map_smul]
end AnnihilationCovariance

def sectorFourierAnnihilationExpression (n : ℕ) (f : OneBoson)
    (u : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure (n+1)))) :
    Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure n)) :=
  (Real.sqrt (n+1 : ℕ) : ℂ) • sectorFourierRawAnnihilation n f u

lemma sectorFourierAnnihilationExpression_ae (n : ℕ) (f : OneBoson)
    (u : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure (n+1)))) :
    sectorFourierAnnihilationExpression n f u =ᵐ[(volume : Measure GW.Space).prod (sectorMeasure n)] fun p =>
      (Real.sqrt (n+1 : ℕ) : ℂ) * ∫ k : GW.Space, (starRingEnd ℂ) (f k)*
        u (p.1-k,(splitCoordinates n 0).symm (k,p.2)) ∂volume := by
  filter_upwards [Lp.coeFn_smul (Real.sqrt (n+1 : ℕ) : ℂ) (sectorFourierRawAnnihilation n f u),
    sectorFourierRawAnnihilation_ae n f u] with p h₁ h₂
  change ((Real.sqrt (n+1 : ℕ) : ℂ) • sectorFourierRawAnnihilation n f u) p = _
  rw [h₁]
  change (Real.sqrt (n+1 : ℕ) : ℂ) * (sectorFourierRawAnnihilation n f u) p = _
  rw [h₂]

lemma sectorFourierAnnihilationExpression_kernel (n : ℕ) (f : OneBoson)
    (u : Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure (n+1)))) :
    physicalKernelProduct n (sectorFourierAnnihilationExpression n f u) =
      (Real.sqrt (n+1 : ℕ) : ℂ) • kernelAnnihilationRaw (sectorFourierPhaseKernel f) n (physicalKernelProduct (n+1) u) :=
  ((physicalKernelProduct n).map_smul (Real.sqrt (n+1 : ℕ) : ℂ) (sectorFourierRawAnnihilation n f u)).trans
    (congrArg (fun z : KernelSector ElectronL2 n => (Real.sqrt (n+1 : ℕ) : ℂ) • z) (sectorFourierRawAnnihilation_kernel n f u))

lemma sectorFourier_actualAnnihilation_intertwines (K : BosonKernel ElectronL2) (n : ℕ) (u : ElectronSector (n+1)) :
    (physicalSectorKernel n (generalizedAnnihilationSector K n u) : KernelSector ElectronL2 n) =
      (kernelAnnihilation K n (physicalSectorKernel (n+1) u) : KernelSector ElectronL2 n) :=
  congrArg (fun z : kernelFixed (E := ElectronL2) n => (z : KernelSector ElectronL2 n))
    ((physicalSectorKernel n).apply_symm_apply (kernelAnnihilation K n (physicalSectorKernel (n+1) u)))

lemma sectorFourier_annihilation_identification (n : ℕ) (f : OneBoson) (u : ElectronSector (n+1)) :
    sectorFourierProductMap n (physicalFourierUnitary (generalizedAnnihilationSector (phaseMultiplicationKernel f) n u)) =
      sectorFourierAnnihilationExpression n f (sectorFourierProductMap (n+1) (physicalFourierUnitary u)) := by
  apply (physicalKernelProduct n).injective
  let z := frankSchleinFixedAmplify sectorFourierElectronMap (n+1) (physicalSectorKernel (n+1) u)
  have hz : physicalKernelProduct (n+1) (sectorFourierProductMap (n+1) (physicalFourierUnitary u)) =
      (z : KernelSector ElectronL2 (n+1)) :=
    (sectorFourierProductMap_kernel (n+1) (physicalFourierUnitary u)).trans
      (congrArg (fun v : kernelFixed (E := ElectronL2) (n+1) => (v : KernelSector ElectronL2 (n+1)))
        (sectorFourier_physical (n+1) u))
  have h₁ := sectorFourierProductMap_kernel n (physicalFourierUnitary (generalizedAnnihilationSector (phaseMultiplicationKernel f) n u))
  have h₂ := congrArg (fun v : kernelFixed (E := ElectronL2) n => (v : KernelSector ElectronL2 n))
    (sectorFourier_physical n (generalizedAnnihilationSector (phaseMultiplicationKernel f) n u))
  have h₃ := congrArg (amplify (sectorMeasure n) sectorFourierElectronMap)
    (sectorFourier_actualAnnihilation_intertwines (phaseMultiplicationKernel f) n u)
  have h₄ := congrArg (fun v : kernelFixed (E := ElectronL2) n => (v : KernelSector ElectronL2 n))
    (sectorFourier_fixedAnnihilation_covariance (physicalFourierUnitary (H := ℂ))
      (phaseMultiplicationKernel f) n (physicalSectorKernel (n+1) u)).symm
  have h₅ := sectorFourierAnnihilationExpression_kernel n f (sectorFourierProductMap (n+1) (physicalFourierUnitary u))
  have h₆ := congrArg (fun v : KernelSector ElectronL2 (n+1) =>
      (Real.sqrt (n+1 : ℕ) : ℂ) • kernelAnnihilationRaw (sectorFourierPhaseKernel f) n v) hz
  have h₇ : (Real.sqrt (n+1 : ℕ) : ℂ) • kernelAnnihilationRaw (sectorFourierPhaseKernel f) n
      (z : KernelSector ElectronL2 (n+1)) =
      (kernelAnnihilation (sectorFourierPhaseKernel f) n z : KernelSector ElectronL2 n) :=
    (kernelAnnihilation_value (sectorFourierPhaseKernel f) n z).symm
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans (h₆.trans h₇)).symm)))

end GW.Fock

-- Compiled component FullVectors01
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Fock
open GW.Analysis

def sectorFourierFullSector (u : Physical) (n : ℕ) :
    Lp ℂ 2 ((volume : Measure GW.Space).prod (sectorMeasure n)) :=
  sectorFourierProductMap n (freeFourierRepresentation u n)

lemma sectorFourierFullSector_creation (f : OneBoson)
    (u : (generalizedCreation (phaseMultiplicationKernel f)).domain) (n : ℕ) :
    sectorFourierFullSector (generalizedCreation (phaseMultiplicationKernel f) u) (n+1) =
      sectorFourierCreationExpression n f (sectorFourierFullSector u.val n) := by
  have h := congrArg (fun z : ElectronSector (n+1) =>
    sectorFourierProductMap (n+1) (physicalFourierUnitary z))
    (generalizedCreation_succ (phaseMultiplicationKernel f) u n)
  exact h.trans (sectorFourier_creation_identification n f (electronBosonUnitary.symm u.val n))

lemma sectorFourierFullSector_annihilation (f : OneBoson)
    (u : (generalizedAnnihilation (phaseMultiplicationKernel f)).domain) (n : ℕ) :
    sectorFourierFullSector (generalizedAnnihilation (phaseMultiplicationKernel f) u) n =
      sectorFourierAnnihilationExpression n f (sectorFourierFullSector u.val (n+1)) := by
  have h := congrArg (fun z : ElectronSector n =>
    sectorFourierProductMap n (physicalFourierUnitary z))
    (generalizedAnnihilation_apply (phaseMultiplicationKernel f) u n)
  exact h.trans (sectorFourier_annihilation_identification n f (electronBosonUnitary.symm u.val (n+1)))

lemma sectorFourierFullSector_creation_zero (f : OneBoson)
    (u : (generalizedCreation (phaseMultiplicationKernel f)).domain) :
    sectorFourierFullSector (generalizedCreation (phaseMultiplicationKernel f) u) 0 = 0 := by
  have h := congrArg (fun z : ElectronSector 0 =>
    sectorFourierProductMap 0 (physicalFourierUnitary z))
    (generalizedCreation_zero (phaseMultiplicationKernel f) u)
  exact h.trans (by rw [map_zero,map_zero])

def sectorFourierRootAnnihilationInput (f : OneBoson)
    (u : (physicalNumberPower (1/2)).domain) :
    (generalizedAnnihilation (phaseMultiplicationKernel f)).domain :=
  ⟨u.val,generalizedAnnihilation_mem_root (phaseMultiplicationKernel f) u⟩

def sectorFourierRootCreationInput (f : OneBoson)
    (u : (physicalNumberPower (1/2)).domain) :
    (generalizedCreation (phaseMultiplicationKernel f)).domain :=
  generalizedCreationRootInput (phaseMultiplicationKernel f) u

lemma sectorFourierFullSector_annihilation_ae (f : OneBoson)
    (u : (generalizedAnnihilation (phaseMultiplicationKernel f)).domain) (n : ℕ) :
    sectorFourierFullSector (generalizedAnnihilation (phaseMultiplicationKernel f) u) n
      =ᵐ[(volume : Measure GW.Space).prod (sectorMeasure n)] fun p =>
      (Real.sqrt (n+1 : ℕ) : ℂ) * ∫ k : GW.Space, (starRingEnd ℂ) (f k) *
        sectorFourierFullSector u.val (n+1) (p.1-k,(splitCoordinates n 0).symm (k,p.2)) ∂volume := by
  rw [sectorFourierFullSector_annihilation]
  exact sectorFourierAnnihilationExpression_ae n f _

end GW.Fock

-- Compiled component FullAE01
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Fock
open GW.Analysis

lemma sectorFourierProductMap_symmetric (n : ℕ) (u : ElectronSector n)
    (τ : Equiv.Perm (Fin n)) :
    productPermutation (volume : Measure GW.Space) n τ (sectorFourierProductMap n u) =
      sectorFourierProductMap n u := by
  apply (physicalKernelProduct n).injective
  rw [physicalKernelProduct_permutation,sectorFourierProductMap_kernel]
  exact (mem_kernelFixed n _).mp (physicalSectorKernel n u).property τ

lemma sectorFourierFullSector_creation_ae (f : OneBoson)
    (u : (generalizedCreation (phaseMultiplicationKernel f)).domain) (n : ℕ) :
    sectorFourierFullSector (generalizedCreation (phaseMultiplicationKernel f) u) (n+1)
      =ᵐ[(volume : Measure GW.Space).prod (sectorMeasure (n+1))] fun p =>
        (Real.sqrt (n+1 : ℕ) : ℂ)⁻¹ * ∑ j : Fin (n+1), f (p.2 j) *
          sectorFourierFullSector u.val n (p.1+p.2 j,fun i => p.2 (j.succAbove i)) := by
  rw [sectorFourierFullSector_creation]
  exact sectorFourierCreationExpression_ae n f _
    (fun τ => sectorFourierProductMap_symmetric n (freeFourierRepresentation u.val n) τ)

lemma sectorFourierFullSector_annihilation_integrable (f : OneBoson) (u : Physical) (n : ℕ) :
    ∀ᵐ p ∂((volume : Measure GW.Space).prod (sectorMeasure n)),
      Integrable (fun k : GW.Space => (starRingEnd ℂ) (f k) *
        sectorFourierFullSector u (n+1) (p.1-k,(splitCoordinates n 0).symm (k,p.2)))
        (volume : Measure GW.Space) :=
  sectorFourierRawAnnihilation_integrable n f _

lemma sectorFourierFullSector_creation_zero_ae (f : OneBoson)
    (u : (generalizedCreation (phaseMultiplicationKernel f)).domain) :
    sectorFourierFullSector (generalizedCreation (phaseMultiplicationKernel f) u) 0
      =ᵐ[(volume : Measure GW.Space).prod (sectorMeasure 0)] fun _ => 0 := by
  rw [sectorFourierFullSector_creation_zero]
  exact Lp.coeFn_zero _ _ _

lemma sectorFourierFullSector_common_ae (f : OneBoson)
    (u : (physicalNumberPower (1/2)).domain) :
    ∀ᵐ q ∂(volume : Measure GW.Space), ∀ n : ℕ,
      (∀ᵐ ks ∂sectorMeasure n,
        sectorFourierFullSector (generalizedAnnihilation (phaseMultiplicationKernel f)
          (sectorFourierRootAnnihilationInput f u)) n (q,ks) =
          (Real.sqrt (n+1 : ℕ) : ℂ) * ∫ k : GW.Space, (starRingEnd ℂ) (f k) *
            sectorFourierFullSector u.val (n+1) (q-k,(splitCoordinates n 0).symm (k,ks)) ∂volume) ∧
      (∀ᵐ ks ∂sectorMeasure n,
        Integrable (fun k : GW.Space => (starRingEnd ℂ) (f k) *
          sectorFourierFullSector u.val (n+1) (q-k,(splitCoordinates n 0).symm (k,ks))) volume) ∧
      (∀ᵐ ks ∂sectorMeasure (n+1),
        sectorFourierFullSector (generalizedCreation (phaseMultiplicationKernel f)
          (sectorFourierRootCreationInput f u)) (n+1) (q,ks) =
          (Real.sqrt (n+1 : ℕ) : ℂ)⁻¹ * ∑ j : Fin (n+1), f (ks j) *
            sectorFourierFullSector u.val n (q+ks j,fun i => ks (j.succAbove i))) := by
  apply ae_all_iff.mpr
  intro n
  filter_upwards [Measure.ae_ae_of_ae_prod
      (sectorFourierFullSector_annihilation_ae f (sectorFourierRootAnnihilationInput f u) n),
    Measure.ae_ae_of_ae_prod (sectorFourierFullSector_annihilation_integrable f u.val n),
    Measure.ae_ae_of_ae_prod
      (sectorFourierFullSector_creation_ae f (sectorFourierRootCreationInput f u) n)] with q hA hI hC
  exact ⟨hA,hI,hC⟩

end GW.Fock

-- Compiled component NumberBounds04
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators
namespace GW.Fock
open GW.Analysis

lemma sectorFourier_annihilation_norm (f : OneBoson)
    (u : (physicalNumberPower (1/2)).domain) :
    ‖generalizedAnnihilation (phaseMultiplicationKernel f) (sectorFourierRootAnnihilationInput f u)‖ ≤
      ‖f‖ * ‖physicalNumberPower (1/2) u‖ := by
  simpa only [sectorFourierRootAnnihilationInput,phaseMultiplicationKernel_norm] using
    generalizedAnnihilation_root_norm (phaseMultiplicationKernel f) u

lemma sectorFourier_root_graphs (f : OneBoson)
    (u : (physicalNumberPower (1/2)).domain) :
    (u.val,generalizedAnnihilation (phaseMultiplicationKernel f) (sectorFourierRootAnnihilationInput f u)) ∈
      (generalizedAnnihilation (phaseMultiplicationKernel f)).graph ∧
    (u.val,generalizedCreation (phaseMultiplicationKernel f) (sectorFourierRootCreationInput f u)) ∈
      (generalizedCreation (phaseMultiplicationKernel f)).graph := by
  constructor
  · exact (generalizedAnnihilation (phaseMultiplicationKernel f)).mem_graph_iff.mpr
      ⟨sectorFourierRootAnnihilationInput f u,rfl,rfl⟩
  · exact (generalizedCreation (phaseMultiplicationKernel f)).mem_graph_iff.mpr
      ⟨sectorFourierRootCreationInput f u,rfl,rfl⟩

/-- The two source Fourier expressions are the sectors of the original full field vectors,
with the original number-domain graph memberships and sharp full-vector bounds.
The pointwise formulas and common full-measure set are given by
`sectorFourierFullSector_common_ae`, with sector zero handled separately. -/
theorem reg_sector_fourier (f : OneBoson) (u : (physicalNumberPower (1/2)).domain) :
    (∀ n : ℕ,
      sectorFourierFullSector (generalizedAnnihilation (phaseMultiplicationKernel f)
        (sectorFourierRootAnnihilationInput f u)) n =
          sectorFourierAnnihilationExpression n f (sectorFourierFullSector u.val (n+1))) ∧
    (∀ n : ℕ,
      sectorFourierFullSector (generalizedCreation (phaseMultiplicationKernel f)
        (sectorFourierRootCreationInput f u)) (n+1) =
          sectorFourierCreationExpression n f (sectorFourierFullSector u.val n)) ∧
    sectorFourierFullSector (generalizedCreation (phaseMultiplicationKernel f)
        (sectorFourierRootCreationInput f u)) 0 = 0 ∧
    ‖generalizedAnnihilation (phaseMultiplicationKernel f) (sectorFourierRootAnnihilationInput f u)‖ ≤
      ‖f‖ * ‖physicalNumberPower (1/2) u‖ :=
  ⟨sectorFourierFullSector_annihilation f _,sectorFourierFullSector_creation f _,
    sectorFourierFullSector_creation_zero f _,sectorFourier_annihilation_norm f u⟩

end GW.Fock
