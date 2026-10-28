import OAI.ArithmeticGeometry.Descent.CMVariety.MarkedPeriodClassification
import OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveHodgeNaturality
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Marked Actions -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.MarkedActions.Abelian.IntrinsicPeriods

noncomputable section

section

/-!
Actual algebraic endomorphisms in the rational marking. Their pullbacks
preserve the canonical Hodge subspace by naturality of the literal pure
forms and singular-cohomology coefficient comparison.
-/

open _root_.CategoryTheory
open scoped TensorProduct

variable {ι : Type}

theorem algebraic_pullback_isHodge (A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (HA : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1))
    (HB : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (B.variety.rationalCohomology 1))
    (hHA : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.IsCanonicalH1 A.variety HA) (hHB : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.IsCanonicalH1 B.variety HB)
    (f : B.toOver ⟶ A.toOver) : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.IsHodgeMap HA HB (AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback f) := by
  intro x hx
  rw [hHA.1] at hx
  rw [hHB.1]
  change AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (AlgebraicGeometry.Betti.Scheme.schemePointSpace B.toOver) 1
    ((AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback f).baseChange ℂ x) ∈ B.variety.pureBettiSubspace 1 0
  have hn : AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (AlgebraicGeometry.Betti.Scheme.schemePointSpace B.toOver) 1
      ((AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback f).baseChange ℂ x) =
        AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback (V := B.variety) (W := A.variety) f 1
          (AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (AlgebraicGeometry.Betti.Scheme.schemePointSpace A.toOver) 1 x) :=
    AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.complexification_pullback (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) 1 x
  rw [hn]
  exact AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback_mem_pureBettiSubspace f 1 0 hx

theorem rationalCoordinates_symm_baseChange {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking ι A)
    (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (A.variety.rationalCohomology 1)) :
    (MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates b).symm.toLinearMap.baseChange ℂ
      ((MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates b).toLinearMap.baseChange ℂ x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul z x =>
    simp only [LinearMap.baseChange_tmul, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem markedHodge_baseChange_holomorphic_iff {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking ι A)
    (H : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1))
    (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (A.variety.rationalCohomology 1)) :
    (MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates b).toLinearMap.baseChange ℂ x ∈
      (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure b H).holomorphic ↔ x ∈ H.holomorphic := by
  change (MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates b).symm.toLinearMap.baseChange ℂ
      ((MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates b).toLinearMap.baseChange ℂ x) ∈ H.holomorphic ↔ _
  rw [rationalCoordinates_symm_baseChange]

theorem markedHodge_baseChange_antiholomorphic_iff {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking ι A)
    (H : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1))
    (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (A.variety.rationalCohomology 1)) :
    (MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates b).toLinearMap.baseChange ℂ x ∈
      (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure b H).antiholomorphic ↔ x ∈ H.antiholomorphic := by
  change (MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates b).symm.toLinearMap.baseChange ℂ
      ((MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates b).toLinearMap.baseChange ℂ x) ∈ H.antiholomorphic ↔ _
  rw [rationalCoordinates_symm_baseChange]

/-- Conjugation of an actual rational operator into the fixed marking. -/
def conjugateCoordinates {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking ι A)
    (u : A.variety.rationalCohomology 1 →ₗ[ℚ] A.variety.rationalCohomology 1) :
    (ι → ℚ) →ₗ[ℚ] (ι → ℚ) :=
  (MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates b).toLinearMap.comp (u.comp (MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates b).symm.toLinearMap)

theorem conjugateCoordinates_baseChange {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking ι A)
    (u : A.variety.rationalCohomology 1 →ₗ[ℚ] A.variety.rationalCohomology 1)
    (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (A.variety.rationalCohomology 1)) :
    (conjugateCoordinates b u).baseChange ℂ ((MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates b).toLinearMap.baseChange ℂ x) =
      (MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates b).toLinearMap.baseChange ℂ (u.baseChange ℂ x) := by
  simp only [conjugateCoordinates, LinearMap.baseChange_comp, LinearMap.comp_apply]
  rw [rationalCoordinates_symm_baseChange]

theorem conjugateCoordinates_hodge {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking ι A)
    (H : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1))
    (u : A.variety.rationalCohomology 1 →ₗ[ℚ] A.variety.rationalCohomology 1)
    (hu : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.IsHodgeMap H H u) :
    AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.IsHodgeMap (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure b H) (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure b H) (conjugateCoordinates b u) := by
  intro x hx
  let e := (MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates b).baseChange ℚ ℂ _ _
  obtain ⟨y, rfl⟩ := e.surjective x
  change (MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates b).toLinearMap.baseChange ℂ y ∈
    (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure b H).holomorphic at hx
  change (conjugateCoordinates b u).baseChange ℂ
    ((MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates b).toLinearMap.baseChange ℂ y) ∈ _
  rw [conjugateCoordinates_baseChange, markedHodge_baseChange_holomorphic_iff]
  exact hu y ((markedHodge_baseChange_holomorphic_iff b H y).mp hx)

def markedEndomorphism {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking ι A) (f : A.toOver ⟶ A.toOver) :
    (ι → ℚ) →ₗ[ℚ] (ι → ℚ) := conjugateCoordinates b (AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback f)

theorem markedEndomorphism_hodge {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking ι A)
    (H : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1))
    (hH : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.IsCanonicalH1 A.variety H) (f : A.toOver ⟶ A.toOver) :
    AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.IsHodgeMap (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure b H) (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure b H) (markedEndomorphism b f) :=
  conjugateCoordinates_hodge b H _ (algebraic_pullback_isHodge A A H H hH hH f)

end

/-!
Construct holomorphic frames from actual marked period matrices in fixed
tangent coordinates. The frame is the ordinary transpose of the period
map, and is continuous whenever that period map is continuous. Its image
is identified with the actual canonical Hodge subspace by integration.
-/

variable {I J : Type} [Fintype I] [Fintype J]

def coordinateDual (I : Type) [Fintype I] :
    (I → ℂ) ≃ₗ[ℂ] Module.Dual ℂ (I → ℂ) := (Pi.basisFun ℂ I).constr ℂ

/-- Transpose in the fixed finite coordinate bases, as an actual
continuous-linear-map-valued linear operator. -/
def periodTranspose : ((I → ℂ) →L[ℂ] (J → ℂ)) →ₗ[ℂ]
    ((J → ℂ) →L[ℂ] (I → ℂ)) where
  toFun p := ((coordinateDual I).symm.toLinearMap.comp
    (p.toLinearMap.dualMap.comp (coordinateDual J).toLinearMap)).toContinuousLinearMap
  map_add' p q := by
    apply ContinuousLinearMap.ext
    intro x
    change (coordinateDual I).symm (((p + q).toLinearMap).dualMap (coordinateDual J x)) =
      (coordinateDual I).symm (p.toLinearMap.dualMap (coordinateDual J x)) +
        (coordinateDual I).symm (q.toLinearMap.dualMap (coordinateDual J x))
    rw [← map_add]
    congr 1
    ext y
    change coordinateDual J x (p y + q y) = _
    rw [map_add]
    rfl
  map_smul' c p := by
    apply ContinuousLinearMap.ext
    intro x
    change (coordinateDual I).symm (((c • p).toLinearMap).dualMap (coordinateDual J x)) =
      c • (coordinateDual I).symm (p.toLinearMap.dualMap (coordinateDual J x))
    rw [← map_smul]
    congr 1
    ext y
    change coordinateDual J x (c • p y) = _
    rw [map_smul]
    rfl

theorem coordinateDual_periodTranspose (p : (I → ℂ) →L[ℂ] (J → ℂ)) (x : J → ℂ) :
    coordinateDual I (periodTranspose p x) =
      p.toLinearMap.dualMap (coordinateDual J x) :=
  (coordinateDual I).apply_symm_apply _

theorem periodTranspose_injective (p : (I → ℂ) →L[ℂ] (J → ℂ))
    (hp : Function.Surjective p) : Function.Injective (periodTranspose p) := by
  intro x y h
  apply (coordinateDual J).injective
  apply LinearMap.dualMap_injective_of_surjective hp
  rw [← coordinateDual_periodTranspose, ← coordinateDual_periodTranspose, h]

/-- Continuity of the frame is proved from the actual period matrix. -/
theorem continuous_periodTranspose :
    Continuous (periodTranspose : ((I → ℂ) →L[ℂ] (J → ℂ)) →
      ((J → ℂ) →L[ℂ] (I → ℂ))) := periodTranspose.continuous_of_finiteDimensional

theorem periodTranspose_range (p : (I → ℂ) →L[ℂ] (J → ℂ)) :
    (periodTranspose p).toLinearMap.range.map (coordinateDual I).toLinearMap =
      p.toLinearMap.ker.dualAnnihilator := by
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker]
  ext φ
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨coordinateDual J x, (coordinateDual_periodTranspose p x).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨periodTranspose p ((coordinateDual J).symm x), ⟨_, rfl⟩, ?_⟩
    rw [LinearEquiv.coe_coe, coordinateDual_periodTranspose, LinearEquiv.apply_symm_apply]

/-- The transpose frame spans exactly the actual marked Hodge subspace.
The tangent coordinates may be any complex-linear equivalence. -/
theorem periodTranspose_range_markedHodge {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking I A) (e : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A ≃ₗ[ℂ] (J → ℂ))
    (H : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1))
    (hH : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.IsCanonicalH1 A.variety H) :
    (periodTranspose (e.toLinearMap.comp (MarkedAbelianPeriods.IntrinsicPeriods.periodMap b)).toContinuousLinearMap).toLinearMap.range =
      (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure b H).holomorphic.map MarkedPeriodClassification.Abelian.IntrinsicPeriods.scalarCoordinates.toLinearMap := by
  apply (Submodule.orderIsoMapComap (coordinateDual I)).injective
  change (periodTranspose (e.toLinearMap.comp (MarkedAbelianPeriods.IntrinsicPeriods.periodMap b)).toContinuousLinearMap).toLinearMap.range.map
      (coordinateDual I).toLinearMap =
    ((MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure b H).holomorphic.map MarkedPeriodClassification.Abelian.IntrinsicPeriods.scalarCoordinates.toLinearMap).map
      (coordinateDual I).toLinearMap
  rw [periodTranspose_range, ← Submodule.map_comp]
  have hker : (e.toLinearMap.comp (MarkedAbelianPeriods.IntrinsicPeriods.periodMap b)).ker = (MarkedAbelianPeriods.IntrinsicPeriods.periodMap b).ker := by
    ext x
    change e (MarkedAbelianPeriods.IntrinsicPeriods.periodMap b x) = 0 ↔ MarkedAbelianPeriods.IntrinsicPeriods.periodMap b x = 0
    exact e.map_eq_zero_iff
  change (e.toLinearMap.comp (MarkedAbelianPeriods.IntrinsicPeriods.periodMap b)).ker.dualAnnihilator =
    (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure b H).holomorphic.map MarkedPeriodClassification.Abelian.IntrinsicPeriods.scalarMarkedBetti.toLinearMap
  rw [hker, MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodge_holomorphic_image b H hH, MarkedAbelianPeriods.IntrinsicPeriods.markedHolomorphic_eq_annihilator]

end

end OAI.ArithmeticGeometry.Descent.CMVariety.MarkedActions.Abelian.IntrinsicPeriods
