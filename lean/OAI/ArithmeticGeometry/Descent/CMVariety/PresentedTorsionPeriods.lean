import OAI.ArithmeticGeometry.Descent.CMVariety.ContinuousPresentedPeriods
import OAI.ArithmeticGeometry.Descent.CMVariety.TorsionPeriodCoordinates
import OAI.ArithmeticGeometry.Descent.CMVariety.LevelComparison

/-! # Presented Torsion Periods -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.PresentedTorsionPeriods.Abelian

noncomputable section

/-!
The presented marked-period point is the actual chart exponential under
the geometric comparison. This identity connects divided-period level
references to the marking preserved by the constructed algebraic maps.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped Classical _root_.Manifold ContDiff _root_.CategoryTheory.MonObj BigOperators

local instance (B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral B.toOver.left := B.variety.property
local instance (B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth B.toOver.hom := B.variety.presentation.smooth

theorem periodMap_eq_realFrame
    {Index V : Type} [Fintype Index]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V]
    {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index A)
    (T : V ≃L[ℂ] AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) (r : (Index → ℝ) →ₗ[ℝ] V)
    (hb : ∀ i, (b i : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) = T (r (Pi.single i 1))) (v : Index → ℝ) :
    MarkedAbelianPeriods.IntrinsicPeriods.periodMap b (fun i => (v i : ℂ)) = T (r v) := by
  rw [MarkedAbelianPeriods.IntrinsicPeriods.periodMap_apply, TorsionPeriodCoordinates.Abelian.realFrame_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hb]
  have h := (T.toLinearEquiv.restrictScalars ℝ).map_smul (v i) (r (Pi.single i 1))
  change T ((v i) • r (Pi.single i 1)) = (v i) • T (r (Pi.single i 1)) at h
  simpa only [← algebraMap_smul ℂ (v i), Complex.coe_algebraMap] using h.symm

namespace ComplexAbelianPresentation

variable {g : ℕ} {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
  [IsIntegral A.scheme.left] [T2Space (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme)]
  {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  [IsScalarTower ℝ ℂ V]

local instance : LieGroup (𝓘(ℝ, ContinuousPresentedPeriods.Abelian.abelianSchemeNativeModel A)) ∞ (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme) :=
  IntrinsicFiberLieGroup.Abelian.nativeScheme_realLieGroup A.scheme

omit [IsScalarTower ℝ ℂ V] in
theorem _root_.OAI.ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation.chart_exponential_eq_presented_period
    (P : StandardModuli.Abelian.ComplexAbelianPresentation A)
    (c : OpenPartialHomeomorph (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme) V)
    (T : V ≃L[ℂ] AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel P.variety)
    (hT : ∀ v, T v = mfderiv (𝓘(ℝ, ContinuousPresentedPeriods.Abelian.abelianSchemeNativeModel A))
      (𝓘(ℝ, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel P.variety)) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map P.comparison.hom) 1
        (ChartEndomorphismDerivative.Abelian.chartTangentMap (E := ContinuousPresentedPeriods.Abelian.abelianSchemeNativeModel A) c v)) (v : V) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map P.comparison.hom (ChartEndomorphismDerivative.Abelian.chartExponential (E := ContinuousPresentedPeriods.Abelian.abelianSchemeNativeModel A) c v) =
      AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization P.variety ((IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus P.variety).proj (T v)) := by
  let : T2Space (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.variety.toOver) :=
    P.variety.variety.presentation.complexPoints_t2Space
  let : IsMonHom P.comparison.hom := P.comparison_group
  have h := IntrinsicDerivativeConjugation.Abelian.nativeSchemeIsoTangent_exp P.comparison
    (ChartEndomorphismDerivative.Abelian.chartTangentMap (E := ContinuousPresentedPeriods.Abelian.abelianSchemeNativeModel A) c v)
  have hd := congrArg
    (fun D : ContinuousPresentedPeriods.Abelian.abelianSchemeNativeModel A →L[ℝ] AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel P.variety =>
      D (ChartEndomorphismDerivative.Abelian.chartTangentMap (E := ContinuousPresentedPeriods.Abelian.abelianSchemeNativeModel A) c v))
    (IntrinsicDerivativeConjugation.Abelian.nativeSchemeIsoTangent_real P.comparison)
  change _ = AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.variety.toOver) (T v)
  exact h.trans (congrArg (AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.variety.toOver))
    (hd.symm.trans (hT v).symm))

theorem _root_.OAI.ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation.chart_divided_period_eq_marked
    {Index : Type} [Fintype Index]
    (P : StandardModuli.Abelian.ComplexAbelianPresentation A)
    (c : OpenPartialHomeomorph (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme) V)
    (T : V ≃L[ℂ] AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel P.variety)
    (hT : ∀ v, T v = mfderiv (𝓘(ℝ, ContinuousPresentedPeriods.Abelian.abelianSchemeNativeModel A))
      (𝓘(ℝ, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel P.variety)) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map P.comparison.hom) 1
        (ChartEndomorphismDerivative.Abelian.chartTangentMap (E := ContinuousPresentedPeriods.Abelian.abelianSchemeNativeModel A) c v))
    (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index P.variety) (r : (Index → ℝ) →ₗ[ℝ] V)
    (hb : ∀ i, (b i : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel P.variety) = T (r (Pi.single i 1)))
    (n : ℕ) (z : Index → ℤ) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map P.comparison.hom
        (ChartEndomorphismDerivative.Abelian.chartExponential (E := ContinuousPresentedPeriods.Abelian.abelianSchemeNativeModel A) c
          ((n : ℝ)⁻¹ • r (fun i => (z i : ℝ)))) =
      AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization P.variety ((IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus P.variety).proj
        (MarkedAbelianPeriods.IntrinsicPeriods.periodMap b (fun i => (((n : ℝ)⁻¹ * (z i : ℝ) : ℝ) : ℂ)))) := by
  rw [StandardModuli.Abelian.ComplexAbelianPresentation.chart_exponential_eq_presented_period P c T hT,
    periodMap_eq_realFrame b T r hb]
  congr 3
  exact (r.map_smul (n : ℝ)⁻¹ (fun i => (z i : ℝ))).symm

end ComplexAbelianPresentation

end

end OAI.ArithmeticGeometry.Descent.CMVariety.PresentedTorsionPeriods.Abelian
