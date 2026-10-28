import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.TorusMap
import OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicDerivativeConjugation
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Torsion

/-! # Presented Tangents -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The exact derivative of the original fiber presentation converts
the chart period frame to native tangent coordinates and exponentials. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped Classical _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

open OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicDerivativeConjugation.Abelian

local instance IntrinsicFrame.PresentedTangents.nativeFramePresentedTangents_varietyIntegral (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance IntrinsicFrame.PresentedTangents.nativeFramePresentedTangents_varietySmooth (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x}

local instance IntrinsicFrame.PresentedTangents.nativeFramePresentedTangents_nativeRealLieGroup (z : Intrinsic.FamilyFrames.FamilyChartBase C)
    [IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C z).scheme.left] :
    LieGroup (𝓘(ℝ, Intrinsic.FamilyFrames.FamilyChartModel C z)) ∞ (Intrinsic.FamilyFrames.FamilyChartPoints C z) :=
  ArithmeticGeometry.Descent.CMVariety.IntrinsicFiberLieGroup.Abelian.nativeScheme_realLieGroup (Intrinsic.FamilyFrames.familyChartFiber C z).scheme

variable (F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C)

def Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedChartTangent (z : Intrinsic.FamilyFrames.FamilyChartBase C) (hz : z ∈ C.charts.charts.neighborhood)
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C z)) :
    Intrinsic.FamilyFrames.FamilyChartTangent C ≃L[ℝ] AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel P.variety := by
  let : ∀ w : Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C w).scheme.left := F.integral
  let : ∀ w : Intrinsic.FamilyFrames.FamilyChartBase C, T2Space (Intrinsic.FamilyFrames.FamilyChartPoints C w) := F.t2
  have hc := F.chartData z hz
  exact (ArithmeticGeometry.Descent.CMVariety.ChartPeriodLattice.Abelian.chartTangentEquiv (F.charts z) hc.2.2.1 hc.1 hc.2.1).trans
    ((ArithmeticGeometry.Descent.CMVariety.IntrinsicDerivativeConjugation.Abelian.nativeSchemeIsoTangent P.comparison).toLinearEquiv.restrictScalars ℝ).toContinuousLinearEquiv

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedChartTangent_exp (z : Intrinsic.FamilyFrames.FamilyChartBase C) (hz : z ∈ C.charts.charts.neighborhood)
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C z)) (v : Intrinsic.FamilyFrames.FamilyChartTangent C) :
    let : ∀ w : Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C w).scheme.left := F.integral
    let : ∀ w : Intrinsic.FamilyFrames.FamilyChartBase C, T2Space (Intrinsic.FamilyFrames.FamilyChartPoints C w) := F.t2
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map P.comparison.hom
      (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (G := Intrinsic.FamilyFrames.FamilyChartPoints C z) (E := Intrinsic.FamilyFrames.FamilyChartModel C z) (F.charts z) v) =
        AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.variety.toOver) (F.presentedChartTangent z hz P v) := by
  let : ∀ w : Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C w).scheme.left := F.integral
  let : ∀ w : Intrinsic.FamilyFrames.FamilyChartBase C, T2Space (Intrinsic.FamilyFrames.FamilyChartPoints C w) := F.t2
  exact ArithmeticGeometry.Descent.CMVariety.IntrinsicDerivativeConjugation.Abelian.nativeSchemeIsoTangent_exp P.comparison (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartTangentMap (E := Intrinsic.FamilyFrames.FamilyChartModel C z) (F.charts z) v)

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedChartTangent_lattice (z : Intrinsic.FamilyFrames.FamilyChartBase C) (hz : z ∈ C.charts.charts.neighborhood)
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C z)) (v : Intrinsic.FamilyFrames.FamilyChartTangent C) :
    let : ∀ w : Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C w).scheme.left := F.integral
    let : ∀ w : Intrinsic.FamilyFrames.FamilyChartBase C, T2Space (Intrinsic.FamilyFrames.FamilyChartPoints C w) := F.t2
    F.presentedChartTangent z hz P v ∈ AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice P.variety ↔
      v ∈ ArithmeticGeometry.Descent.CMVariety.ChartPeriodLattice.Abelian.chartPeriodLattice (G := Intrinsic.FamilyFrames.FamilyChartPoints C z) (E := Intrinsic.FamilyFrames.FamilyChartModel C z) (F.charts z) := by
  let : ∀ w : Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C w).scheme.left := F.integral
  let : ∀ w : Intrinsic.FamilyFrames.FamilyChartBase C, T2Space (Intrinsic.FamilyFrames.FamilyChartPoints C w) := F.t2
  change AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.variety.toOver) (F.presentedChartTangent z hz P v) = 1 ↔ _
  rw [← F.presentedChartTangent_exp z hz P v]
  have h1 : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map P.comparison.hom 1 = 1 := MonObj.one_comp P.comparison.hom
  rw [← h1]
  exact (ArithmeticGeometry.Descent.CMVariety.IntrinsicDerivativeConjugation.Abelian.nativeSchemeIsoHomeomorph P.comparison).injective.eq_iff

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedTorusMap_mk (z : Intrinsic.FamilyFrames.FamilyChartBase C) (hz : z ∈ F.neighborhood)
    (hzN : z ∈ C.charts.charts.neighborhood)
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C z)) (v : Intrinsic.FamilyFrames.FamilyChartTangent C) :
    F.presentedTorusMap z hz P (QuotientAddGroup.mk v) =
      AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.e06Input P.variety
        (QuotientAddGroup.mk (F.presentedChartTangent z hzN P (F.realTransport z v))) := by
  let : ∀ w : Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C w).scheme.left := F.integral
  let : ∀ w : Intrinsic.FamilyFrames.FamilyChartBase C, T2Space (Intrinsic.FamilyFrames.FamilyChartPoints C w) := F.t2
  exact F.presentedChartTangent_exp z hzN P (F.realTransport z v)

end

end OAI.RepresentationTheory.Theta.Geometric
