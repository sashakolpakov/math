import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.PresentedTangents

/-! # Frame Tangent Comparison -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The real tangent identification in the fixed-torus transport is
the same original derivative used in the holomorphic native period matrices. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

local instance FrameTangentComparison.frameTangentComparison_varietyIntegral (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance FrameTangentComparison.frameTangentComparison_varietySmooth (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x}

variable (F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C)

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedChartTangent_derivative (z : Intrinsic.FamilyFrames.FamilyChartBase C) (hz : z ∈ C.charts.charts.neighborhood)
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C z)) (v : Intrinsic.FamilyFrames.FamilyChartTangent C) :
    let : ∀ w : Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C w).scheme.left := F.integral
    F.presentedChartTangent z hz P v =
      mfderiv (𝓘(ℝ, Intrinsic.FamilyFrames.FamilyChartModel C z)) (𝓘(ℝ, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel P.variety))
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map P.comparison.hom) 1
        (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartTangentMap (E := Intrinsic.FamilyFrames.FamilyChartModel C z) (F.charts z) v) := by
  let : ∀ w : Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C w).scheme.left := F.integral
  exact (congrArg (fun T : Intrinsic.FamilyFrames.FamilyChartModel C z →L[ℝ] AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel P.variety =>
    T (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartTangentMap (E := Intrinsic.FamilyFrames.FamilyChartModel C z) (F.charts z) v))
      (ArithmeticGeometry.Descent.CMVariety.IntrinsicDerivativeConjugation.Abelian.nativeSchemeIsoTangent_real P.comparison)).symm

end

end OAI.RepresentationTheory.Theta.Geometric
