import OAI.RepresentationTheory.Theta.Geometric.FrameTangentComparison
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.FrameRationalEquiv
import OAI.RepresentationTheory.Theta.Geometric.Period.VarietyMarkedAbelianPeriods

/-! # Frame Marking Transport -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Native frame transport carries the actual central marking to the
same marking used by the constructed holomorphic family period matrices. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.Manifold ContDiff

local instance FrameMarkingTransport.frameMarkingTransport_varietyIntegral (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance FrameMarkingTransport.frameMarkingTransport_varietySmooth (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x}

variable (F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C)

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.realTransport_periods (z : Intrinsic.FamilyFrames.FamilyChartBase C) (v : Fin F.rank → ℝ) :
    F.realTransport z (F.periods (Intrinsic.FamilyFrames.familyChartCenter C) v) = F.periods z v :=
  congrArg (F.periods z) ((F.periods (Intrinsic.FamilyFrames.familyChartCenter C)).symm_apply_apply v)

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.nativeRealTransport_marked_vector (z : Intrinsic.FamilyFrames.FamilyChartBase C) (hzN : z ∈ C.charts.charts.neighborhood)
    (P₀ : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C (Intrinsic.FamilyFrames.familyChartCenter C)))
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C z))
    (T₀ : Intrinsic.FamilyFrames.FamilyChartTangent C ≃L[ℂ] AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel P₀.variety)
    (T : Intrinsic.FamilyFrames.FamilyChartTangent C ≃L[ℂ] AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel P.variety)
    (h₀ : ∀ v, T₀ v = F.presentedChartTangent (Intrinsic.FamilyFrames.familyChartCenter C) (Family.ChartOpenImage.familyChartCenter_mem C) P₀ v)
    (hz : ∀ v, T v = F.presentedChartTangent z hzN P v) (v : Fin F.rank → ℝ) :
    F.nativeRealTransport z hzN P₀ P (T₀ (F.periods (Intrinsic.FamilyFrames.familyChartCenter C) v)) = T (F.periods z v) := by
  change F.presentedChartTangent z hzN P
    (F.realTransport z ((F.presentedChartTangent (Intrinsic.FamilyFrames.familyChartCenter C) (Family.ChartOpenImage.familyChartCenter_mem C) P₀).symm
      (T₀ (F.periods (Intrinsic.FamilyFrames.familyChartCenter C) v)))) = _
  rw [h₀, ContinuousLinearEquiv.symm_apply_apply, F.realTransport_periods, ← hz]

end

end OAI.RepresentationTheory.Theta.Geometric
