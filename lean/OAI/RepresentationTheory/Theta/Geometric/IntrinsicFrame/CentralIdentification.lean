import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.EndomorphismTransport
import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.TorusMap

/-! # Central Identification -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The fixed-torus maps at the center are the original central fiber
identification, including the actual central endomorphism action. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x}

local instance IntrinsicFrame.CentralIdentification.nativeFrameCentralIdentification_nativeRealLieGroup (z : Intrinsic.FamilyFrames.FamilyChartBase C)
    [IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C z).scheme.left] :
    LieGroup (𝓘(ℝ, Intrinsic.FamilyFrames.FamilyChartModel C z)) ∞ (Intrinsic.FamilyFrames.FamilyChartPoints C z) :=
  ArithmeticGeometry.Descent.CMVariety.IntrinsicFiberLieGroup.Abelian.nativeScheme_realLieGroup (Intrinsic.FamilyFrames.familyChartFiber C z).scheme

variable (F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C)

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.torusFiberMap_center
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C (Intrinsic.FamilyFrames.familyChartCenter C))) (t : F.CentralTorus) :
    F.torusFiberMap (Intrinsic.FamilyFrames.familyChartCenter C) F.center t = F.centralTorusHomeomorph P t := by
  let : ∀ z : Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C z).scheme.left := F.integral
  let : ∀ z : Intrinsic.FamilyFrames.FamilyChartBase C, T2Space (Intrinsic.FamilyFrames.FamilyChartPoints C z) := F.t2
  induction t using Quotient.inductionOn with
  | h v =>
    change (F.transportedExponential (Intrinsic.FamilyFrames.familyChartCenter C) v).toMul = _
    rw [F.transportedExponential_apply, F.centralTorusHomeomorph_mk, F.realTransport_central]

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedTorusMap_center
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C (Intrinsic.FamilyFrames.familyChartCenter C))) (t : F.CentralTorus) :
    F.presentedTorusMap (Intrinsic.FamilyFrames.familyChartCenter C) F.center P t =
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map P.comparison.hom (F.centralTorusHomeomorph P t) :=
  congrArg (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map P.comparison.hom) (F.torusFiberMap_center P t)

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.centralTorusEndomorphism_square
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C (Intrinsic.FamilyFrames.familyChartCenter C)))
    (k : G.scheme ⟶ G.scheme) (t : F.CentralTorus) :
    F.torusFiberMap (Intrinsic.FamilyFrames.familyChartCenter C) F.center (F.centralTorusEndomorphism P k t) =
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism S G k (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)))
        (F.torusFiberMap (Intrinsic.FamilyFrames.familyChartCenter C) F.center t) := by
  rw [F.torusFiberMap_center P, F.torusFiberMap_center P]
  exact (F.centralTorusHomeomorph P).apply_symm_apply _

end

end OAI.RepresentationTheory.Theta.Geometric
