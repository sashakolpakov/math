import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntegralDualModel
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.TranslationClassComparison
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicPointLine

/-! # Point Class -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! The original algebraic difference bundle at a native period point
has exactly the computed theta translation class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicPointLine

variable {dim : ℕ} {matrix : DefinitionsIntegral.IntegralMatrix dim}
    {F : DefinitionsIntegral.MarkedPolarizedTorus dim matrix} {hP : matrix.transpose = -matrix}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel F) (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (F.polarizationFactor hP))
    (f : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (g : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hf : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t))
    (hg : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t))

local instance PeriodModel.Geometric.AlgebraicPeriodModel.thetaPointClass_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance PeriodModel.Geometric.AlgebraicPeriodModel.thetaPointClass_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

include hf hg in
theorem PeriodModel.Geometric.AlgebraicPeriodModel.thetaPointDifference_holomorphicClass (hdeg : V.degree = U.degree + 1)
    (a : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) :
    AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass M.abelian.variety
      (AbelianModuli.ReferenceFamily.IntrinsicPointLine.nativePointFamilyLine (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left))
        (M.vectorPeriod a)) = M.translationHolomorphicClass (-a) := by
  have h := congrArg (AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicIsoClass.nativeHolomorphicPicardClass M.abelian.variety)
    (AbelianModuli.ReferenceFamily.IntrinsicPointLine.nativePointDifference_class M.abelianScheme (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left) (M.vectorPeriod a))
  exact h.trans (M.nativeThetaTranslationClass_eq U V f g hf hg hdeg a)

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
