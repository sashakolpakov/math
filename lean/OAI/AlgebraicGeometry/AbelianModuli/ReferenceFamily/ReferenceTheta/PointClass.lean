import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceTheta.TranslationClassComparison
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicPointLine

/-! # Point Class -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The original algebraic difference bundle at a native period point
has exactly the computed theta translation class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Reference.Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : Reference.AlgebraicModel.ReferenceAlgebraicModel F hP) (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (F.polarizationFactor hP))
    (f : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (g : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hf : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t))
    (hg : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t))

local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaPointClass_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaPointClass_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

include hf hg in
theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaPointDifference_holomorphicClass (hdeg : V.degree = U.degree + 1)
    (a : F.periodData.space) :
    Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass M.abelian.variety
      (IntrinsicPointLine.nativePointFamilyLine (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left))
        (M.vectorPeriod a)) = M.translationHolomorphicClass (-a) := by
  have h := congrArg (Intrinsic.HolomorphicIsoClass.nativeHolomorphicPicardClass M.abelian.variety)
    (IntrinsicPointLine.nativePointDifference_class M.abelianScheme (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left) (M.vectorPeriod a))
  exact h.trans (M.nativeThetaTranslationClass_eq U V f g hf hg hdeg a)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
