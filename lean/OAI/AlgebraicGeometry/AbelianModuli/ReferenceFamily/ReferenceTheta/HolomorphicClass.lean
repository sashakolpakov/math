import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicFrameComparison
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceTheta.ConnectionCech

/-! # Holomorphic Class -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The actual algebraic theta bundle has the holomorphic unit class
computed by its original theta-frame logarithms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

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

local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaHolomorphicClass_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaHolomorphicClass_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaHolomorphicClass_eq_logarithmic :
    Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass M.abelian.variety (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left) =
      Holomorphic.LogUnitClass.holomorphicLogUnitClass (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
        (M.thetaChernCover U V f g hf hg) (M.thetaChernLogCech U V f g hf hg)
        (M.thetaChernLogCech_holomorphic U V f g hf hg) (M.thetaChernLogCech_cocycle U V f g hf hg)
        (M.thetaChernLogRefinement U V f g hf hg).covers := by
  apply Intrinsic.HolomorphicFrameComparison.nativeHolomorphicLineClass_eq_frameCech M.abelian.variety (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left)
    (M.thetaChernCover U V f g hf hg) (M.thetaChernLogRefinement U V f g hf hg).covers
    (fun i => ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left i.2) (M.thetaChernLogRefinement U V f g hf hg).subset
    (Holomorphic.LogUnitClass.holomorphicLogUnitCech _ _ _ _ (M.thetaChernLogCech_holomorphic U V f g hf hg))
    (Holomorphic.LogUnitClass.holomorphicLogUnitCech_closed _ _ _ _ (M.thetaChernLogCech_holomorphic U V f g hf hg)
      (M.thetaChernLogCech_cocycle U V f g hf hg))
  intro a x
  exact M.thetaChernLogCech_exp U V f g hf hg a x

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
