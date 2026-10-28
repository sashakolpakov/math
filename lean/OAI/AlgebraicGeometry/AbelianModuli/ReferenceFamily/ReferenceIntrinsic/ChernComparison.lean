import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceTheta.ChernIntegration
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceTheta.Embedding
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveCurvatureIntegration

/-! # Chern Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The original reference curvature represents the actual ample
algebraic Chern class under the original native de Rham-Betti comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Reference.Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : Reference.AlgebraicModel.ReferenceAlgebraicModel F hP)

local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeChernComparison_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeChernComparison_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

def Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaClosedForm :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) 2 :=
  ⟨M.nativeThetaNormalizedCurvature, M.nativeThetaNormalizedCurvature_closed⟩

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaChern_comparison
    (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (F.polarizationFactor hP))
    (f : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (g : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hf : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t))
    (hg : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t))
    (hdeg : V.degree = U.degree + 1) :
    (M.abelian.variety.deRhamBettiIso 2).hom
      (M.abelian.variety.deRhamClass 2 M.nativeThetaClosedForm) =
      M.abelian.variety.rationalCohomologyInclusion 2
        (Intrinsic.ChernClasses.lineBundleChernClass M.abelian.variety.presentation (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left)) := by
  apply (M.abelian.variety.deRhamBettiIso_apply_eq_iff 2 _ _).mpr
  have h := M.nativeThetaChern_curvature_integration U V f g hf hg hdeg
  have hform := M.abelian.variety.deRhamToSmoothSingular_formClass 2 M.nativeThetaClosedForm
  have hnat := AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality
    (AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 2
    M.nativeThetaCurvatureCocycle
  exact hform.trans (hnat.symm.trans (h.trans
    (ComplexMultiplication.HodgeComparison.ProjectiveCurvatureIntegration.CM.Construction.rationalSmoothCohomologyMap_eq M.abelian.variety 2
      (Intrinsic.ChernClasses.lineBundleChernClass M.abelian.variety.presentation (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left)))))

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.exists_ample_native_chern :
    ∃ L : HilbertConstruction.Line.Bundles.LineBundle M.abelian.toOver.left, L.IsAmple ∧
      (M.abelian.variety.deRhamBettiIso 2).hom
        (M.abelian.variety.deRhamClass 2 M.nativeThetaClosedForm) =
      M.abelian.variety.rationalCohomologyInclusion 2 (Intrinsic.ChernClasses.lineBundleChernClass M.abelian.variety.presentation L) := by
  obtain ⟨U, V, f, g, _, hdeg, _, _, _, _, _, _, hf, hg, _, hamp⟩ := M.exists_ample_theta_quotient
  exact ⟨RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left, hamp, M.nativeThetaChern_comparison U V f g hf hg hdeg⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
