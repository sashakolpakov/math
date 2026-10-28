import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceTheta.CurvatureClass
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.IntegrationCechTotal
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalCechClass
import OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothCechComparison

/-! # Chern Integration -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Actual integration carries the normalized original curvature to
the smooth-singular image of the original native algebraic Chern class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothCechComparison
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

local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaIntegration_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaIntegration_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaRationalDefectCocycle_integration (hdeg : V.degree = U.degree + 1) :
    AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (ComplexMultiplication.HodgeComparison.IntegrationCechTotal.CM.Construction.manifoldIntegrationCechTotalMap (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) (M.thetaChernCover U V f g hf hg)) 2
      (M.nativeThetaRationalDefectCocycle U V f g hf hg hdeg) =
    ComplexMultiplication.HodgeComparison.RationalCohomologyMap.CM.Construction.rationalComplexCocycleMap (ComplexMultiplication.HodgeComparison.RationalSmoothCechAugmentation.CM.Construction.rationalSmoothCechTotalMap (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) (M.thetaChernCover U V f g hf hg)) 2
      (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantCechToTotal
        (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) (M.thetaChernCover U V f g hf hg)) 2
        (DivisorClass.Chern.LogCech.RationalCech.logDefectCocycle (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
          (M.thetaChernCover U V f g hf hg) (M.thetaChernLogCech U V f g hf hg)
          (M.thetaChernLogCech_cocycle U V f g hf hg))) := by
  apply Subtype.ext
  exact ComplexMultiplication.HodgeComparison.IntegrationCechTotal.CM.Construction.manifoldIntegrationCechTotalMap_rational (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) (M.thetaChernCover U V f g hf hg) 2
    (DivisorClass.Chern.LogCech.RationalCech.logDefectCech (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
      (M.thetaChernCover U V f g hf hg) (M.thetaChernLogCech U V f g hf hg)
      (M.thetaChernLogCech_cocycle U V f g hf hg))

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeTheta_curvature_smooth_logclass (hdeg : V.degree = U.degree + 1) :
    HomologicalComplex.homologyMap (AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 2
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 2
        M.nativeThetaCurvatureCocycle) =
    ComplexMultiplication.HodgeComparison.RationalCohomologyMap.CM.Construction.rationalComplexCohomologyMap (ComplexMultiplication.HodgeComparison.RationalSmoothCech.CM.Construction.rationalSmoothCochainMap (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 2
      (DivisorClass.Chern.LogCech.RationalCech.logarithmicSingularClass (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
        (M.thetaChernCover U V f g hf hg) (M.thetaChernLogRefinement U V f g hf hg).covers
        (M.thetaChernLogCech U V f g hf hg) (M.thetaChernLogCech_cocycle U V f g hf hg)) := by
  let W := M.thetaChernCover U V f g hf hg
  let T := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver
  let A := RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian
  let e := AlgebraicTopology.Cohomology.Singular.ManifoldSmoothCechComparison.manifoldSmoothCechCohomologyIso A T W (M.thetaChernLogRefinement U V f g hf hg).covers 2
  apply e.toLinearEquiv.injective
  have hmap := congrArg (fun k => HomologicalComplex.homologyMap k 2)
    (ComplexMultiplication.HodgeComparison.IntegrationCechTotal.CM.Construction.manifoldIntegrationCechTotalMap_global A T W)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hmap
  have hglobal := ConcreteCategory.congr_hom hmap
    (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex A T) 2 M.nativeThetaCurvatureCocycle)
  have haug := AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechAugmentationToTotal (E := A) W) 2 M.nativeThetaCurvatureCocycle
  have hcurv := M.nativeTheta_curvature_total_class U V f g hf hg hdeg
  have hdef := AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality (ComplexMultiplication.HodgeComparison.IntegrationCechTotal.CM.Construction.manifoldIntegrationCechTotalMap A T W) 2
    (M.nativeThetaRationalDefectCocycle U V f g hf hg hdeg)
  have hrat := ComplexMultiplication.HodgeComparison.RationalCechClass.CM.Construction.rationalSmoothCechClass_of_cocycle A T W
    (M.thetaChernLogRefinement U V f g hf hg).covers 2
    (DivisorClass.Chern.LogCech.RationalCech.logDefectCocycle (TopCat.of T) W
      (M.thetaChernLogCech U V f g hf hg) (M.thetaChernLogCech_cocycle U V f g hf hg))
  exact hglobal.symm.trans
    ((congrArg (HomologicalComplex.homologyMap (ComplexMultiplication.HodgeComparison.IntegrationCechTotal.CM.Construction.manifoldIntegrationCechTotalMap A T W) 2)
      (haug.trans hcurv)).trans
      (hdef.trans ((congrArg (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.SmoothCechDoubleComplex.manifoldSmoothCechTotal A T W (ModuleCat.of ℂ ℂ)) 2)
        (M.nativeThetaRationalDefectCocycle_integration U V f g hf hg hdeg)).trans hrat.symm)))

include hf hg in
theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaChern_curvature_integration (hdeg : V.degree = U.degree + 1) :
    HomologicalComplex.homologyMap (AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 2
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 2
        M.nativeThetaCurvatureCocycle) =
    ComplexMultiplication.HodgeComparison.RationalCohomologyMap.CM.Construction.rationalComplexCohomologyMap (ComplexMultiplication.HodgeComparison.RationalSmoothCech.CM.Construction.rationalSmoothCochainMap (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 2
      (Intrinsic.ChernClasses.lineBundleChernClass M.abelian.variety.presentation (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left)) :=
  (M.nativeTheta_curvature_smooth_logclass U V f g hf hg hdeg).trans
    (congrArg (ComplexMultiplication.HodgeComparison.RationalCohomologyMap.CM.Construction.rationalComplexCohomologyMap (ComplexMultiplication.HodgeComparison.RationalSmoothCech.CM.Construction.rationalSmoothCochainMap (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 2) (M.thetaChernClass_eq_logarithmic U V f g hf hg).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
