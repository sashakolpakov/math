import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CurvatureD
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.IntegrationCechTotal
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalCechClass
import OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothCechComparison

/-! # Curvature Integration -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CurvatureIntegration

noncomputable section

/-! Actual integration takes the normalized metric curvature to the original rational singular Chern class. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothCechComparison
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [CompactSpace M] [T2Space M]
  [IsManifold 𝓘(ℂ, E) ∞ M] (u : Connecting.holomorphicUnitCohomology E M)

theorem holomorphicLineRationalDefectCocycle_integration :
    AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (ComplexMultiplication.HodgeComparison.IntegrationCechTotal.CM.Construction.manifoldIntegrationCechTotalMap E M (Singular.holomorphicLogCover E M u)) 2
      (CurvatureD.holomorphicLineRationalDefectCocycle u) =
    ComplexMultiplication.HodgeComparison.RationalCohomologyMap.CM.Construction.rationalComplexCocycleMap (ComplexMultiplication.HodgeComparison.RationalSmoothCechAugmentation.CM.Construction.rationalSmoothCechTotalMap E M (Singular.holomorphicLogCover E M u)) 2
      (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (Cech.Obj.RationalCech.locallyConstantCechToTotal (TopCat.of M) (Singular.holomorphicLogCover E M u)) 2
        (LogCech.RationalCech.logDefectCocycle (TopCat.of M) (Singular.holomorphicLogCover E M u)
          (Singular.holomorphicLogCech E M u) (Singular.holomorphicLogCech_cocycle E M u))) := by
  apply Subtype.ext
  exact ComplexMultiplication.HodgeComparison.IntegrationCechTotal.CM.Construction.manifoldIntegrationCechTotalMap_rational E M (Singular.holomorphicLogCover E M u) 2
    (LogCech.RationalCech.logDefectCech (TopCat.of M) (Singular.holomorphicLogCover E M u)
      (Singular.holomorphicLogCech E M u) (Singular.holomorphicLogCech_cocycle E M u))

theorem holomorphicLine_curvature_smooth_chern :
    HomologicalComplex.homologyMap (AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap E M) 2
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M) 2 (CurvatureD.holomorphicLineCurvatureCocycle u)) =
    ComplexMultiplication.HodgeComparison.RationalCohomologyMap.CM.Construction.rationalComplexCohomologyMap (ComplexMultiplication.HodgeComparison.RationalSmoothCech.CM.Construction.rationalSmoothCochainMap E M) 2 (Singular.holomorphicFirstChernClassQ E M u) := by
  let U := Singular.holomorphicLogCover E M u
  let e := AlgebraicTopology.Cohomology.Singular.ManifoldSmoothCechComparison.manifoldSmoothCechCohomologyIso E M U (Singular.holomorphicLogCover_covers E M u) 2
  apply e.toLinearEquiv.injective
  have hmap := congrArg (fun k => HomologicalComplex.homologyMap k 2)
    (ComplexMultiplication.HodgeComparison.IntegrationCechTotal.CM.Construction.manifoldIntegrationCechTotalMap_global E M U)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hmap
  have hglobal := ConcreteCategory.congr_hom hmap
    (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M) 2 (CurvatureD.holomorphicLineCurvatureCocycle u))
  have haug := AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechAugmentationToTotal (E := E) U) 2 (CurvatureD.holomorphicLineCurvatureCocycle u)
  have hcurv := CurvatureD.holomorphicLine_curvature_total_class u
  have hdef := AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality (ComplexMultiplication.HodgeComparison.IntegrationCechTotal.CM.Construction.manifoldIntegrationCechTotalMap E M U) 2 (CurvatureD.holomorphicLineRationalDefectCocycle u)
  have hrat := ComplexMultiplication.HodgeComparison.RationalCechClass.CM.Construction.rationalSmoothCechClass_of_cocycle E M U (Singular.holomorphicLogCover_covers E M u) 2
    (LogCech.RationalCech.logDefectCocycle (TopCat.of M) U (Singular.holomorphicLogCech E M u) (Singular.holomorphicLogCech_cocycle E M u))
  exact hglobal.symm.trans
    ((congrArg (HomologicalComplex.homologyMap (ComplexMultiplication.HodgeComparison.IntegrationCechTotal.CM.Construction.manifoldIntegrationCechTotalMap E M U) 2)
      (haug.trans hcurv)).trans
      (hdef.trans ((congrArg (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.SmoothCechDoubleComplex.manifoldSmoothCechTotal E M U (ModuleCat.of ℂ ℂ)) 2)
        (holomorphicLineRationalDefectCocycle_integration u)).trans hrat.symm)))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CurvatureIntegration
