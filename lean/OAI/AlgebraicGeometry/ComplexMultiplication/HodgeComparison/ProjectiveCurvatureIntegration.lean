import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveCurvatureDefect
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.IntegrationCechTotal
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalCechClass
import OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothCechComparison
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalIntegrationDefect

/-! # Projective Curvature Integration -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveCurvatureIntegration.CM.Construction

noncomputable section

section

/-! The actual projective curvature integrates to the smooth singular
image of the rational logarithmic class. -/

open _root_.CategoryTheory _root_.TopologicalSpace Set
open OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothCechComparison
open scoped _root_.Manifold ContDiff

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M] [NormalSpace M]
  {ι : Type} [Fintype ι]
  (p : M → Projectivization ℂ (ι → ℂ)) (hp : Continuous p)
  (hhol : ∀ i, ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ι → ℂ) ∞
    (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart p i) (ProjectiveGluing.CM.Construction.projectiveLiftDomain p hp i : Set M))

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

theorem projectiveRationalDefectCocycle_integration :
    AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (IntegrationCechTotal.CM.Construction.manifoldIntegrationCechTotalMap E M (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol)) 2
      (ProjectiveCurvatureDefect.CM.Construction.projectiveRationalDefectCocycle p hp hhol) =
    RationalCohomologyMap.CM.Construction.rationalComplexCocycleMap (RationalSmoothCechAugmentation.CM.Construction.rationalSmoothCechTotalMap E M (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol)) 2
      (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap
        (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantCechToTotal (TopCat.of M) (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol)) 2
        (DivisorClass.Chern.LogCech.RationalCech.logDefectCocycle (TopCat.of M) (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol)
          (ProjectiveChernCocycle.CM.Construction.projectiveLogCech p hp hhol) (ProjectiveChernCocycle.CM.Construction.projectiveLogCech_cocycle p hp hhol))) := by
  apply Subtype.ext
  exact IntegrationCechTotal.CM.Construction.manifoldIntegrationCechTotalMap_rational E M (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol) 2
    (DivisorClass.Chern.LogCech.RationalCech.logDefectCech (TopCat.of M) (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol)
      (ProjectiveChernCocycle.CM.Construction.projectiveLogCech p hp hhol) (ProjectiveChernCocycle.CM.Construction.projectiveLogCech_cocycle p hp hhol))

theorem projective_curvature_smooth_class :
    HomologicalComplex.homologyMap (AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap E M) 2
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M) 2 (ProjectiveCurvatureDefect.CM.Construction.projectiveCurvatureCocycle p hp hhol)) =
    RationalCohomologyMap.CM.Construction.rationalComplexCohomologyMap (RationalSmoothCech.CM.Construction.rationalSmoothCochainMap E M) 2
      (ProjectiveChernCocycle.CM.Construction.projectiveLogarithmicClassQ p hp hhol) := by
  let U := ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol
  let e := AlgebraicTopology.Cohomology.Singular.ManifoldSmoothCechComparison.manifoldSmoothCechCohomologyIso E M U (ProjectiveLogarithmicCover.CM.Construction.projectiveLogRefinement p hp hhol).covers 2
  apply e.toLinearEquiv.injective
  have hmap := congrArg (fun f => HomologicalComplex.homologyMap f 2)
    (IntegrationCechTotal.CM.Construction.manifoldIntegrationCechTotalMap_global E M U)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hmap
  have hglobal := ConcreteCategory.congr_hom hmap
    (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M) 2 (ProjectiveCurvatureDefect.CM.Construction.projectiveCurvatureCocycle p hp hhol))
  have haug := AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechAugmentationToTotal (E := E) U) 2
    (ProjectiveCurvatureDefect.CM.Construction.projectiveCurvatureCocycle p hp hhol)
  have hcurv := ProjectiveCurvatureDefect.CM.Construction.projective_curvature_total_class p hp hhol
  have hdef := AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality (IntegrationCechTotal.CM.Construction.manifoldIntegrationCechTotalMap E M U) 2
    (ProjectiveCurvatureDefect.CM.Construction.projectiveRationalDefectCocycle p hp hhol)
  have hrat := RationalCechClass.CM.Construction.rationalSmoothCechClass_of_cocycle E M U
    (ProjectiveLogarithmicCover.CM.Construction.projectiveLogRefinement p hp hhol).covers 2
    (DivisorClass.Chern.LogCech.RationalCech.logDefectCocycle (TopCat.of M) U
      (ProjectiveChernCocycle.CM.Construction.projectiveLogCech p hp hhol) (ProjectiveChernCocycle.CM.Construction.projectiveLogCech_cocycle p hp hhol))
  exact hglobal.symm.trans
    ((congrArg (HomologicalComplex.homologyMap (IntegrationCechTotal.CM.Construction.manifoldIntegrationCechTotalMap E M U) 2)
      (haug.trans hcurv)).trans
      (hdef.trans ((congrArg (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.SmoothCechDoubleComplex.manifoldSmoothCechTotal E M U (ModuleCat.of ℂ ℂ)) 2)
        (projectiveRationalDefectCocycle_integration p hp hhol)).trans hrat.symm)))

end

/-! The Fubini–Study form of every actual projective variety represents
the rational singular class constructed from its coordinate transition logs. -/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothCechComparison

theorem rationalSmoothCohomologyMap_eq (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ)
    (a : V.rationalCohomology n) :
    RationalCohomologyMap.CM.Construction.rationalComplexCohomologyMap (RationalSmoothCech.CM.Construction.rationalSmoothCochainMap V.analyticModel V.analyticSpace) n a =
      V.rationalToSmoothSingular n a := by
  obtain ⟨c, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_surjective (ModuleCat.of ℚ ℚ) (Betti.Scheme.schemePointSpace V.toOver) n a
  have h := RationalCohomologyMap.CM.Construction.rationalComplexCohomologyMap_class
    (RationalSmoothCech.CM.Construction.rationalSmoothCochainMap V.analyticModel V.analyticSpace) n c
  exact h.trans (RationalIntegrationDefect.CM.Construction.rationalSmoothCocycle_class V n c)

def fubiniStudyClassQ (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : V.rationalCohomology 2 :=
  ProjectiveChernCocycle.CM.Construction.projectiveLogarithmicClassQ (ProjectiveScheme.CM.Construction.projectiveEmbeddingCoordinates V)
    (ProjectiveScheme.CM.Construction.projectiveEmbeddingCoordinates_continuous V) (IntrinsicProjectiveCharts.CM.Construction.projectiveEmbeddingCoordinates_holomorphic V)

def fubiniStudyClosedForm (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 2 :=
  ⟨IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V, IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm_closed V⟩

theorem fubiniStudyClassQ_comparison (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    (V.deRhamBettiIso 2).hom (V.deRhamClass 2 (fubiniStudyClosedForm V)) =
      V.rationalCohomologyInclusion 2 (fubiniStudyClassQ V) := by
  apply (V.deRhamBettiIso_apply_eq_iff 2 _ _).mpr
  have h := projective_curvature_smooth_class (ProjectiveScheme.CM.Construction.projectiveEmbeddingCoordinates V)
    (ProjectiveScheme.CM.Construction.projectiveEmbeddingCoordinates_continuous V) (IntrinsicProjectiveCharts.CM.Construction.projectiveEmbeddingCoordinates_holomorphic V)
  have hform := V.deRhamToSmoothSingular_formClass 2 (fubiniStudyClosedForm V)
  have hnat := AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality
    (AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap V.analyticModel V.analyticSpace) 2
    (ProjectiveCurvatureDefect.CM.Construction.projectiveCurvatureCocycle (ProjectiveScheme.CM.Construction.projectiveEmbeddingCoordinates V)
      (ProjectiveScheme.CM.Construction.projectiveEmbeddingCoordinates_continuous V) (IntrinsicProjectiveCharts.CM.Construction.projectiveEmbeddingCoordinates_holomorphic V))
  exact hform.trans (hnat.symm.trans (h.trans
    (rationalSmoothCohomologyMap_eq V 2 (fubiniStudyClassQ V))))

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveCurvatureIntegration.CM.Construction
