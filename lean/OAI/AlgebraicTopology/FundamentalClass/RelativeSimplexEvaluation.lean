import OAI.AlgebraicTopology.FundamentalClass.SimplexCycles
import OAI.AlgebraicTopology.FundamentalClass.EvaluationLocalization

/-! # Relative Simplex Evaluation -/

namespace OAI.AlgebraicTopology.FundamentalClass.RelativeSimplexEvaluation.IntegrationConstruction

noncomputable section

/-! The integral local cycle and its smooth complex representative give
the same relative homology class and the same actual simplex integral. -/

open _root_.CategoryTheory Opposite Set _root_.TopologicalSpace
open scoped Simplicial _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]

def smoothProjectedSimplexClass (U : Opens M) (n : ℕ)
    (σ : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌)
    (hσ : SimplexCycles.IntegrationConstruction.SimplexFacesIn (TopCat.of M) U n σ.val) :
    (RelativeSmooth.IntegrationConstruction.smoothRelativeChains E M U).homology n :=
  Cohomology.Singular.ChainRepresentatives.chainClass _ n ⟨(RelativeSmooth.IntegrationConstruction.smoothRelativeProjection E M U).f n
    (Cohomology.Singular.ChainDual.simplexChain (R := ℂ) (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet σ),
    SimplexCycles.IntegrationConstruction.smoothSimplex_relative_cycle E M U n σ hσ⟩

theorem smoothProjectedSimplexClass_comparison (U : Opens M) (n : ℕ)
    (σ : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌)
    (hσ : SimplexCycles.IntegrationConstruction.SimplexFacesIn (TopCat.of M) U n σ.val) :
    HomologicalComplex.homologyMap (RelativeSmooth.IntegrationConstruction.smoothRelativeComparison E M U) n
      (smoothProjectedSimplexClass E M U n σ hσ) =
      RelativeCoefficients.IntegrationConstruction.relativeCoefficientHomology (TopCat.of M) U n
        (ProjectedClasses.IntegrationConstruction.projectedClass (TopCat.of M) U n
          (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj (TopCat.of M)) σ.val)
          (SimplexCycles.IntegrationConstruction.integralSimplex_relative_cycle (TopCat.of M) U n σ.val hσ)) := by
  rw [smoothProjectedSimplexClass, Cohomology.Singular.EvaluationNaturality.chainClass_naturality, ProjectedClasses.IntegrationConstruction.projectedClass,
    RelativeCoefficients.IntegrationConstruction.relativeCoefficientHomology_class]
  apply congrArg (Cohomology.Singular.ChainRepresentatives.chainClass _ n)
  apply Subtype.ext
  change (RelativeSmooth.IntegrationConstruction.smoothRelativeComparison E M U).f n
    ((RelativeSmooth.IntegrationConstruction.smoothRelativeProjection E M U).f n
      (Cohomology.Singular.ChainDual.simplexChain (R := ℂ) (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet σ)) =
    RelativeCoefficients.IntegrationConstruction.relativeCoefficient (TopCat.of M) U n
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection (TopCat.of M) U).f n
        (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj (TopCat.of M)) σ.val))
  rw [RelativeCoefficients.IntegrationConstruction.relativeCoefficient_projection]
  have hcoeff : Duality.Poincare.IntegralCapCoefficients.integralToScalarSingular (R := ℂ) (TopCat.of M) n
      (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj (TopCat.of M)) σ.val) =
      Cohomology.Singular.ChainDual.simplexChain (R := ℂ) (TopCat.toSSet.obj (TopCat.of M)) σ.val :=
    Duality.Poincare.IntegralCapCoefficients.integralToScalarSimplicial_simplex _ n σ.val
  rw [hcoeff]
  have h := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (RelativeSmooth.IntegrationConstruction.smoothRelativeComparison_projection E M U) n)
    (Cohomology.Singular.ChainDual.simplexChain (R := ℂ) (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet σ)
  change (RelativeSmooth.IntegrationConstruction.smoothRelativeComparison E M U).f n
      ((RelativeSmooth.IntegrationConstruction.smoothRelativeProjection E M U).f n
        (Cohomology.Singular.ChainDual.simplexChain (R := ℂ) (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet σ)) =
    (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℂ (TopCat.of M) U).f n
      ((SmoothHomology.IntegrationConstruction.smoothChainInclusion E M).f n
        (Cohomology.Singular.ChainDual.simplexChain (R := ℂ) (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet σ)) at h
  rw [Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap_simplex] at h
  exact h

variable [IsManifold 𝓘(ℝ, E) ∞ M]

theorem relativeIntegration_smoothProjectedSimplexClass (U : Opens M) (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M n) (hform : ∀ x : U, form.val.val x = 0)
    (σ : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌)
    (hσ : SimplexCycles.IntegrationConstruction.SimplexFacesIn (TopCat.of M) U n σ.val) :
    SupportedEvaluation.IntegrationConstruction.relativeIntegrationOnHomology E M U n form hform
      (smoothProjectedSimplexClass E M U n σ hσ) = DeRham.Comparison.SmoothSimplexIntegration.smoothSimplexIntegration σ form.val := by
  rw [smoothProjectedSimplexClass, SupportedEvaluation.IntegrationConstruction.relativeIntegrationOnHomology_projection_class,
    SupportedEvaluation.IntegrationConstruction.smoothIntegrationFunctional, Cohomology.Singular.ChainDual.degreewiseChainDualEquiv_simplex, DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain_evaluation]

theorem evaluation_on_integral_relative_simplex (U : Opens M) (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M n) (hform : ∀ x : U, form.val.val x = 0)
    (β : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) (TopCat.of M) n)
    (hβ : HomologicalComplex.homologyMap
      (Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ) M) n β =
        DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCohomologyMap E M n (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M n form))
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of M)).homology n)
    (σ : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌)
    (hσ : SimplexCycles.IntegrationConstruction.SimplexFacesIn (TopCat.of M) U n σ.val) (sign : ℤ)
    (hclass : sign • ProjectedClasses.IntegrationConstruction.projectedClass (TopCat.of M) U n
        (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj (TopCat.of M)) σ.val)
        (SimplexCycles.IntegrationConstruction.integralSimplex_relative_cycle (TopCat.of M) U n σ.val hσ) =
      HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection (TopCat.of M) U) n z) :
    Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℂ ℂ) (TopCat.of M) n β
      (Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℂ) (TopCat.of M) n z) =
      sign • DeRham.Comparison.SmoothSimplexIntegration.smoothSimplexIntegration σ form.val := by
  have hcomp : HomologicalComplex.homologyMap (RelativeSmooth.IntegrationConstruction.smoothRelativeComparison E M U) n
      (sign • smoothProjectedSimplexClass E M U n σ hσ) =
      HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℂ (TopCat.of M) U) n
        (Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℂ) (TopCat.of M) n z) := by
    rw [map_zsmul, smoothProjectedSimplexClass_comparison, ← map_zsmul, hclass,
      RelativeCoefficients.IntegrationConstruction.relativeCoefficientHomology_projection]
  rw [EvaluationLocalization.IntegrationConstruction.evaluation_eq_relativeIntegration E M U n form hform β hβ _ _ hcomp, map_zsmul,
    relativeIntegration_smoothProjectedSimplexClass]

end

end OAI.AlgebraicTopology.FundamentalClass.RelativeSimplexEvaluation.IntegrationConstruction
