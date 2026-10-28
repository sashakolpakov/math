import OAI.AlgebraicGeometry.AbelianVariety.CupFunctional
import OAI.AlgebraicTopology.Kunneth.SimplexComparisonHomotopy
import OAI.AlgebraicTopology.Kunneth.ClosedManifoldWedge
import OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass
import OAI.AlgebraicTopology.Products.CupCohomologyAlgebra

/-! # Integration Product -/

namespace OAI.AlgebraicGeometry.AbelianVariety.IntegrationProduct.Constructions.ExteriorCohomology

noncomputable section

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff Simplicial TensorProduct
open OAI.AlgebraicTopology.Products.CupCohomologyAlgebra OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass
variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {n p q : ℕ}

theorem modelFunctionalCochain_sub (F G : AlgebraicTopology.Kunneth.TensorSimplicialForms.Constructions.SimplexFormTensor q n p →ₗ[ℂ] ℂ)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M p) (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M q) :
    TensorRestriction.Constructions.ExteriorCohomology.modelFunctionalCochain (F - G) a b =
      TensorRestriction.Constructions.ExteriorCohomology.modelFunctionalCochain F a b - TensorRestriction.Constructions.ExteriorCohomology.modelFunctionalCochain G a b := by
  apply AlgebraicTopology.Products.Cup.cochain_ext (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet (ModuleCat.of ℂ ℂ)
  intro sigma
  rw [map_sub, TensorRestriction.Constructions.ExteriorCohomology.modelFunctionalCochain_evaluation, TensorRestriction.Constructions.ExteriorCohomology.modelFunctionalCochain_evaluation,
    TensorRestriction.Constructions.ExteriorCohomology.modelFunctionalCochain_evaluation]
  rfl

theorem modelFunctionalCochain_difference (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M p)
    (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M q) :
    TensorRestriction.Constructions.ExteriorCohomology.modelFunctionalCochain (AlgebraicTopology.Kunneth.SimplexComparisonHomotopy.Constructions.simplexIntegrationDifference q p) a b =
      AlgebraicTopology.Products.Cup.cochainCast (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet (ModuleCat.of ℂ ℂ)
        (Nat.add_comm p q) (AlgebraicTopology.DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain E M (p + q) (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge a b.val)) -
      AlgebraicTopology.Products.Cup.cochainCast (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet (ModuleCat.of ℂ ℂ)
        (Nat.add_comm p q) (AlgebraicTopology.Products.Cup.cupWith (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet
          (LinearMap.mul ℂ ℂ) (AlgebraicTopology.DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain E M p a)
          (AlgebraicTopology.DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain E M q b.val)) := by
  rw [AlgebraicTopology.Kunneth.SimplexComparisonHomotopy.Constructions.simplexIntegrationDifference, modelFunctionalCochain_sub,
    WedgeFunctional.Constructions.ExteriorCohomology.modelFunctionalCochain_wedge, CupFunctional.Constructions.ExteriorCohomology.modelFunctionalCochain_cup]

theorem cohomologyCast_injective (K : SSet.{0}) {k l : ℕ} (h : k = l) :
    Function.Injective (AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast K (ModuleCat.of ℂ ℂ) h) := by
  subst l
  exact Function.injective_id

/-- Actual smooth-simplex integration carries wedge products to the actual cup product. -/
theorem integration_class_wedge (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M p)
    (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M q) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M) (p + q)
      (AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCocycle E M (p + q) (AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldWedge a b)) =
    AlgebraicTopology.Products.CupCohomology.cohomologyCup (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet p q
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M) p
        (AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCocycle E M p a))
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M) q
        (AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCocycle E M q b)) := by
  rw [AlgebraicTopology.Products.CupCohomology.cohomologyCupWith_class_class]
  apply cohomologyCast_injective (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet
    (Nat.add_comm p q)
  rw [AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast_class, AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast_class]
  cases p with
  | zero =>
      apply congrArg (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (q + 0))
      apply Subtype.ext
      apply sub_eq_zero.mp
      have hz := TensorRestriction.Constructions.ExteriorCohomology.modelFunctionalCochain_factor_zero (AlgebraicTopology.Kunneth.SimplexComparisonHomotopy.Constructions.simplexIntegrationDifference q 0)
        (AlgebraicTopology.Kunneth.SimplexComparisonHomotopy.Constructions.simplexComparisonHomotopy q 0)
        (by apply LinearMap.ext; intro x; exact AlgebraicTopology.Kunneth.SimplexComparisonHomotopy.Constructions.simplexComparisonHomotopy_zero q x) a b
      rw [modelFunctionalCochain_difference] at hz
      simpa only [AlgebraicTopology.Products.CupCohomologyAlgebra.cocycleCast_val] using! hz
  | succ p =>
      apply (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_iff_exists_succ _ (q + p) _ _).mpr
      refine ⟨TensorRestriction.Constructions.ExteriorCohomology.modelFunctionalCochain (AlgebraicTopology.Kunneth.SimplexComparisonHomotopy.Constructions.simplexComparisonHomotopy q p) a.val b, ?_⟩
      have hh := TensorRestriction.Constructions.ExteriorCohomology.modelFunctionalCochain_homotopy_boundary
        (AlgebraicTopology.Kunneth.SimplexComparisonHomotopy.Constructions.simplexIntegrationDifference q (p + 1)) (AlgebraicTopology.Kunneth.SimplexComparisonHomotopy.Constructions.simplexComparisonHomotopy q (p + 1))
        (AlgebraicTopology.Kunneth.SimplexComparisonHomotopy.Constructions.simplexComparisonHomotopy q p)
        (by apply LinearMap.ext; intro x; exact AlgebraicTopology.Kunneth.SimplexComparisonHomotopy.Constructions.simplexComparisonHomotopy_succ q p x) a b
      rw [modelFunctionalCochain_difference] at hh
      simpa only [AlgebraicTopology.Products.CupCohomologyAlgebra.cocycleCast_val] using! hh

end

end OAI.AlgebraicGeometry.AbelianVariety.IntegrationProduct.Constructions.ExteriorCohomology
