import OAI.AlgebraicGeometry.AbelianVariety.TensorRestriction
import OAI.AlgebraicTopology.Kunneth.SimplexWedgeIntegral
import OAI.AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain

/-! # Wedge Functional -/

namespace OAI.AlgebraicGeometry.AbelianVariety.WedgeFunctional.Constructions.ExteriorCohomology

noncomputable section

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff Simplicial TensorProduct
open OAI.AlgebraicTopology.Kunneth.SimplexWedgeIntegral.Constructions OAI.AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {n p q : ℕ}

theorem simplexManifoldFormRestriction_degreeCast {k l : ℕ} (h : k = l)
    (sigma : (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M k) :
    AlgebraicTopology.Kunneth.SimplexFormPullback.Constructions.simplexManifoldFormRestriction sigma l (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldDegreeCast h a) =
      AlgebraicTopology.Kunneth.RestrictedWedge.Constructions.restrictedFormDegreeCast (AlgebraicTopology.Kunneth.SimplexFormDomain.Constructions.coordinateSimplex n) h (AlgebraicTopology.Kunneth.SimplexFormPullback.Constructions.simplexManifoldFormRestriction sigma k a) := by
  subst l
  rfl

theorem smoothSimplexCochain_degreeCast {k l : ℕ} (h : k = l)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M k) :
    AlgebraicTopology.DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain E M l (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldDegreeCast h a) =
      AlgebraicTopology.Products.Cup.cochainCast (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet (ModuleCat.of ℂ ℂ) h
        (AlgebraicTopology.DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain E M k a) := by
  subst l
  rfl

/-- The model wedge functional is exactly the repository's integration cochain. -/
theorem modelFunctionalCochain_wedge (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M p)
    (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M q) :
    TensorRestriction.Constructions.ExteriorCohomology.modelFunctionalCochain (AlgebraicTopology.Kunneth.SimplexWedgeIntegral.Constructions.simplexWedgeIntegral q p) a b =
      AlgebraicTopology.Products.Cup.cochainCast (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet (ModuleCat.of ℂ ℂ)
        (Nat.add_comm p q) (AlgebraicTopology.DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain E M (p + q) (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge a b.val)) := by
  rw [← smoothSimplexCochain_degreeCast]
  apply AlgebraicTopology.Products.Cup.cochain_ext (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet (ModuleCat.of ℂ ℂ)
  intro sigma
  rw [TensorRestriction.Constructions.ExteriorCohomology.modelFunctionalCochain_evaluation, AlgebraicTopology.DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain_evaluation,
    ← AlgebraicTopology.Kunneth.RestrictedSimplexIntegration.Constructions.simplexIntegral_manifoldRestriction, simplexManifoldFormRestriction_degreeCast,
    SimplexWedge.Constructions.ExteriorCohomology.simplexManifoldFormRestriction_wedge]
  rfl

end

end OAI.AlgebraicGeometry.AbelianVariety.WedgeFunctional.Constructions.ExteriorCohomology
