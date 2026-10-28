import OAI.AlgebraicTopology.Kunneth.SimplexComparisonHomotopy
import OAI.AlgebraicTopology.Kunneth.ManifoldCupRestriction
import OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass

/-! # Manifold Comparison Cochain -/

namespace OAI.AlgebraicTopology.Kunneth.ManifoldComparisonCochain

noncomputable section

/-! The simplex homotopy gives an actual smooth-singular primitive for the product discrepancy. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory Opposite
open scoped _root_.Manifold ContDiff Simplicial TensorProduct

namespace Constructions

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {p q : ℕ}

def manifoldIntegrationDifference (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M p) (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M q) :
    (Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M).X (q + p) :=
  DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain E M (q + p)
      (ManifoldWedge.Constructions.manifoldDegreeCast (Nat.add_comm p q) (ManifoldWedge.Constructions.manifoldWedge a b.val)) - ManifoldCupRestriction.Constructions.manifoldCupCochain a b

theorem manifoldIntegrationDifference_evaluation
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M p) (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M q)
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋q + p⦌) :
    Cohomology.Singular.Coefficients.simplicialEvaluation (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet (ModuleCat.of ℂ ℂ) sigma
      (manifoldIntegrationDifference a b) =
        SimplexComparisonHomotopy.Constructions.simplexIntegrationDifference q p (ManifoldWedgeRestriction.Constructions.simplexManifoldTensorRestriction sigma a b) := by
  unfold manifoldIntegrationDifference
  rw [map_sub, DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain_evaluation,
    ← ManifoldWedgeRestriction.Constructions.simplexWedgeIntegral_manifold, ← ManifoldCupRestriction.Constructions.simplexCupIntegral_manifold]
  rfl

def manifoldComparisonCochain (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M (p + 1)) (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M q) :
    (Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M).X (q + p) :=
  (Cohomology.Singular.Coefficients.degreewiseFunctionIso (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet
    (ModuleCat.of ℂ ℂ) (q + p)).toLinearEquiv.symm
      (fun sigma => SimplexComparisonHomotopy.Constructions.simplexComparisonHomotopy q p (ManifoldWedgeRestriction.Constructions.simplexManifoldTensorRestriction sigma a b))

theorem manifoldComparisonCochain_evaluation
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M (p + 1)) (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M q)
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋q + p⦌) :
    Cohomology.Singular.Coefficients.simplicialEvaluation (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet (ModuleCat.of ℂ ℂ) sigma
      (manifoldComparisonCochain a b) =
        SimplexComparisonHomotopy.Constructions.simplexComparisonHomotopy q p (ManifoldWedgeRestriction.Constructions.simplexManifoldTensorRestriction sigma a b) := by
  rw [← Cohomology.Singular.Coefficients.degreewiseFunctionIso_hom_apply]
  change ((Cohomology.Singular.Coefficients.degreewiseFunctionIso (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet
      (ModuleCat.of ℂ ℂ) (q + p)).toLinearEquiv
    ((Cohomology.Singular.Coefficients.degreewiseFunctionIso (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet
      (ModuleCat.of ℂ ℂ) (q + p)).toLinearEquiv.symm _)) sigma = _
  rw [LinearEquiv.apply_symm_apply]

theorem manifoldComparisonCochain_d_evaluation
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M (p + 1)) (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M q)
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋q + p + 1⦌) :
    Cohomology.Singular.Coefficients.simplicialEvaluation (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet (ModuleCat.of ℂ ℂ) sigma
      ((Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M).d (q + p) (q + p + 1)
        (manifoldComparisonCochain a b)) =
      TensorSimplicialForms.Constructions.simplexFormTensorDelta q (q + p) (p + 1) (SimplexComparisonHomotopy.Constructions.simplexComparisonHomotopy q p)
        (ManifoldWedgeRestriction.Constructions.simplexManifoldTensorRestriction sigma a b) := by
  rw [Cohomology.Singular.Formulas.evaluation_coboundary_apply, TensorSimplicialForms.Constructions.simplexFormTensorDelta_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [manifoldComparisonCochain_evaluation]
  have hf := ManifoldWedgeRestriction.Constructions.simplexManifoldTensorRestriction_face (SimplexCategory.δ j) sigma a b
  exact congrArg (fun t => (-1 : ℤ) ^ j.val • SimplexComparisonHomotopy.Constructions.simplexComparisonHomotopy q p t) hf

theorem manifoldIntegrationDifference_closed_zero
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M 0) (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M q) :
    manifoldIntegrationDifference a.val b = 0 := by
  apply Products.Cup.cochain_ext (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet (ModuleCat.of ℂ ℂ)
  intro sigma
  rw [manifoldIntegrationDifference_evaluation, map_zero]
  have h := SimplexComparisonHomotopy.Constructions.simplexComparisonHomotopy_zero q (ManifoldWedgeRestriction.Constructions.simplexManifoldTensorRestriction sigma a.val b)
  rw [ManifoldWedgeRestriction.Constructions.simplexManifoldTensorRestriction_closed, map_zero] at h
  exact h.symm

theorem manifoldIntegrationDifference_closed_succ
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M (p + 1)) (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M q) :
    manifoldIntegrationDifference a.val b =
      (Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M).d (q + p) (q + p + 1)
        (manifoldComparisonCochain a.val b) := by
  apply Products.Cup.cochain_ext (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet (ModuleCat.of ℂ ℂ)
  intro sigma
  rw [manifoldIntegrationDifference_evaluation]
  erw [manifoldComparisonCochain_d_evaluation (p := p) (q := q) a.val b sigma]
  have h := SimplexComparisonHomotopy.Constructions.simplexComparisonHomotopy_succ q p (ManifoldWedgeRestriction.Constructions.simplexManifoldTensorRestriction sigma a.val b)
  rw [ManifoldWedgeRestriction.Constructions.simplexManifoldTensorRestriction_closed, map_zero] at h
  exact sub_eq_zero.mp h.symm

end Constructions

end

end OAI.AlgebraicTopology.Kunneth.ManifoldComparisonCochain
