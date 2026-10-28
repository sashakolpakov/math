import OAI.AlgebraicGeometry.AbelianVariety.WedgeFunctional
import OAI.AlgebraicTopology.Kunneth.SimplexCupIntegral

/-! # Cup Functional -/

namespace OAI.AlgebraicGeometry.AbelianVariety.CupFunctional.Constructions.ExteriorCohomology

noncomputable section

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff Simplicial TensorProduct
open OAI.AlgebraicTopology.Kunneth.SimplexCupIntegral.Constructions
variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {n p q : ℕ}

theorem simplexFormCochain_restriction
    (sigma : (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M p) :
    AlgebraicTopology.Kunneth.SimplexFormCochain.Constructions.simplexFormCochain n p (AlgebraicTopology.Kunneth.SimplexFormPullback.Constructions.simplexManifoldFormRestriction sigma p a) =
      (AlgebraicTopology.Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of ℂ ℂ) (SSet.yonedaEquiv.symm sigma)).f p
        (AlgebraicTopology.DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain E M p a) := by
  apply AlgebraicTopology.Products.Cup.cochain_ext Δ[n] (ModuleCat.of ℂ ℂ)
  intro s
  rw [AlgebraicTopology.Kunneth.SimplexFormCochain.Constructions.simplexFormCochain_evaluation, AlgebraicTopology.Cohomology.Singular.Formulas.evaluation_pullback_apply,
    AlgebraicTopology.DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain_evaluation, ← AlgebraicTopology.Kunneth.RestrictedSimplexIntegration.Constructions.simplexIntegral_manifoldRestriction]
  exact congrArg (AlgebraicTopology.Kunneth.RestrictedSimplexIntegration.Constructions.simplexIntegral p)
    (AlgebraicTopology.Kunneth.SimplexFormPullback.Constructions.simplexManifoldFormRestriction_face (SSet.stdSimplex.objEquiv s) sigma a).symm

theorem modelFunctionalCochain_cup (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M p)
    (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M q) :
    TensorRestriction.Constructions.ExteriorCohomology.modelFunctionalCochain (AlgebraicTopology.Kunneth.SimplexCupIntegral.Constructions.simplexCupIntegral q p) a b =
      AlgebraicTopology.Products.Cup.cochainCast (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet (ModuleCat.of ℂ ℂ)
        (Nat.add_comm p q) (AlgebraicTopology.Products.Cup.cupWith (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet
          (LinearMap.mul ℂ ℂ) (AlgebraicTopology.DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain E M p a)
          (AlgebraicTopology.DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain E M q b.val)) := by
  apply AlgebraicTopology.Products.Cup.cochain_ext (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet (ModuleCat.of ℂ ℂ)
  intro sigma
  rw [TensorRestriction.Constructions.ExteriorCohomology.modelFunctionalCochain_evaluation]
  change AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation Δ[q + p] (ModuleCat.of ℂ ℂ)
    (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋q + p⦌))
    (AlgebraicTopology.Kunneth.SimplexCupIntegral.Constructions.simplexTensorCup q (q + p) p
      (AlgebraicTopology.Kunneth.SimplexFormPullback.Constructions.simplexManifoldFormRestriction sigma p a ⊗ₜ[ℂ] TensorRestriction.Constructions.ExteriorCohomology.closedSimplexRestriction sigma b)) = _
  rw [AlgebraicTopology.Kunneth.SimplexCupIntegral.Constructions.simplexTensorCup_tmul]
  change AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation Δ[q + p] (ModuleCat.of ℂ ℂ) _
    (AlgebraicTopology.Products.Cup.cochainCast _ _ _ (AlgebraicTopology.Products.Cup.cupWith _ _
      (AlgebraicTopology.Kunneth.SimplexFormCochain.Constructions.simplexFormCochain _ _ (AlgebraicTopology.Kunneth.SimplexFormPullback.Constructions.simplexManifoldFormRestriction sigma p a))
      (AlgebraicTopology.Kunneth.SimplexFormCochain.Constructions.simplexFormCochain _ _ (AlgebraicTopology.Kunneth.SimplexFormPullback.Constructions.simplexManifoldFormRestriction sigma q b.val)))) = _
  rw [simplexFormCochain_restriction, simplexFormCochain_restriction,
    ← AlgebraicTopology.Products.Cup.cupWith_pullback, ← AlgebraicTopology.Kunneth.SimplexCupIntegral.Constructions.cochainCast_pullback, AlgebraicTopology.Cohomology.Singular.Formulas.evaluation_pullback_apply]
  have hs : (SSet.yonedaEquiv.symm sigma).app _
      (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋q + p⦌)) = sigma := by
    change (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet.map (𝟙 _).op sigma = sigma
    simp
  rw [hs]

end

end OAI.AlgebraicGeometry.AbelianVariety.CupFunctional.Constructions.ExteriorCohomology
