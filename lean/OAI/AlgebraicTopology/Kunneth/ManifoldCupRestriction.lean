import OAI.AlgebraicTopology.Kunneth.ManifoldWedgeRestriction
import OAI.AlgebraicTopology.Kunneth.SimplexCupIntegral

/-! # Manifold Cup Restriction -/

namespace OAI.AlgebraicTopology.Kunneth.ManifoldCupRestriction

noncomputable section

/-! The simplex cup model recovers the actual smooth-singular cup cochain. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory Opposite
open scoped _root_.Manifold ContDiff Simplicial TensorProduct

namespace Constructions

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {p q : ℕ}

theorem simplexFormCochain_manifold {n : ℕ}
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M p) :
    SimplexFormCochain.Constructions.simplexFormCochain n p (SimplexFormPullback.Constructions.simplexManifoldFormRestriction sigma p a) =
      (Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of ℂ ℂ) (SSet.yonedaEquiv.symm sigma)).f p
        (DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain E M p a) := by
  apply Products.Cup.cochain_ext Δ[n] (ModuleCat.of ℂ ℂ)
  intro s
  rw [SimplexFormCochain.Constructions.simplexFormCochain_evaluation, Cohomology.Singular.Formulas.evaluation_pullback_apply,
    DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain_evaluation,
    ← SimplexFormPullback.Constructions.simplexManifoldFormRestriction_face (SSet.stdSimplex.objEquiv s),
    RestrictedSimplexIntegration.Constructions.simplexIntegral_manifoldRestriction]
  rfl

def manifoldCupCochain (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M p) (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M q) :
    (Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M).X (q + p) :=
  Products.Cup.cochainCast (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet (ModuleCat.of ℂ ℂ) (Nat.add_comm p q)
    (Products.Cup.cupWith (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet (LinearMap.mul ℂ ℂ)
      (DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain E M p a) (DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain E M q b.val))

theorem simplexTensorCup_manifold {n : ℕ}
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M p) (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M q) :
    SimplexCupIntegral.Constructions.simplexTensorCup q n p (ManifoldWedgeRestriction.Constructions.simplexManifoldTensorRestriction sigma a b) =
      (Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of ℂ ℂ) (SSet.yonedaEquiv.symm sigma)).f (q + p)
        (manifoldCupCochain a b) := by
  unfold ManifoldWedgeRestriction.Constructions.simplexManifoldTensorRestriction manifoldCupCochain
  rw [SimplexCupIntegral.Constructions.simplexTensorCup_tmul, SimplexCupIntegral.Constructions.cochainCast_pullback, Products.Cup.cupWith_pullback,
    simplexFormCochain_manifold]
  congr 2
  exact simplexFormCochain_manifold sigma b.val

theorem simplexCupIntegral_manifold (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M p) (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M q)
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋q + p⦌) :
    SimplexCupIntegral.Constructions.simplexCupIntegral q p (ManifoldWedgeRestriction.Constructions.simplexManifoldTensorRestriction sigma a b) =
      Cohomology.Singular.Coefficients.simplicialEvaluation (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet (ModuleCat.of ℂ ℂ)
        sigma (manifoldCupCochain a b) := by
  change Cohomology.Singular.Coefficients.simplicialEvaluation Δ[q + p] (ModuleCat.of ℂ ℂ)
    (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋q + p⦌))
      (SimplexCupIntegral.Constructions.simplexTensorCup q (q + p) p (ManifoldWedgeRestriction.Constructions.simplexManifoldTensorRestriction sigma a b)) = _
  rw [simplexTensorCup_manifold, Cohomology.Singular.Formulas.evaluation_pullback_apply,
    SSet.yonedaEquiv_symm_app_objEquiv_symm]
  change Cohomology.Singular.Coefficients.simplicialEvaluation (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet (ModuleCat.of ℂ ℂ)
    ((Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet.map (𝟙 _) sigma) (manifoldCupCochain a b) = _
  rw [CategoryTheory.Functor.map_id]
  rfl

end Constructions

end

end OAI.AlgebraicTopology.Kunneth.ManifoldCupRestriction
