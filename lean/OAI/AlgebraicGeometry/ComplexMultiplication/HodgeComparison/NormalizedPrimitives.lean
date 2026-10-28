import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ZeroCocycles
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PrimitiveTransitions
import OAI.AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain

/-! # Normalized Primitives -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.NormalizedPrimitives.CM.Construction

noncomputable section

/-! Normalize an actual smooth primitive against a prescribed singular
zero-cochain whose coboundary is the integrated derivative. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def constantZeroForm (z : ℂ) : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0 :=
  Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal
    (Analysis.DifferentialForms.Manifold.LocallyConstant.locallyConstantToManifoldZeroForm E ⊤ (LocallyConstant.const _ z))

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem constantZeroForm_scalar (z : ℂ) (x : M) :
    HolomorphicPrimitive.CM.Construction.zeroFormScalar (constantZeroForm E M z) x = z := by
  unfold constantZeroForm HolomorphicPrimitive.CM.Construction.zeroFormScalar
  rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal_apply, Analysis.DifferentialForms.Manifold.LocallyConstant.locallyConstantToManifoldZeroForm_apply]
  rfl

theorem constantZeroForm_d (z : ℂ) : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (constantZeroForm E M z) = 0 := by
  apply HolomorphicPrimitive.CM.Construction.d_zeroForm_eq_zero_of_locallyConstant
  have heq : HolomorphicPrimitive.CM.Construction.zeroFormScalar (constantZeroForm E M z) = fun _ => z :=
    funext (constantZeroForm_scalar E M z)
  rw [heq]
  exact IsLocallyConstant.const z

theorem normalize_primitive_against_zero_cochain [PathConnectedSpace M]
    (x₀ : M) (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0)
    (b : (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M).X 0)
    (hb : (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M).d 0 1 b =
      AlgebraicTopology.DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain E M 1 (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f)) :
    ∃ g : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0,
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d g = Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f ∧
      ∀ x, HolomorphicPrimitive.CM.Construction.zeroFormScalar g x = ZeroCocycles.CM.Construction.smoothZeroCochainPoint E M b x := by
  let c := AlgebraicTopology.DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain E M 0 f - b
  have hi := ConcreteCategory.congr_hom
    ((AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap E M).comm 0 1) f
  change (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M).d 0 1
      (AlgebraicTopology.DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain E M 0 f) =
    AlgebraicTopology.DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain E M 1 (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f) at hi
  have hc : (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M).d 0 1 c = 0 := by
    rw [map_sub, hi, hb, sub_self]
  let k : ℂ := HolomorphicPrimitive.CM.Construction.zeroFormScalar f x₀ - ZeroCocycles.CM.Construction.smoothZeroCochainPoint E M b x₀
  have hk (x : M) : HolomorphicPrimitive.CM.Construction.zeroFormScalar f x - ZeroCocycles.CM.Construction.smoothZeroCochainPoint E M b x = k := by
    have h := ZeroCocycles.CM.Construction.smooth_zero_cocycle_constant E M c hc x x₀
    simpa only [c, k, HolomorphicPrimitive.CM.Construction.zeroFormScalar, ZeroCocycles.CM.Construction.smoothZeroCochainPoint_sub,
      ZeroCocycles.CM.Construction.smoothZeroCochainPoint_integration] using h
  refine ⟨f - constantZeroForm E M k, ?_, ?_⟩
  · rw [map_sub, constantZeroForm_d, sub_zero]
  · intro x
    change HolomorphicPrimitive.CM.Construction.zeroFormScalar f x - HolomorphicPrimitive.CM.Construction.zeroFormScalar (constantZeroForm E M k) x = _
    rw [constantZeroForm_scalar, ← hk x]
    ring

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.NormalizedPrimitives.CM.Construction
