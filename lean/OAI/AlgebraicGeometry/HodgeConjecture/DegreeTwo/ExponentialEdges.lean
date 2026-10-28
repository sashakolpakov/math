import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialForms
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.StraightIntegrationEq

/-! # Exponential Edges -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialEdges.Constructions.Exponential

noncomputable section

/-! Actual smooth exponential edges and the periods of invariant one-forms. -/

open _root_.CategoryTheory Opposite _root_.Manifold
open scoped Simplicial _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.StraightIntegrationEq.Constructions.StraightIntegration

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace C] [ChartedSpace E C] [CommGroup C]
  [LieGroup (𝓘(ℝ, E)) ∞ C] [T2Space C]

/-- The actual smooth one-simplex obtained by exponentiating a straight edge. -/
def smoothExponentialEdge (v : E) :
    (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E C).toSSet _⦋1⦌ :=
  (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothSingularMap E E (ExponentialM.Constructions.Exponential.expMap (E := E) (C := C)) ExponentialSmooth.Constructions.Exponential.expMap_contMDiff).app _
    (StraightIntegrationEq.Constructions.StraightIntegration.smoothVectorEdge v)

/-- Integrating an invariant one-form along an exponential edge evaluates
its identity covector on the displacement. -/
theorem smoothExponentialEdge_integration
    (α : TangentSpace (𝓘(ℝ, E)) (1 : C) [⋀^Fin 1]→L[ℝ] ℂ) (v : E) :
    AlgebraicTopology.DeRham.Comparison.SmoothSimplexIntegration.smoothSimplexIntegration (smoothExponentialEdge (C := C) v)
      (AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantSmoothForm α) = α (fun _ => v) := by
  unfold smoothExponentialEdge
  rw [AlgebraicTopology.DeRham.Comparison.SmoothSimplexIntegration.smoothSimplexIntegration_postcompose]
  exact StraightIntegrationEq.Constructions.StraightIntegration.smoothVectorEdge_integration (V := E) _ α (ExponentialForms.Constructions.Exponential.invariantSmoothForm_pullback_expMap α) v

/-- Exponentiating a lattice vector closes the edge at the group identity. -/
theorem smoothExponentialEdge_isLoop (ℓ : ExponentialLocal.Constructions.Exponential.expLattice (E := E) (C := C)) :
    (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E C).toSSet.δ 0 (smoothExponentialEdge (ℓ : E)) =
      (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E C).toSSet.δ 1 (smoothExponentialEdge (ℓ : E)) := by
  apply Subtype.ext
  apply TopCat.toSSetObj₀Equiv.injective
  erw [← TopCat.toSSetObj₁Equiv_apply_one, ← TopCat.toSSetObj₁Equiv_apply_zero]
  have he (t : TopCat.I) :
      TopCat.toSSetObj₁Equiv (smoothExponentialEdge (C := C) (ℓ : E)).val t =
        ExponentialM.Constructions.Exponential.expMap (C := C) (TopCat.toSSetObj₁Equiv (PeriodEdges.Constructions.SingularPeriods.vectorEdge (ℓ : E)) t) := rfl
  rw [he, he, PeriodEdges.Constructions.SingularPeriods.vectorEdge_one, PeriodEdges.Constructions.SingularPeriods.vectorEdge_zero]
  have hl : ExponentialM.Constructions.Exponential.expMap (C := C) (ℓ : E) = 1 := ℓ.property
  rw [hl]
  exact (ExponentialM.Constructions.Exponential.exp_zero (G := C)).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialEdges.Constructions.Exponential
