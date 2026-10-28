import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialForms
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StraightIntegrationEq

/-! # Exponential Edges Is -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ExponentialEdgesIs.ExponentialEdges

noncomputable section

/-! Actual smooth exponential edges and the periods of invariant one-forms. -/

open _root_.CategoryTheory Opposite _root_.Manifold
open scoped Simplicial _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialForms.Constructions.Exponential
open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PeriodEdgesTo.PeriodEdges OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StraightIntegrationEq.StraightIntegration

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace C] [ChartedSpace E C] [CommGroup C]
  [LieGroup (𝓘(ℝ, E)) ∞ C] [T2Space C]

/-- The actual smooth one-simplex obtained by exponentiating a straight edge. -/
def smoothExponentialEdge (v : E) :
    (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E C).toSSet _⦋1⦌ :=
  (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothSingularMap E E (HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (E := E) (C := C)) HodgeConjecture.DegreeTwo.ExponentialSmooth.Constructions.Exponential.expMap_contMDiff).app _
    (StraightIntegrationEq.StraightIntegration.smoothVectorEdge v)

/-- Integrating an invariant one-form along an exponential edge evaluates
its identity covector on the displacement. -/
theorem smoothExponentialEdge_integration
    (α : TangentSpace (𝓘(ℝ, E)) (1 : C) [⋀^Fin 1]→L[ℝ] ℂ) (v : E) :
    AlgebraicTopology.DeRham.Comparison.SmoothSimplexIntegration.smoothSimplexIntegration (smoothExponentialEdge (C := C) v)
      (AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantSmoothForm α) = α (fun _ => v) := by
  unfold smoothExponentialEdge
  rw [AlgebraicTopology.DeRham.Comparison.SmoothSimplexIntegration.smoothSimplexIntegration_postcompose]
  exact StraightIntegrationEq.StraightIntegration.smoothVectorEdge_integration (V := E) _ α (HodgeConjecture.DegreeTwo.ExponentialForms.Constructions.Exponential.invariantSmoothForm_pullback_expMap α) v

/-- Exponentiating a lattice vector closes the edge at the group identity. -/
theorem smoothExponentialEdge_isLoop (ℓ : HodgeConjecture.DegreeTwo.ExponentialLocal.Constructions.Exponential.expLattice (E := E) (C := C)) :
    (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E C).toSSet.δ 0 (smoothExponentialEdge (ℓ : E)) =
      (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E C).toSSet.δ 1 (smoothExponentialEdge (ℓ : E)) := by
  apply Subtype.ext
  apply TopCat.toSSetObj₀Equiv.injective
  erw [← TopCat.toSSetObj₁Equiv_apply_one, ← TopCat.toSSetObj₁Equiv_apply_zero]
  have he (t : TopCat.I) :
      TopCat.toSSetObj₁Equiv (smoothExponentialEdge (C := C) (ℓ : E)).val t =
        HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := C) (TopCat.toSSetObj₁Equiv (PeriodEdgesTo.PeriodEdges.vectorEdge (ℓ : E)) t) := rfl
  rw [he, he, PeriodEdgesTo.PeriodEdges.vectorEdge_one, PeriodEdgesTo.PeriodEdges.vectorEdge_zero]
  have hl : HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := C) (ℓ : E) = 1 := ℓ.property
  rw [hl]
  exact (HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.exp_zero (G := C)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ExponentialEdgesIs.ExponentialEdges
