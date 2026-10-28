import OAI.AlgebraicGeometry.AbelianVariety.InvariantWedge
import OAI.AlgebraicTopology.Kunneth.RestrictedWedge
import OAI.AlgebraicTopology.Kunneth.RestrictedSimplexIntegration

/-! # Simplex Wedge -/

namespace OAI.AlgebraicGeometry.AbelianVariety.SimplexWedge.Constructions.ExteriorCohomology

noncomputable section

open scoped _root_.Manifold ContDiff Simplicial

variable {V : Type*} {E M : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {p q : ℕ}

theorem parameterFormPullback_wedge (f : V → M) (hf : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ f)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M p) (b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M q) :
    AlgebraicTopology.Kunneth.SimplexFormPullback.Constructions.parameterFormPullback f hf (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge a b) =
      AlgebraicTopology.Kunneth.WedgeAlgebra.Constructions.normedWedge (AlgebraicTopology.Kunneth.SimplexFormPullback.Constructions.parameterFormPullback f hf a) (AlgebraicTopology.Kunneth.SimplexFormPullback.Constructions.parameterFormPullback f hf b) := by
  apply Analysis.DifferentialForms.Manifold.Basic.SmoothForm.ext
  intro x
  let D : V →L[ℝ] E := mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f x
  let T : V →L[ℝ] V := (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm.toContinuousLinearMap
  ext v
  exact congrArg (fun c : V [⋀^Fin (p + q)]→L[ℝ] ℂ => c v)
    (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge_pullback (E := V) (F := E) (D.comp T) (a (f x)) (b (f x))).symm

theorem simplexManifoldFormRestriction_wedge {n : ℕ}
    (sigma : (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M p) (b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M q) :
    AlgebraicTopology.Kunneth.SimplexFormPullback.Constructions.simplexManifoldFormRestriction sigma (p + q) (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge a b) =
      AlgebraicTopology.Kunneth.RestrictedWedge.Constructions.restrictedWedge (AlgebraicTopology.Kunneth.SimplexFormDomain.Constructions.coordinateSimplex n) p q
        (AlgebraicTopology.Kunneth.SimplexFormPullback.Constructions.simplexManifoldFormRestriction sigma p a) (AlgebraicTopology.Kunneth.SimplexFormPullback.Constructions.simplexManifoldFormRestriction sigma q b) := by
  simp only [AlgebraicTopology.Kunneth.SimplexFormPullback.Constructions.simplexManifoldFormRestriction, AlgebraicTopology.Kunneth.SimplexFormPullback.Constructions.restrictedManifoldPullback, LinearMap.comp_apply,
    parameterFormPullback_wedge, AlgebraicTopology.Kunneth.RestrictedWedge.Constructions.restrictedWedge_restrict]

theorem smoothSimplexIntegration_wedge_restricted
    (sigma : (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋p + q⦌)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M p) (b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M q) :
    AlgebraicTopology.DeRham.Comparison.SmoothSimplexIntegration.smoothSimplexIntegration sigma (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge a b) =
      AlgebraicTopology.Kunneth.RestrictedSimplexIntegration.Constructions.simplexIntegral (p + q)
        (AlgebraicTopology.Kunneth.RestrictedWedge.Constructions.restrictedWedge (AlgebraicTopology.Kunneth.SimplexFormDomain.Constructions.coordinateSimplex (p + q)) p q
          (AlgebraicTopology.Kunneth.SimplexFormPullback.Constructions.simplexManifoldFormRestriction sigma p a) (AlgebraicTopology.Kunneth.SimplexFormPullback.Constructions.simplexManifoldFormRestriction sigma q b)) := by
  rw [← AlgebraicTopology.Kunneth.RestrictedSimplexIntegration.Constructions.simplexIntegral_manifoldRestriction, simplexManifoldFormRestriction_wedge]

end

end OAI.AlgebraicGeometry.AbelianVariety.SimplexWedge.Constructions.ExteriorCohomology
