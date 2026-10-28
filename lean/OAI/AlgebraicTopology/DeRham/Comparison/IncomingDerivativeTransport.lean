import OAI.Analysis.DifferentialForms.Manifold.ManifoldDegreeTransport
import OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham

/-! # Incoming Derivative Transport -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.IncomingDerivativeTransport

noncomputable section

/-!
# Equality transport of actual incoming exterior derivatives

The incoming derivative at positive degree is the ordinary exterior
derivative. Reindexing its primitive by the equal degree does not change
the resulting form. This supplies the precise quotient-interface witness
for an actual d′d″ form once its derivative identity has been proved.
-/

open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {k n : ℕ}

/-- The incoming derivative agrees with the ordinary derivative under the
actual equality of the natural-number degree indices. -/
theorem manifoldIncomingExteriorDerivative_castDegree (h : k + 1 = n)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M k) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldIncomingExteriorDerivative E M n
        (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree (by omega : k = n - 1) form) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree h (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form) := by
  subst n
  simp only [Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldIncomingExteriorDerivative_succ, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_self]

/-- A transported actual exterior derivative has its explicit incoming primitive. -/
theorem exists_incoming_primitive_castDegree_d (h : k + 1 = n)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M k) :
    ∃ primitive : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M (n - 1),
      Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldIncomingExteriorDerivative E M n primitive =
        Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree h (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form) :=
  ⟨Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree (by omega : k = n - 1) form,
    manifoldIncomingExteriorDerivative_castDegree h form⟩

/-- Consequently the transported derivative is in the actual exact-form submodule. -/
theorem castDegree_d_mem_manifoldExactForms (h : k + 1 = n)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M k) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree h (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form) ∈ Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldExactForms E M n :=
  exists_incoming_primitive_castDegree_d h form

end

end OAI.AlgebraicTopology.DeRham.Comparison.IncomingDerivativeTransport
