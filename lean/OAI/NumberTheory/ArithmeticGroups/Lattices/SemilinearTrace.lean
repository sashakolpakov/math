import OAI.NumberTheory.ArithmeticGroups.Lattices.SemilinearBasisCoordinates
import Mathlib.LinearAlgebra.Trace

/-! # Semilinear Trace -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.SemilinearTrace.Construction

noncomputable section

/-! Trace is compatible with a semilinear intertwiner carrying one
basis onto another. -/

open scoped Classical

theorem semilinear_intertwining_trace
    {R S V W ι : Type*} [CommRing R] [CommRing S]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module S W]
    [Fintype ι]
    (σ : R →+* S) (b : Module.Basis ι R V) (c : Module.Basis ι S W)
    (f : V →ₛₗ[σ] W) (hf : ∀ i, f (b i) = c i)
    (A : Module.End R V) (B : Module.End S W) (hAB : ∀ x, f (A x) = B (f x)) :
    σ (LinearMap.trace R V A) = LinearMap.trace S W B := by
  rw [LinearMap.trace_eq_matrix_trace R b, LinearMap.trace_eq_matrix_trace S c,
    ← SemilinearBasisCoordinates.Construction.semilinear_intertwining_matrix σ b c f hf A B hAB]
  simp only [Matrix.trace, Matrix.diag, map_sum, Matrix.map_apply]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.SemilinearTrace.Construction
