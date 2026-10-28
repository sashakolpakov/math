import Mathlib.RingTheory.Trace.Defs

/-! # Algebra Trace -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.AlgebraTrace

noncomputable section

/-! The trace of a finite free algebra, divided by its invertible rank, is an explicit linear retraction of the structural algebra map. -/
universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

def normalizedAlgebraTrace (u : Rˣ) : A →ₗ[R] R := (↑u⁻¹ : R) • Algebra.trace R A

theorem normalizedAlgebraTrace_algebraMap {n : ℕ} (b : Module.Basis (Fin n) R A)
    (u : Rˣ) (hu : (u : R) = n) (r : R) :
    normalizedAlgebraTrace (A := A) u (algebraMap R A r) = r := by
  change (↑u⁻¹ : R) * Algebra.trace R A (algebraMap R A r) = r
  rw [Algebra.trace_algebraMap_of_basis b, Fintype.card_fin, nsmul_eq_mul, ← hu, ← mul_assoc]
  simp

theorem normalizedAlgebraTrace_one {n : ℕ} (b : Module.Basis (Fin n) R A)
    (u : Rˣ) (hu : (u : R) = n) : normalizedAlgebraTrace (A := A) u 1 = 1 := by
  simpa only [map_one] using normalizedAlgebraTrace_algebraMap b u hu 1

theorem normalizedAlgebraTrace_comp_algebraLinearMap {n : ℕ} (b : Module.Basis (Fin n) R A)
    (u : Rˣ) (hu : (u : R) = n) :
    (normalizedAlgebraTrace (A := A) u).comp (Algebra.linearMap R A) = LinearMap.id := by
  apply LinearMap.ext
  intro r
  exact normalizedAlgebraTrace_algebraMap b u hu r

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.AlgebraTrace
