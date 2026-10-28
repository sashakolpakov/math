import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.AlgebraTrace
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree

/-! # Algebra Trace Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Free.AlgebraTraceBaseChange

noncomputable section

/-! Algebra trace for finite free algebras commutes with every actual scalar extension, using the transported finite basis. -/
universe u v w z

variable {R : Type u} {A : Type v} {S : Type w} {B : Type z}
variable [CommRing R] [CommRing A] [CommRing S] [CommRing B]
variable [Algebra R A] [Algebra R S] [Algebra S B] [Algebra R B] [IsScalarTower R S B]

theorem freeAlgebraTrace_baseChange {ι : Type*} [Fintype ι]
    (b : Module.Basis ι R A) (ε : A →ₐ[R] B) (h : IsBaseChange S ε.toLinearMap) (a : A) :
    Algebra.trace S B (ε a) = algebraMap R S (Algebra.trace R A a) := by
  classical
  rw [Algebra.trace_eq_matrix_trace (h.basis b), Algebra.trace_eq_matrix_trace b,
    AddMonoidHom.map_trace]
  congr 1
  ext i j
  simp only [Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, h.basis_apply]
  change (h.basis b).repr (ε a * ε (b j)) i = _
  rw [← map_mul ε]
  exact h.basis_repr_comp_apply b (a * b j) i

theorem normalizedAlgebraTrace_baseChange {ι : Type*} [Fintype ι]
    (b : Module.Basis ι R A) (ε : A →ₐ[R] B) (h : IsBaseChange S ε.toLinearMap)
    (u : Rˣ) (a : A) :
    Normalized.AlgebraTrace.normalizedAlgebraTrace (A := B) (Units.map (algebraMap R S) u) (ε a) =
      algebraMap R S (Normalized.AlgebraTrace.normalizedAlgebraTrace (A := A) u a) := by
  change algebraMap R S (↑u⁻¹ : R) * Algebra.trace S B (ε a) =
    algebraMap R S ((↑u⁻¹ : R) * Algebra.trace R A a)
  rw [freeAlgebraTrace_baseChange b ε h a, map_mul]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Free.AlgebraTraceBaseChange
