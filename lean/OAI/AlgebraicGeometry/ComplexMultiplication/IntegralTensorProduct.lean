import OAI.AlgebraicGeometry.ComplexMultiplication.ClosedPoints
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Nontrivial
import Mathlib.Algebra.Ring.Basic

/-! # Integral Tensor Product -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.IntegralTensorProduct

noncomputable section

/-! # Integral tensor products over an algebraically closed field

The proof specializes finitely many coefficients at an actual rational point.
It will be used to derive geometric group properties from the original assumptions.
-/

open scoped TensorProduct

variable {K A B : Type*} [Field K] [IsAlgClosed K]
  [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A]
  [CommRing B] [IsDomain B] [Algebra K B]

/-- Evaluation in the first factor is an actual algebra homomorphism. -/
def tensorEvaluation (f : A →ₐ[K] K) : A ⊗[K] B →ₐ[K] B :=
  (Algebra.TensorProduct.lid K B).toAlgHom.comp
    (Algebra.TensorProduct.map f (AlgHom.id K B))

omit [IsAlgClosed K] [IsDomain A] [Algebra.FiniteType K A] [IsDomain B] in
theorem tensorEvaluation_coordinate {ι : Type*} [DecidableEq ι] (b : Module.Basis ι K B)
    (f : A →ₐ[K] K) (t : A ⊗[K] B) (i : ι) :
    b.repr (tensorEvaluation f t) i =
      f (TensorProduct.equivFinsuppOfBasisRight b t i) := by
  induction t using TensorProduct.inductionOn with
  | tmul a z =>
      simp [tensorEvaluation, mul_comm]
  | add x y hx hy => simp [hx, hy]

/-- The tensor product of a finite-type domain with a domain over an algebraically
closed field has no zero divisors. -/
theorem integralTensorProduct_noZeroDivisors : NoZeroDivisors (A ⊗[K] B) := by
  classical
  let b := Module.Free.chooseBasis K B
  let e := TensorProduct.equivFinsuppOfBasisRight (M := A) b
  have coeff_nonzero (t : A ⊗[K] B) (ht : t ≠ 0) : ∃ i, e t i ≠ 0 := by
    by_contra h
    have hz : e t = 0 := by
      ext i
      exact not_ne_iff.mp (not_exists.mp h i)
    exact ht (e.injective (hz.trans e.map_zero.symm))
  refine ⟨fun {u v} huv => ?_⟩
  by_cases hu : u = 0
  · exact Or.inl hu
  by_cases hv : v = 0
  · exact Or.inr hv
  obtain ⟨i, hi⟩ := coeff_nonzero u hu
  obtain ⟨j, hj⟩ := coeff_nonzero v hv
  obtain ⟨f, hf⟩ := ClosedPoints.exists_algHom_ne_zero (K := K) (e u i * e v j) (mul_ne_zero hi hj)
  have hcoeff : f (e u i) * f (e v j) ≠ 0 := by simpa using hf
  have hfu : tensorEvaluation f u ≠ 0 := by
    intro h
    apply left_ne_zero_of_mul hcoeff
    rw [← tensorEvaluation_coordinate b f u i, h]
    simp
  have hfv : tensorEvaluation f v ≠ 0 := by
    intro h
    apply right_ne_zero_of_mul hcoeff
    rw [← tensorEvaluation_coordinate b f v j, h]
    simp
  have hz : tensorEvaluation f u * tensorEvaluation f v = 0 := by
    rw [← map_mul, huv, map_zero]
  exact False.elim ((mul_ne_zero hfu hfv) hz)

/-- No extra geometric-integrality assumption is needed for these algebras. -/
theorem integralTensorProduct_isDomain : IsDomain (A ⊗[K] B) := by
  let : NoZeroDivisors (A ⊗[K] B) := integralTensorProduct_noZeroDivisors
  let : Nontrivial (A ⊗[K] B) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain K A B
      (algebraMap K A).injective (algebraMap K B).injective
  exact NoZeroDivisors.to_isDomain _

end

end OAI.AlgebraicGeometry.ComplexMultiplication.IntegralTensorProduct
