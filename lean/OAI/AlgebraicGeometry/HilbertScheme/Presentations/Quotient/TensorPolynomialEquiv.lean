import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.BaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.IntegerQuotient
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.ScalarRestriction
import Mathlib.LinearAlgebra.TensorProduct.Decomposition

/-! # Tensor Polynomial Equiv -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.TensorPolynomialEquiv.GradedHilbert

noncomputable section

/-! Tensor base change of the actual homogeneous quotient is polynomial-linear and preserves every integer homogeneous degree. -/

open _root_.MvPolynomial TensorProduct DirectSum

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.ScalarRestriction.GradedModules

universe u v

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S] {n : ℕ}

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))

def quotientTensorPolynomialEquiv :
    ((Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) ⊗[R] S) ≃ₗ[Hilbert.Polynomial.GradedHilbert.CoordinateRing R n]
      Hilbert.Polynomial.GradedHilbert.CoordinateRing S n ⧸ (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I).toIdeal where
  __ := ((TensorProduct.comm R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) S).trans
    ((Graded.BaseChange.GradedHilbert.quotientBaseChangeEquiv (S := S) I).toLinearEquiv.restrictScalars R)).toAddEquiv
  map_smul' a x := by
    let E := (TensorProduct.comm R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) S).trans
      ((Graded.BaseChange.GradedHilbert.quotientBaseChangeEquiv (S := S) I).toLinearEquiv.restrictScalars R)
    change E (a • x) = a • E x
    induction x using TensorProduct.inductionOn with
    | tmul m s =>
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective m
      change Graded.BaseChange.GradedHilbert.quotientBaseChangeEquiv I (s ⊗ₜ[R] Ideal.Quotient.mk I.toIdeal (a * p)) =
        a • Graded.BaseChange.GradedHilbert.quotientBaseChangeEquiv I (s ⊗ₜ[R] Ideal.Quotient.mk I.toIdeal p)
      rw [Graded.BaseChange.GradedHilbert.quotientBaseChangeEquiv_tmul, Graded.BaseChange.GradedHilbert.quotientBaseChangeEquiv_tmul]
      change Ideal.Quotient.mk _ (s • MvPolynomial.map (algebraMap R S) (a * p)) =
        Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap R S) a * (s • MvPolynomial.map (algebraMap R S) p))
      rw [map_mul, mul_smul_comm]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem quotientTensorPolynomialEquiv_tmul (m : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (s : S) :
    quotientTensorPolynomialEquiv (S := S) I (m ⊗ₜ[R] s) = Graded.BaseChange.GradedHilbert.quotientBaseChangeEquiv I (s ⊗ₜ[R] m) := rfl

theorem quotientTensorPolynomialEquiv_homogeneous (d : ℤ)
    (x : (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) ⊗[R] S)
    (hx : x ∈ decomposeTensor (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) S d) :
    quotientTensorPolynomialEquiv (S := S) I x ∈ Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I) d := by
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.inductionOn with
  | tmul m s =>
    obtain ⟨p, hp, hpm⟩ := m.property
    change Ideal.Quotient.mk I.toIdeal p = m.val at hpm
    change Graded.BaseChange.GradedHilbert.quotientBaseChangeEquiv I (s ⊗ₜ[R] m.val) ∈
      Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I) d
    rw [← hpm, Graded.BaseChange.GradedHilbert.quotientBaseChangeEquiv_tmul]
    exact ⟨s • MvPolynomial.map (algebraMap R S) p,
      Submodule.smul_mem _ s (Graded.ScalarRestriction.GradedModules.coefficientMap_integer_homogeneous hp), rfl⟩
  | add x y hx hy =>
    simp only [map_add]
    exact Submodule.add_mem _ hx hy

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.TensorPolynomialEquiv.GradedHilbert
