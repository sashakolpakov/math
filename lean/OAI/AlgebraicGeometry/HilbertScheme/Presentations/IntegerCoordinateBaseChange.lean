import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.IntegerQuotient
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.BaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorFractionTorsion

/-! # Integer Coordinate Base Change -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.IntegerCoordinateBaseChange.GradedHilbert

noncomputable section

/-! Tensor base change of integer-graded coordinate pieces agrees with the actual quotient ring maps. -/

open _root_.MvPolynomial TensorProduct

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorFractionTorsion.GradedModules

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {n : ℕ}

def integerQuotientGradingBaseChangeEquiv (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (d : ℕ) :
    S ⊗[R] Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I (d : ℤ) ≃ₗ[S]
      Graded.Quotient.GradedHilbert.quotientGrading (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I) d :=
  ((LinearEquiv.ofEq _ _ (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading_nat I d)).baseChange R S).trans
    (Graded.BaseChange.GradedHilbert.quotientGradingBaseChangeEquiv I d)

theorem integerQuotientGradingBaseChangeEquiv_val (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (d : ℕ)
    (x : S ⊗[R] Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I (d : ℤ)) :
    (integerQuotientGradingBaseChangeEquiv (S := S) I d x).val =
      Graded.BaseChange.GradedHilbert.quotientBaseChangeEquiv I (((Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I (d : ℤ)).subtype.lTensor S) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
    simp only [integerQuotientGradingBaseChangeEquiv, LinearEquiv.trans_apply,
      LinearEquiv.baseChange_tmul, LinearMap.lTensor_tmul]
    rfl
  | add x y hx hy => simp only [map_add, Submodule.coe_add, hx, hy]

theorem quotientBaseChangeEquiv_scalar (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (p : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (x : S ⊗[R] (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)) :
    Graded.BaseChange.GradedHilbert.quotientBaseChangeEquiv (S := S) I
      (((TensorFractionTorsion.GradedModules.moduleScalarEnd (R := R) (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) p).lTensor S) x) =
      Ideal.Quotient.mk (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I).toIdeal
        (MvPolynomial.map (algebraMap R S) p) * Graded.BaseChange.GradedHilbert.quotientBaseChangeEquiv I x := by
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective m
    change Graded.BaseChange.GradedHilbert.quotientBaseChangeEquiv I (s ⊗ₜ[R] Ideal.Quotient.mk I.toIdeal (p * f)) = _
    rw [Graded.BaseChange.GradedHilbert.quotientBaseChangeEquiv_tmul, Graded.BaseChange.GradedHilbert.quotientBaseChangeEquiv_tmul]
    rw [← map_mul]
    congr 1
    rw [map_mul, mul_smul_comm]
  | add x y hx hy => simp only [map_add, mul_add, hx, hy]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.IntegerCoordinateBaseChange.GradedHilbert
