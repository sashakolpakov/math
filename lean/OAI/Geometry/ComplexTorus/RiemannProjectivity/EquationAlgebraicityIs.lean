import OAI.Geometry.ComplexTorus.RiemannProjectivity.JacobianLocalizationAt

/-! # Equation Algebraicity Is -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.EquationAlgebraicityIs.Constructions.EquationAlgebraicity

noncomputable section

/-! # RiemannProjectivity: the coordinate-equation algebra is algebraic over the projection base -/

open _root_.Polynomial
open OAI.Geometry.ComplexTorus.RiemannProjectivity.JacobianLocalizationAt.Constructions.SmoothEquationPoint OAI.Geometry.ComplexTorus.RiemannProjectivity.JacobianLocalizationAt.Constructions.SplitPolynomialJacobian

variable {n m : ℕ}

def baseMap (F : Fin m → Polynomial (MvPolynomial (Fin n) ℂ)) :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ] JacobianLocalizationAt.Constructions.SmoothEquationPoint.equationRing F :=
  (Ideal.Quotient.mkₐ ℂ _).comp (MvPolynomial.rename Sum.inl)

instance baseAlgebra (F : Fin m → Polynomial (MvPolynomial (Fin n) ℂ)) :
    Algebra (MvPolynomial (Fin n) ℂ) (JacobianLocalizationAt.Constructions.SmoothEquationPoint.equationRing F) := (baseMap F).toRingHom.toAlgebra

instance baseTower (F : Fin m → Polynomial (MvPolynomial (Fin n) ℂ)) :
    IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) (JacobianLocalizationAt.Constructions.SmoothEquationPoint.equationRing F) :=
  IsScalarTower.of_algHom (baseMap F)

def coordinate (F : Fin m → Polynomial (MvPolynomial (Fin n) ℂ))
    (i : Fin n ⊕ Fin m) : JacobianLocalizationAt.Constructions.SmoothEquationPoint.equationRing F := Ideal.Quotient.mk _ (MvPolynomial.X i)

theorem aeval_coordinate (F : Fin m → Polynomial (MvPolynomial (Fin n) ℂ))
    (j : Fin m) (P : Polynomial (MvPolynomial (Fin n) ℂ)) :
    aeval (coordinate F (Sum.inr j)) P = Ideal.Quotient.mk _ (JacobianLocalizationAt.Constructions.SplitPolynomialJacobian.equation j P) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    have heq : JacobianLocalizationAt.Constructions.SplitPolynomialJacobian.equation j (P + Q) = JacobianLocalizationAt.Constructions.SplitPolynomialJacobian.equation j P + JacobianLocalizationAt.Constructions.SplitPolynomialJacobian.equation j Q := eval₂_add _ _
    rw [map_add, heq, map_add, hP, hQ]
  | monomial k a =>
    simp only [aeval_monomial, JacobianLocalizationAt.Constructions.SplitPolynomialJacobian.equation, eval₂_monomial]
    rfl

theorem coordinate_isAlgebraic (F : Fin m → Polynomial (MvPolynomial (Fin n) ℂ))
    (hF : ∀ j, F j ≠ 0) (i : Fin n ⊕ Fin m) :
    IsAlgebraic (MvPolynomial (Fin n) ℂ) (coordinate F i) := by
  cases i with
  | inl i =>
    have h : coordinate F (Sum.inl i) = algebraMap (MvPolynomial (Fin n) ℂ) (JacobianLocalizationAt.Constructions.SmoothEquationPoint.equationRing F)
        (MvPolynomial.X i) := by
      change Ideal.Quotient.mk _ (MvPolynomial.X (Sum.inl i)) =
        Ideal.Quotient.mk _ ((MvPolynomial.rename Sum.inl) (MvPolynomial.X i))
      rw [MvPolynomial.rename_X]
    rw [h]
    exact isAlgebraic_algebraMap _
  | inr j =>
    refine ⟨F j, hF j, ?_⟩
    rw [aeval_coordinate]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span ⟨j, rfl⟩

theorem isAlgebraic (F : Fin m → Polynomial (MvPolynomial (Fin n) ℂ))
    (hF : ∀ j, F j ≠ 0) : Algebra.IsAlgebraic (MvPolynomial (Fin n) ℂ) (JacobianLocalizationAt.Constructions.SmoothEquationPoint.equationRing F) := by
  constructor
  intro a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  induction p using MvPolynomial.induction_on with
  | C c =>
    have h : Ideal.Quotient.mk _ (MvPolynomial.C c) =
        algebraMap (MvPolynomial (Fin n) ℂ) (JacobianLocalizationAt.Constructions.SmoothEquationPoint.equationRing F) (MvPolynomial.C c) := by
      change Ideal.Quotient.mk _ (MvPolynomial.C c) =
        Ideal.Quotient.mk _ ((MvPolynomial.rename Sum.inl) (MvPolynomial.C c))
      rw [MvPolynomial.rename_C]
    rw [h]
    exact isAlgebraic_algebraMap _
  | add p q hp hq =>
    rw [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    rw [map_mul]
    exact hp.mul (coordinate_isAlgebraic F hF i)

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.EquationAlgebraicityIs.Constructions.EquationAlgebraicity
