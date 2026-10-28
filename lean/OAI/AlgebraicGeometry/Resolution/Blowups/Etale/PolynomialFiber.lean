import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.Hypersurface
import Mathlib.RingTheory.PolynomialAlgebra

/-! # Polynomial Fiber -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.PolynomialFiber.Construction

noncomputable section

/-! Étale polynomial base changes and the actual zero-coordinate fiber. -/

open _root_.Polynomial

attribute [local instance] Polynomial.algebra

variable {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]

/-- Polynomial coefficient extension is étale when the coefficient extension is. -/
theorem etale_polynomial_coefficient_extension [Algebra.Etale A R] :
    Algebra.Etale A[X] R[X] :=
  Algebra.Etale.of_equiv (Algebra.IsPushout.equiv A A[X] R R[X])

variable [Algebra A[X] R] [IsScalarTower A A[X] R] [Algebra.Etale A[X] R]

/-- The zero fiber of an actual étale coordinate is étale over the other coordinates. -/
theorem etale_polynomial_zero_fiber :
    Algebra.Etale A (R ⧸ Ideal.span {algebraMap A[X] R (X : A[X])}) := by
  let I : Ideal A[X] := Ideal.span {X}
  let : Algebra.Etale A (A[X] ⧸ I) := Coordinate.Hypersurface.Construction.polynomial_quotient_X_etale
  let : Algebra.Etale (A[X] ⧸ I) (R ⧸ I.map (algebraMap A[X] R)) :=
    Coordinate.Hypersurface.Construction.etale_quotient_of_etale I
  let : IsScalarTower A (A[X] ⧸ I) (R ⧸ I.map (algebraMap A[X] R)) := by
    apply IsScalarTower.of_algebraMap_eq (R := A) (S := A[X] ⧸ I)
      (A := R ⧸ I.map (algebraMap A[X] R))
    intro a
    rw [IsScalarTower.algebraMap_apply A A[X] (A[X] ⧸ I),
      ← IsScalarTower.algebraMap_apply A[X] (A[X] ⧸ I)]
    exact IsScalarTower.algebraMap_apply A A[X] _ a
  have ht : Algebra.Etale A (R ⧸ I.map (algebraMap A[X] R)) :=
    Algebra.Etale.comp A (A[X] ⧸ I) _
  have he : I.map (algebraMap A[X] R) = Ideal.span {algebraMap A[X] R (X : A[X])} := by
    dsimp only [I]
    rw [Ideal.map_span, Set.image_singleton]
  exact Algebra.Etale.of_equiv (Ideal.quotientEquivAlgOfEq A he)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.PolynomialFiber.Construction
