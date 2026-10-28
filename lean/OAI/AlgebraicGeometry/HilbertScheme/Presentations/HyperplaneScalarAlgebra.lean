import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.Hyperplane
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IntegerKillVariables

/-! # Hyperplane Scalar Algebra -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.HyperplaneScalarAlgebra.GradedHilbert

noncomputable section

/-! The smaller coordinate quotient as an actual module over the original polynomial ring. -/

open _root_.MvPolynomial

universe u

variable (R : Type u) [CommRing R] (n : ℕ)

@[instance_reducible]
def coordinateDeletionAlgebra : Algebra (Hilbert.Polynomial.GradedHilbert.CoordinateRing R (n + 1)) (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) :=
  (Coordinate.Hyperplane.GradedHilbert.forgetZeroCoordinate R n).toRingHom.toAlgebra

attribute [local instance] coordinateDeletionAlgebra

theorem coordinateDeletion_algebraMap :
    algebraMap (Hilbert.Polynomial.GradedHilbert.CoordinateRing R (n + 1)) (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) =
      (Coordinate.Hyperplane.GradedHilbert.forgetZeroCoordinate R n).toRingHom := rfl

instance coordinateDeletion_scalarTower : IsScalarTower R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R (n + 1)) (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) :=
  IsScalarTower.of_algHom (Coordinate.Hyperplane.GradedHilbert.forgetZeroCoordinate R n)

variable {R n} (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R (n + 1)))

def coordinateHyperplanePolynomialEquiv :
    (Hilbert.Polynomial.GradedHilbert.CoordinateRing R (n + 1) ⧸ (Linear.FormQuotient.GradedHilbert.linearFormQuotientIdeal I (X 0) (isHomogeneous_X R 0)).toIdeal) ≃ₗ[Hilbert.Polynomial.GradedHilbert.CoordinateRing R (n + 1)]
      Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ (Coordinate.Hyperplane.GradedHilbert.coordinateHyperplaneIdeal I).toIdeal where
  __ := (Coordinate.Hyperplane.GradedHilbert.coordinateHyperplaneQuotientEquiv I).toAddEquiv
  map_smul' a x := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Coordinate.Hyperplane.GradedHilbert.coordinateHyperplaneQuotientEquiv I (Ideal.Quotient.mk _ (a * p)) =
      Ideal.Quotient.mk _ ((Coordinate.Hyperplane.GradedHilbert.forgetZeroCoordinate R n a) * (Coordinate.Hyperplane.GradedHilbert.forgetZeroCoordinate R n p))
    rw [Coordinate.Hyperplane.GradedHilbert.coordinateHyperplaneQuotientEquiv_mk, map_mul]

theorem coordinateHyperplanePolynomialEquiv_homogeneous (d : ℤ)
    (x : Hilbert.Polynomial.GradedHilbert.CoordinateRing R (n + 1) ⧸ (Linear.FormQuotient.GradedHilbert.linearFormQuotientIdeal I (X 0) (isHomogeneous_X R 0)).toIdeal)
    (hx : x ∈ Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (Linear.FormQuotient.GradedHilbert.linearFormQuotientIdeal I (X 0) (isHomogeneous_X R 0)) d) :
    coordinateHyperplanePolynomialEquiv I x ∈ Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (Coordinate.Hyperplane.GradedHilbert.coordinateHyperplaneIdeal I) d := by
  obtain ⟨p, hp, rfl⟩ := hx
  exact ⟨Coordinate.Hyperplane.GradedHilbert.forgetZeroCoordinate R n p, IntegerKillVariables.GradedHilbert.killVariables_integer_homogeneous _ hp, rfl⟩

instance coordinateHyperplane_gradedSMul :
    SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := Fin (n + 1 + 1)) R)
      (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (Coordinate.Hyperplane.GradedHilbert.coordinateHyperplaneIdeal I)) where
  smul_mem {i j} a b ha hb := by
    rw [← algebraMap_smul (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n)]
    exact SetLike.GradedSMul.smul_mem (IntegerKillVariables.GradedHilbert.killVariables_integer_homogeneous _ ha) hb

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.HyperplaneScalarAlgebra.GradedHilbert
