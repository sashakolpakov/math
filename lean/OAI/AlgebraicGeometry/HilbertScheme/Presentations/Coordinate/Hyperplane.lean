import OAI.AlgebraicGeometry.HilbertScheme.Presentations.KillVariables
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.FormQuotient
import Mathlib.Data.Fin.SuccPred

/-! # Hyperplane -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.Hyperplane.GradedHilbert

noncomputable section

/-! A coordinate hyperplane quotient is the actual polynomial coordinate quotient in one fewer variable. -/

open _root_.MvPolynomial

universe u

variable (R : Type u) [CommRing R] (n : ℕ)

def forgetZeroCoordinate : Hilbert.Polynomial.GradedHilbert.CoordinateRing R (n + 1) →ₐ[R] Hilbert.Polynomial.GradedHilbert.CoordinateRing R n :=
  MvPolynomial.killCompl (Fin.succ_injective (n := n + 1))

theorem forgetZeroCoordinate_surjective : Function.Surjective (forgetZeroCoordinate R n) :=
  KillVariables.GradedHilbert.killVariables_surjective _

theorem forgetZeroCoordinate_kernel :
    RingHom.ker (forgetZeroCoordinate R n).toRingHom = Ideal.span {X 0} := by
  rw [forgetZeroCoordinate, KillVariables.GradedHilbert.killVariables_kernel, Fin.range_succ, compl_compl, Set.image_singleton]

theorem forgetZeroCoordinate_homogeneous {p : Hilbert.Polynomial.GradedHilbert.CoordinateRing R (n + 1)} {d : ℕ}
    (hp : p.IsHomogeneous d) : (forgetZeroCoordinate R n p).IsHomogeneous d :=
  KillVariables.GradedHilbert.killVariables_homogeneous _ hp

def forgetZeroCoordinateGraded : Hilbert.Polynomial.GradedHilbert.grading R (n + 1) →+*ᵍ Hilbert.Polynomial.GradedHilbert.grading R n where
  __ := (forgetZeroCoordinate R n).toRingHom
  map_mem := forgetZeroCoordinate_homogeneous R n

variable {R n}

def coordinateHyperplaneIdeal (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R (n + 1))) :
    HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n) := I.map (forgetZeroCoordinateGraded R n)

def coordinateHyperplaneMap (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R (n + 1))) :
    Hilbert.Polynomial.GradedHilbert.CoordinateRing R (n + 1) →ₐ[R] Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ (coordinateHyperplaneIdeal I).toIdeal :=
  (Ideal.Quotient.mkₐ R (coordinateHyperplaneIdeal I).toIdeal).comp (forgetZeroCoordinate R n)

theorem coordinateHyperplaneMap_surjective (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R (n + 1))) :
    Function.Surjective (coordinateHyperplaneMap I) :=
  (Ideal.Quotient.mk_surjective).comp (forgetZeroCoordinate_surjective R n)

theorem coordinateHyperplaneMap_kernel (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R (n + 1))) :
    RingHom.ker (coordinateHyperplaneMap I).toRingHom =
      (Linear.FormQuotient.GradedHilbert.linearFormQuotientIdeal I (X 0) (isHomogeneous_X R 0)).toIdeal := by
  change RingHom.ker ((Ideal.Quotient.mk (coordinateHyperplaneIdeal I).toIdeal).comp
    (forgetZeroCoordinate R n).toRingHom) = I.toIdeal ⊔ Ideal.span {X 0}
  rw [← RingHom.comap_ker, Ideal.mk_ker]
  change (I.toIdeal.map (forgetZeroCoordinate R n).toRingHom).comap
    (forgetZeroCoordinate R n).toRingHom = _
  rw [Ideal.comap_map_of_surjective (forgetZeroCoordinate R n).toRingHom
    (forgetZeroCoordinate_surjective R n),
    ← RingHom.ker_eq_comap_bot, forgetZeroCoordinate_kernel]

def coordinateHyperplaneQuotientEquiv (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R (n + 1))) :
    (Hilbert.Polynomial.GradedHilbert.CoordinateRing R (n + 1) ⧸ (Linear.FormQuotient.GradedHilbert.linearFormQuotientIdeal I (X 0) (isHomogeneous_X R 0)).toIdeal) ≃ₐ[R]
      Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ (coordinateHyperplaneIdeal I).toIdeal :=
  (Ideal.quotientEquivAlgOfEq R (coordinateHyperplaneMap_kernel I).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (coordinateHyperplaneMap_surjective I))

theorem coordinateHyperplaneQuotientEquiv_mk (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R (n + 1)))
    (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing R (n + 1)) :
    coordinateHyperplaneQuotientEquiv I
      (Ideal.Quotient.mk (Linear.FormQuotient.GradedHilbert.linearFormQuotientIdeal I (X 0) (isHomogeneous_X R 0)).toIdeal f) =
      Ideal.Quotient.mk (coordinateHyperplaneIdeal I).toIdeal (forgetZeroCoordinate R n f) := rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.Hyperplane.GradedHilbert
