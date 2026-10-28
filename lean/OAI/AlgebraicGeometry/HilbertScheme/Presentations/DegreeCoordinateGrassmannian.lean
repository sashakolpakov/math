import OAI.AlgebraicGeometry.HilbertScheme.Presentations.DegreeCoordinateRelations
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.LinearTransport
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.GrassmannianBaseChange

/-! # Degree Coordinate Grassmannian -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.DegreeCoordinateGrassmannian.GradedHilbert

noncomputable section

/-! Actual Grassmannian quotients of homogeneous pieces in fixed monomial
coordinates, with comparison under arbitrary coefficient base change. -/

universe u
variable {R A : Type u} [CommRing R] [CommRing A] {n N k : ℕ}

def degreeCoordinateGrassmannian (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    [Module.Projective R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal N)]
    (hr : ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal N) p = k) :
    Module.Grassmannian R (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N → R) k :=
  Presentations.Grassmannian.LinearTransport.grassmannianLinearTransport (Homogeneous.CoordinateBasis.GradedHilbert.coordinateDegreeBasis R n N).equivFun {
    toSubmodule := Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal N
    finite_quotient := inferInstance
    projective_quotient := inferInstance
    rankAtStalk_eq := hr }

theorem degreeCoordinateGrassmannian_toSubmodule (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    [Module.Projective R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal N)]
    (hr : ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal N) p = k) :
    (degreeCoordinateGrassmannian I hr).toSubmodule = DegreeCoordinateRelations.GradedHilbert.degreeCoordinateRelations I N := rfl

theorem degreeCoordinateGrassmannian_baseChange_eq [Algebra R A]
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (J : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading A n))
    [Module.Projective R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal N)] [Module.Projective A (Hilbert.Polynomial.GradedHilbert.DegreeQuotient J.toIdeal N)]
    (hR : ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal N) p = k)
    (hA : ∀ p : PrimeSpectrum A, Module.rankAtStalk (R := A) (Hilbert.Polynomial.GradedHilbert.DegreeQuotient J.toIdeal N) p = k)
    (h : Hilbert.Polynomial.GradedHilbert.degreeRelations (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I).toIdeal N = Hilbert.Polynomial.GradedHilbert.degreeRelations J.toIdeal N) :
    Coordinate.GrassmannianBaseChange.Grassmannian.coordinateGrassmannianMap (algebraMap R A) (degreeCoordinateGrassmannian I hR) =
      degreeCoordinateGrassmannian J hA := by
  apply Module.Grassmannian.ext
  change Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (algebraMap R A) (DegreeCoordinateRelations.GradedHilbert.degreeCoordinateRelations I N) = DegreeCoordinateRelations.GradedHilbert.degreeCoordinateRelations J N
  rw [DegreeCoordinateRelations.GradedHilbert.degreeCoordinateRelations_baseChange]
  exact congrArg (Submodule.map (Homogeneous.CoordinateBasis.GradedHilbert.coordinateDegreeBasis A n N).equivFun.toLinearMap) h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.DegreeCoordinateGrassmannian.GradedHilbert
