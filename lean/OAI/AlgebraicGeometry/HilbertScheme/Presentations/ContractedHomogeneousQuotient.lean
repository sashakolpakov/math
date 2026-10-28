import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.BaseChange
import Mathlib.RingTheory.Flat.TorsionFree

/-! # Contracted Homogeneous Quotient -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ContractedHomogeneousQuotient.GradedHilbert

noncomputable section

/-! Contract a homogeneous ideal along a coefficient extension. The actual
quotient embeds in the original quotient, so torsion-freeness descends. -/

universe u v
variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A] {n : ℕ}

def contractedHomogeneousIdeal (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading A n)) : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n) :=
  I.comap (Graded.BaseChange.GradedHilbert.gradedCoefficientMap (algebraMap R A))

def contractedQuotientMap (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading A n)) :
    (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ (contractedHomogeneousIdeal I).toIdeal) →ₐ[R]
      Hilbert.Polynomial.GradedHilbert.CoordinateRing A n ⧸ I.toIdeal :=
  Ideal.quotientMapₐ I.toIdeal (MvPolynomial.mapAlgHom (Algebra.ofId R A)) le_rfl

theorem contractedQuotientMap_injective (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading A n)) :
    Function.Injective (contractedQuotientMap (R := R) I) := Ideal.quotientMap_injective

theorem contractedQuotient_isTorsionFree (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading A n))
    [Module.IsTorsionFree R (Hilbert.Polynomial.GradedHilbert.CoordinateRing A n ⧸ I.toIdeal)] :
    Module.IsTorsionFree R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ (contractedHomogeneousIdeal I).toIdeal) :=
  Function.Injective.moduleIsTorsionFree (contractedQuotientMap I)
    (contractedQuotientMap_injective I) (fun r x => map_smul (contractedQuotientMap I) r x)

theorem contractedDegreeQuotient_isTorsionFree (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading A n))
    [Module.IsTorsionFree R (Hilbert.Polynomial.GradedHilbert.CoordinateRing A n ⧸ I.toIdeal)] (d : ℕ) :
    Module.IsTorsionFree R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (contractedHomogeneousIdeal (R := R) I).toIdeal d) := by
  let := contractedQuotient_isTorsionFree (R := R) I
  let J := contractedHomogeneousIdeal (R := R) I
  let e := Graded.Quotient.GradedHilbert.degreeQuotientEquivQuotientGrading J d
  exact Function.Injective.moduleIsTorsionFree e e.injective (fun r x => e.map_smul r x)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ContractedHomogeneousQuotient.GradedHilbert
