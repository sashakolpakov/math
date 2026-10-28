import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DenseCoefficientRanks
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.FiberFunction
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.Polynomial
import Mathlib.Topology.Instances.Rat

/-! # Dense Polynomial Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DensePolynomialDescent

noncomputable section

/-! A flat projective family over a noetherian ring inherits its Hilbert polynomial from any injective coefficient extension. -/

open _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.Polynomial.GradedHilbert

universe u

theorem noetherianFlat_hilbertPolynomial_dense_descent
    {C A : Type u} [CommRing C] [IsNoetherianRing C] [CommRing A] [Algebra C A]
    (hinj : Function.Injective (algebraMap C A))
    {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading C n))
    [Flat (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))]
    (P : Polynomial ℚ)
    (hP : ∀ q : PrimeSpectrum A, HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
      (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := q.asIdeal.ResidueField)
        (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I))).toIdeal P)
    (p : PrimeSpectrum C) : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
      (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I)).toIdeal P := by
  apply (HilbertScheme.Presentations.Saturation.Polynomial.GradedHilbert.projectiveSaturation_hasHilbertPolynomial_iff _ P).mpr
  refine ⟨HilbertScheme.Presentations.Flat.FamilyCoordinates.GradedHilbert.flatFamilyHilbertDegree I P, fun d hd => ?_⟩
  have hdB : HilbertScheme.Presentations.Projective.FamilyCoordinateBound.GradedHilbert.projectiveFamilyCoordinateBound I ≤ d := (le_max_left _ _).trans hd
  have : Module.Projective C (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) := HilbertScheme.Presentations.Flat.FamilyCoordinates.GradedHilbert.coordinateBound_degreeQuotient_projective I d hdB
  have : Module.FinitePresentation C (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) :=
    Module.finitePresentation_of_finite C (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d)
  have h := DenseCoefficientRanks.finiteFlat_rankAtStalk_dense_value (algebraMap C A) hinj
    (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) (P.eval (d : ℚ)) (fun k : ℕ => (k : ℚ))
    (fun q => Noetherian.FiberFunction.coefficientFiber_rank_eq_polynomial I P q (hP q) d hd) p
  rw [HilbertScheme.Presentations.Relative.Coordinates.GradedHilbert.degreeQuotient_rankAtStalk] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DensePolynomialDescent
