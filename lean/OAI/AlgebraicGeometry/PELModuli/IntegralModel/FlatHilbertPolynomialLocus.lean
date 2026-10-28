import OAI.AlgebraicGeometry.PELModuli.IntegralModel.UniformFiberHilbertFunction
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.Coordinates
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.Polynomial
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-! # Flat Hilbert Polynomial Locus -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FlatHilbertPolynomialLocus.PolarizationEmbedding

noncomputable section

/-! The locus of each actual residue-fiber Hilbert polynomial is open
and closed in a flat noetherian projective family. -/

open _root_.AlgebraicGeometry

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))
    [Flat (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))]

theorem isClopen_residue_hilbertPolynomial (P : Polynomial ℚ) :
    IsClopen {p : PrimeSpectrum R | HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
      (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I).toIdeal P} := by
  classical
  obtain ⟨b, hb⟩ := UniformFiberHilbertFunction.PolarizationEmbedding.exists_uniform_field_specialization_hilbertFunction.{u, u} I
  obtain ⟨c, hc⟩ := HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert.eventual_coordinatePieces_flat_of_projective_flat I
  let a := max b c
  have hflat (i : Fin (n + 1)) : Module.Flat R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal (a + i.val)) :=
    hc _ ((le_max_right b c).trans (Nat.le_add_right _ _))
  have heq : {p : PrimeSpectrum R | HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
      (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I).toIdeal P} =
      {p : PrimeSpectrum R | P.natDegree ≤ n ∧ ∀ i : Fin (n + 1),
        (Module.rankAtStalk (R := R) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal (a + i.val)) p : ℚ) =
          P.eval ((a + i.val : ℕ) : ℚ)} := by
    ext p
    have h := UniformFiberHilbertFunction.PolarizationEmbedding.hilbertPolynomial_iff_uniform_values I hb (algebraMap R p.asIdeal.ResidueField)
      P a (le_max_left b c)
    change HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (I.map (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap (algebraMap R p.asIdeal.ResidueField))).toIdeal P ↔ _
    rw [h]
    apply and_congr_right
    intro _
    apply forall_congr'
    intro i
    let := hflat i
    rw [HilbertScheme.Presentations.Relative.Coordinates.GradedHilbert.degreeQuotient_rankAtStalk]
    rfl
  rw [heq]
  by_cases hdeg : P.natDegree ≤ n
  · have hsets : {p : PrimeSpectrum R | P.natDegree ≤ n ∧ ∀ i : Fin (n + 1),
        (Module.rankAtStalk (R := R) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal (a + i.val)) p : ℚ) =
          P.eval ((a + i.val : ℕ) : ℚ)} =
        ⋂ i : Fin (n + 1), {p : PrimeSpectrum R |
          (Module.rankAtStalk (R := R) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal (a + i.val)) p : ℚ) =
            P.eval ((a + i.val : ℕ) : ℚ)} := by
      ext p
      simp only [Set.mem_ofPred_eq, hdeg, true_and, Set.mem_iInter]
    rw [hsets]
    apply isClopen_iInter_of_finite
    intro i
    let := hflat i
    let : Module.FinitePresentation R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal (a + i.val)) :=
      Module.finitePresentation_of_finite R _
    exact (Module.isLocallyConstant_rankAtStalk
      (R := R) (M := HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal (a + i.val))).comp
        (fun r : ℕ => (r : ℚ)) |>.isClopen_fiber _
  · simpa only [hdeg, false_and, Set.ofPred_false] using
      (isClopen_empty : IsClopen (∅ : Set (PrimeSpectrum R)))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FlatHilbertPolynomialLocus.PolarizationEmbedding
