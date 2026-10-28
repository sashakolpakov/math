import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.FractionBasicOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveCoordinate.GlobalSections

/-! # Basic Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveCoordinate.BasicOpen

noncomputable section

/-! The basic open of a coordinate ratio is the intersection of its two projective charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial _root_.HomogeneousLocalization

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem coordinateRatioSection_singleton_basicOpen (i j : Fin (n + 1)) :
    (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).basicOpen
      (Coordinate.RatioSections.coordinateRatioSection I {i} i j (Finset.mem_singleton_self i)) =
        ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i} ⊓ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {j} := by
  have hf : HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R {i}) ∈ HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I 1 := by
    have hi := HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert.quotient_inversionMonomial_homogeneous I {i}
    simp only [Finset.card_singleton] at hi
    exact hi
  have h := Projective.FractionBasicOpen.projectiveFraction_basicOpen (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) hf Nat.zero_lt_one
    ((HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I).map_mem (isHomogeneous_X R j)) Nat.zero_lt_one
  have hempty : HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R (∅ : Finset (Fin (n + 1))) = 1 := by
    simp [HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial, HilbertScheme.Presentations.LaurentExponents.ProjectiveCech.inversionExponent]
  apply Eq.trans ?_ (congrArg (fun V => ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i} ⊓ V)
    (Cover.coordinateProjectiveChartOpen_singleton I j).symm)
  change (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).basicOpen
    (Proj.awayToSection (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R {i}))
      (Coordinate.HomogeneousRatios.coordinateHomogeneousRatio I {i} i j (Finset.mem_singleton_self i))) =
        Proj.basicOpen (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R {i})) ⊓
          Proj.basicOpen (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (X j))
  unfold Coordinate.HomogeneousRatios.coordinateHomogeneousRatio Homogeneous.FactorRatios.homogeneousFactorRatio
  simp only [Finset.card_singleton, Finset.erase_singleton, hempty, map_one, mul_one]
  simp only [Away.isLocalizationElem, pow_one] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveCoordinate.BasicOpen
