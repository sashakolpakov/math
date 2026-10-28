import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.AffineObstructionFlatness
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ChartPresentation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Properness

/-! # Chart Obstruction Flatness -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ChartObstructionFlatness.GradedHilbert

noncomputable section

/-! Actual projective quotients over a Noetherian local ring satisfy
the proper affine-chart obstruction criterion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomogeneousLocalization _root_.MvPolynomial

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}

abbrev projectiveCoordinateChart (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (i : Fin (n + 1)) :=
  HomogeneousLocalization.Away (Graded.Quotient.GradedHilbert.quotientGrading I) (Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i))

theorem projectiveCoordinateChart_noetherian (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (i : Fin (n + 1)) : IsNoetherianRing (projectiveCoordinateChart I i) :=
  isNoetherianRing_of_ringEquiv (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ Affine.ChartPresentation.GradedHilbert.affineChartIdeal I i)
    (Affine.ChartPresentation.GradedHilbert.affineChartPresentationAlgEquiv I i).toRingEquiv

theorem projectiveQuotient_flat_of_chart_idealTensor [IsLocalRing R]
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (J : Ideal R) (hJ : J ≠ ⊤)
    (hred : ∀ i, Module.Flat (R ⧸ J)
      (projectiveCoordinateChart I i ⧸ J.map (algebraMap R (projectiveCoordinateChart I i))))
    (hinj : ∀ i, Function.Injective (IdealTensor.Obstruction.idealTensorMultiplication R R (projectiveCoordinateChart I i) J)) :
    Flat (Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I)) := by
  let C := Proj.affineOpenCoverOfIrrelevantLESpan (Graded.Quotient.GradedHilbert.quotientGrading I)
    (fun i : Fin (n + 1) => Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i))
    (fun i => (Graded.Quotient.GradedHilbert.gradedQuotientMap I).map_mem (isHomogeneous_X R i))
    (fun _ => Nat.zero_lt_one) (Flatness.GradedHilbert.quotient_irrelevant_le_span_variables I)
  let : IsProper (Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I)) := Properness.GradedHilbert.projectiveQuotient_proper I
  let : ∀ i, Algebra R (C.X i) := fun i =>
    inferInstanceAs (Algebra R (projectiveCoordinateChart I i))
  let : ∀ i, IsNoetherianRing (C.X i) := fun i => projectiveCoordinateChart_noetherian I i
  let : ∀ i, Module.Flat (R ⧸ J) ((C.X i) ⧸ J.map (algebraMap R (C.X i))) := hred
  apply Proper.AffineObstructionFlatness.proper_flat_of_affine_idealTensor_injective (.of R)
    (Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I)) C (fun i => ?_) J hJ hinj
  exact (Flatness.GradedHilbert.projectiveStructureMap_away (Graded.Quotient.GradedHilbert.quotientGrading I)
    ((Graded.Quotient.GradedHilbert.gradedQuotientMap I).map_mem (isHomogeneous_X R i))).symm

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ChartObstructionFlatness.GradedHilbert
