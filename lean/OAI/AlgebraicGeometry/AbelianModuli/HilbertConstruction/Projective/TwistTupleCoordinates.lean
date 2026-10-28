import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.TwistPairAgreement
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.SingletonCoordinates

/-! # Twist Tuple Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.TwistTupleCoordinates

noncomputable section

/-! Regular-function coefficients in the standard degree-d frames give all one-chart homogeneous Čech cochains. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def coordinateTwistTupleCechEquiv (d : ℕ) :
    ((i : Fin (n + 1)) → Coefficient.AlgebraPresheaf.coefficientAlgebraSections
      (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))
      (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i})) ≃ₗ[R]
    HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := Fin (n + 1)) R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
      (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ) 1 :=
  (LinearEquiv.piCongrRight (fun i => ProjectiveChart.PowerFrames.coordinateChartPowerSectionEquiv I {i} i
    (Finset.mem_singleton_self i) d)).trans
    (Cech.SingletonCoordinates.moduleCechOneTermEquiv R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ)).symm

theorem coordinateTwistTupleCechEquiv_singleton (d : ℕ)
    (x : (i : Fin (n + 1)) → Coefficient.AlgebraPresheaf.coefficientAlgebraSections
      (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))) (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}))
    (i : Fin (n + 1)) :
    (coordinateTwistTupleCechEquiv I d x).val {i} =
      (ProjectiveChart.PowerFrames.coordinateChartPowerSectionEquiv I {i} i (Finset.mem_singleton_self i) d (x i)).val := by
  let e := Cech.SingletonCoordinates.moduleCechOneTermEquiv (σ := Fin (n + 1)) R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
    (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ)
  let y := fun j => ProjectiveChart.PowerFrames.coordinateChartPowerSectionEquiv I {j} j (Finset.mem_singleton_self j) d (x j)
  exact (Cech.SingletonCoordinates.moduleCechOneTermEquiv_apply R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
    (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ) (e.symm y) i).symm.trans
    (congrArg (fun z => (z i).val) (e.apply_symm_apply y))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.TwistTupleCoordinates
