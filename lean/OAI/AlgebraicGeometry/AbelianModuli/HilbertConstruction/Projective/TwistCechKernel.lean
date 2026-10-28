import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.TwistTupleCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.AllPairCompatibility

/-! # Twist Cech Kernel -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.TwistCechKernel

noncomputable section

/-! The homogeneous Čech kernel is exactly the system of degree-d projective transition equations on coordinate-pair charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def CoordinateTwistCompatible (d : ℕ)
    (x : (i : Fin (n + 1)) → Coefficient.AlgebraPresheaf.coefficientAlgebraSections
      (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))) (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i})) : Prop :=
  ∀ i j, (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).presheaf.map (homOfLE (ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I
      (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self i {j})))).op (x i) =
    Coordinate.RatioSections.coordinateRatioSection I {i, j} i j (Finset.mem_insert_self i {j}) ^ d *
      (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).presheaf.map (homOfLE (ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I
        (Finset.singleton_subset_iff.mpr (Finset.mem_insert_of_mem (Finset.mem_singleton_self j))))).op (x j)

theorem coordinateTwistTupleCechEquiv_kernel_iff (d : ℕ)
    (x : (i : Fin (n + 1)) → Coefficient.AlgebraPresheaf.coefficientAlgebraSections
      (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))) (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i})) :
    TwistTupleCoordinates.coordinateTwistTupleCechEquiv I d x ∈
      (HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := Fin (n + 1)) R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
        (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ) 1).ker ↔ CoordinateTwistCompatible I d x := by
  refine (Cech.AllPairCompatibility.moduleCech_one_cocycle_iff_all R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
    (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ) (TwistTupleCoordinates.coordinateTwistTupleCechEquiv I d x)).trans ?_
  apply forall₂_congr
  intro i j
  exact (congrArg₂ Eq
    (congrArg (Cech.PairDifferential.moduleCechPairRestrictionLeft R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) i j)
      (TwistTupleCoordinates.coordinateTwistTupleCechEquiv_singleton I d x i))
    (congrArg (Cech.PairDifferential.moduleCechPairRestrictionRight R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) i j)
      (TwistTupleCoordinates.coordinateTwistTupleCechEquiv_singleton I d x j))).to_iff.trans
        (TwistPairAgreement.coordinateTwistPairAgreement_iff I i j d (x i) (x j))

def coordinateTwistCompatibleModule (d : ℕ) : Submodule R
    ((i : Fin (n + 1)) → Coefficient.AlgebraPresheaf.coefficientAlgebraSections
      (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))) (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i})) :=
  (HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := Fin (n + 1)) R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
    (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ) 1).ker.comap (TwistTupleCoordinates.coordinateTwistTupleCechEquiv I d).toLinearMap

theorem coordinateTwistCompatibleModule_mem (d : ℕ)
    (x : (i : Fin (n + 1)) → Coefficient.AlgebraPresheaf.coefficientAlgebraSections
      (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))) (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i})) :
    x ∈ coordinateTwistCompatibleModule I d ↔ CoordinateTwistCompatible I d x :=
  coordinateTwistTupleCechEquiv_kernel_iff I d x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.TwistCechKernel
