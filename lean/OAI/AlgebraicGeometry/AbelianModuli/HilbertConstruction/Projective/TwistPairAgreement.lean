import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PowerFrameChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PowerFrameRestrictions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.PairCompatibility

/-! # Twist Pair Agreement -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.TwistPairAgreement

noncomputable section

/-! Equality of homogeneous sections on a two-coordinate chart is precisely the twisting transition equation for their regular-function coefficients. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem coordinateTwistPairAgreement_iff (i j : Fin (n + 1)) (d : ℕ)
    (x : Γ(Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I), ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}))
    (y : Γ(Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I), ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {j})) :
    Cech.PairDifferential.moduleCechPairRestrictionLeft R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) i j
        (ProjectiveChart.PowerFrames.coordinateChartPowerSectionEquiv I {i} i (Finset.mem_singleton_self i) d x).val =
      Cech.PairDifferential.moduleCechPairRestrictionRight R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) i j
        (ProjectiveChart.PowerFrames.coordinateChartPowerSectionEquiv I {j} j (Finset.mem_singleton_self j) d y).val ↔
    (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).presheaf.map (homOfLE (ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I
      (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self i {j})))).op x =
      Coordinate.RatioSections.coordinateRatioSection I {i, j} i j (Finset.mem_insert_self i {j}) ^ d *
      (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).presheaf.map (homOfLE (ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I
        (Finset.singleton_subset_iff.mpr (Finset.mem_insert_of_mem (Finset.mem_singleton_self j))))).op y := by
  let hL : ({i} : Finset (Fin (n + 1))) ⊆ {i, j} :=
    Finset.singleton_subset_iff.mpr (Finset.mem_insert_self i {j})
  let hR : ({j} : Finset (Fin (n + 1))) ⊆ {i, j} :=
    Finset.singleton_subset_iff.mpr (Finset.mem_insert_of_mem (Finset.mem_singleton_self j))
  have hl := PowerFrameRestrictions.coordinateChartPowerSectionEquiv_restriction I hL i (Finset.mem_singleton_self i) d x
  have hr := PowerFrameRestrictions.coordinateChartPowerSectionEquiv_restriction I hR j (Finset.mem_singleton_self j) d y
  exact (congrArg₂ Eq hl.symm hr.symm).to_iff.trans
    (Subtype.val_injective.eq_iff.trans
      (PowerFrameChange.coordinateChartPowerSectionEquiv_eq_iff I {i, j} i j (hL (Finset.mem_singleton_self i))
        (hR (Finset.mem_singleton_self j)) d _ _))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.TwistPairAgreement
