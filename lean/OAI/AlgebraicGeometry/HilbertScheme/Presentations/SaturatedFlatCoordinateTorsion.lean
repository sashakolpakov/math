import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SaturatedCechAugmentation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces
import Mathlib.RingTheory.Flat.TorsionFree

/-! # Saturated Flat Coordinate Torsion -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.SaturatedFlatCoordinateTorsion.GradedHilbert

noncomputable section

/-! Saturated coordinate quotients of a flat projective family are
torsion-free in every degree, with no noetherian hypothesis on the base. -/

open _root_.AlgebraicGeometry

universe u
variable {R : Type u} [CommRing R] {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (hI : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal)
variable [Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))]

include hI in
theorem saturatedFlat_degree_isTorsionFree (d : ℕ) : Module.IsTorsionFree R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) := by
  let V := fun q => ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := Fin (n + 1)) R
    (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ) q
  let δ : V 0 →ₗ[R] V 1 := ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := Fin (n + 1)) R
    (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ) 0
  let : Module.Flat R (V 1) := ModuleCech.Terms.ProjectiveCech.moduleCechTerm_flat R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
    (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ) 1 Nat.zero_lt_one (by
      intro s hs
      let := Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert.coordinateChartDegreeZero_flat I s hs
      exact EventualDegreeFlatness.ProjectiveCech.moduleChartDegree_flat_of_zero R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
        (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) s hs (d : ℤ) (Int.natCast_nonneg d))
  let : Module.IsTorsionFree R (V 1) := Module.Flat.isTorsionFree
  let : Module.IsTorsionFree R (V 0) := Function.Injective.moduleIsTorsionFree δ
    (SaturatedCechAugmentation.GradedHilbert.saturatedCechAugmentation_injective I hI d) (fun r x => δ.map_smul r x)
  let e : Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d ≃ₗ[R] V 0 :=
    (Coordinate.IntegerQuotient.GradedHilbert.integerDegreeQuotientEquiv I d).trans
      (Cech.AugmentationDegree.ProjectiveCech.moduleCechAugmentationEquiv (σ := Fin (n + 1)) R
        (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ)).symm
  exact Function.Injective.moduleIsTorsionFree e e.injective (fun r x => e.map_smul r x)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.SaturatedFlatCoordinateTorsion.GradedHilbert
