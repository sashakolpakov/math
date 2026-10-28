import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.ProjectiveAugmentation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SaturatedCechAugmentation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.Coordinates

/-! # Saturated Coordinates -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.SaturatedCoordinates.GradedHilbert

noncomputable section

/-! A dimension-and-Hilbert-polynomial bound gives finite projective coordinate quotients for every saturated flat projective family over a noetherian ring. -/

open _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (hSat : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal)
variable [Flat (Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))]
variable (P : Polynomial ℚ) (hP : ∀ p : PrimeSpectrum R,
  Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
    (Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I)).toIdeal P)

include hSat hP in
theorem uniform_saturated_coordinate_flat (d : ℕ) (hd : RegularCoordinateFlag.GradedHilbert.regularCoordinateFlagBound.{u} n P ≤ d) :
    Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) := by
  have hd' : (RegularCoordinateFlag.GradedHilbert.regularCoordinateFlagBound.{u} n P : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  let : Module.Flat R (ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := Fin (n + 1)) R
    (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ) 0) :=
    Cech.FlatAugmentation.ProjectiveCech.moduleCech_augmentation_flat R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ)
      (ProjectiveAugmentation.GradedHilbert.uniform_projective_cech_exact I P hP (d : ℤ) hd') (by
        intro f hf hfc hfd
        have hz : ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := Fin (n + 1)) R
          (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ) 0 ⟨f, hf, hfc⟩ =
            ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := Fin (n + 1)) R
              (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ) 0 0 := by
          rw [LinearMap.map_zero]
          exact Subtype.ext hfd
        exact congrArg Subtype.val (SaturatedCechAugmentation.GradedHilbert.saturatedCechAugmentation_injective I hSat d hz)) (fun s hs => by
        let : Module.Flat R (Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
          (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) s 0) := Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert.coordinateChartDegreeZero_flat I s hs
        exact EventualDegreeFlatness.ProjectiveCech.moduleChartDegree_flat_of_zero R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
          (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) s hs (d : ℤ) (Int.natCast_nonneg d))
  let : Module.Flat R (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I (d : ℤ)) := Module.Flat.of_linearEquiv
    (Cech.AugmentationDegree.ProjectiveCech.moduleCechAugmentationEquiv (σ := Fin (n + 1)) R
      (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ)).symm
  exact Module.Flat.of_linearEquiv (Coordinate.IntegerQuotient.GradedHilbert.integerDegreeQuotientEquiv I d)

include hSat hP in
theorem uniform_saturated_coordinate_projective (d : ℕ) (hd : RegularCoordinateFlag.GradedHilbert.regularCoordinateFlagBound.{u} n P ≤ d) :
    Module.Projective R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) := by
  let : Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) := uniform_saturated_coordinate_flat I hSat P hP d hd
  exact Relative.Coordinates.GradedHilbert.degreeQuotient_projective_of_flat I d

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.SaturatedCoordinates.GradedHilbert
