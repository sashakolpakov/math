import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.ProjectiveSections
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.FlatImages

/-! # Projective Augmentation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.ProjectiveAugmentation.GradedHilbert

noncomputable section

/-! Uniform surjectivity from homogeneous coordinates to projective sections, detected through the actual residue-field Čech complexes. -/

open _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.FlatImages.ProjectiveCech

universe u

variable {R : Type u} [CommRing R] {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (P : Polynomial ℚ)
variable (hP : ∀ p : PrimeSpectrum R,
  Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
    (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I)).toIdeal P)

include hP in
theorem coordinateCech_residueField_exact_all (d : ℤ) (hd : (RegularCoordinateFlag.GradedHilbert.regularCoordinateFlagBound.{u} n P : ℤ) ≤ d)
    (q : ℕ) (p : PrimeSpectrum R) :
    Function.Exact ((ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := Fin (n + 1)) R
      (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d q).lTensor p.asIdeal.ResidueField)
      ((ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := Fin (n + 1)) R
        (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d (q + 1)).lTensor p.asIdeal.ResidueField) := by
  apply (Coordinate.CechTensorExactness.GradedHilbert.coordinateCech_tensor_exact_iff (S := p.asIdeal.ResidueField) I d q).mpr
  let J := Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I
  apply (Saturation.PositiveCech.GradedHilbert.saturationCech_exact_iff J d q).mpr
  exact Cech.FlatAugmentation.ProjectiveCech.moduleCechTermDifferential_exact p.asIdeal.ResidueField
    (Hilbert.Polynomial.GradedHilbert.CoordinateRing p.asIdeal.ResidueField n ⧸ (Projective.Saturation.GradedHilbert.projectiveSaturation J).toIdeal)
    (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (Projective.Saturation.GradedHilbert.projectiveSaturation J)) d q
    (FieldCechBound.GradedHilbert.saturated_cech_exact_uniform (Projective.Saturation.GradedHilbert.projectiveSaturation J) (Projective.Saturation.GradedHilbert.projectiveSaturation_isSaturated J)
      P (hP p) d hd (q + 1))

variable [IsNoetherianRing R] [Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))]

include hP in
theorem uniform_projective_augmentation_exact (d : ℤ) (hd : (RegularCoordinateFlag.GradedHilbert.regularCoordinateFlagBound.{u} n P : ℤ) ≤ d) :
    Function.Exact (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := Fin (n + 1)) R
      (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d 0)
      (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := Fin (n + 1)) R
        (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d 1) := by
  let f := ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := Fin (n + 1)) R
    (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d 0
  let g := ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := Fin (n + 1)) R
    (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d 1
  let : Module.Flat R g.range := Cech.FlatImages.ProjectiveCech.moduleCech_positive_image_flat R
    (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d (fun s hs => by
      let : Module.Flat R (Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
        (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) s 0) := Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert.coordinateChartDegreeZero_flat I s hs
      exact EventualDegreeFlatness.ProjectiveCech.moduleChartDegree_flat_of_zero R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
        (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) s hs d ((Int.natCast_nonneg _).trans hd))
      (ProjectiveSections.GradedHilbert.uniform_projective_sections_flat I P hP d hd).2 0
  let : Module.Finite R (FiberwiseExactness.linearKernelCohomology R f g
    (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential_square R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d 0)) :=
    Presentations.Finite.CechKernelQuotients.ProjectiveCech.moduleCech_kernelQuotient_finite R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d 0
  exact FiberwiseExactness.exact_of_residueFields_of_flat_range R f g
    (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential_square R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d 0)
    (coordinateCech_residueField_exact_all I P hP d hd 0)

include hP in
theorem uniform_projective_cech_exact (d : ℤ) (hd : (RegularCoordinateFlag.GradedHilbert.regularCoordinateFlagBound.{u} n P : ℤ) ≤ d)
    (q : ℕ) : Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := Fin (n + 1)) R
      (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d (q + 1) := by
  cases q with
  | zero =>
    intro f hf hfc hfd
    have hz : ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := Fin (n + 1)) R
      (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d 1 ⟨f, hf, hfc⟩ = 0 := Subtype.ext hfd
    obtain ⟨g, hg⟩ := (uniform_projective_augmentation_exact I P hP d hd _).mp hz
    exact ⟨g.val, g.property.1, g.property.2, congrArg Subtype.val hg⟩
  | succ q => exact (ProjectiveSections.GradedHilbert.uniform_projective_sections_flat I P hP d hd).2 q

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.ProjectiveAugmentation.GradedHilbert
