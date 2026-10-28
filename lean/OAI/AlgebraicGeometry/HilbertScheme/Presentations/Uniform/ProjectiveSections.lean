import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.CechTensorExactness
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.PositiveCech
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.FieldCechBound
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FiberwiseModuleCech
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces
import Mathlib.RingTheory.Flat.EquationalCriterion

/-! # Projective Sections -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.ProjectiveSections.GradedHilbert

noncomputable section

/-! Uniform finiteness, projectivity, and higher Čech vanishing for flat projective coordinate families with a fixed fiber Hilbert polynomial. -/

open _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.FiberwiseModuleCech.ProjectiveCech

universe u

variable {R : Type u} [CommRing R] {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (P : Polynomial ℚ)
variable (hP : ∀ p : PrimeSpectrum R,
  Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
    (Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I)).toIdeal P)

include hP in
theorem coordinateCech_residueField_exact (d : ℤ) (hd : (RegularCoordinateFlag.GradedHilbert.regularCoordinateFlagBound.{u} n P : ℤ) ≤ d)
    (q : ℕ) (p : PrimeSpectrum R) :
    Function.Exact ((ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := Fin (n + 1)) R
      (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d (q + 1)).lTensor p.asIdeal.ResidueField)
      ((ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := Fin (n + 1)) R
        (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d (q + 1 + 1)).lTensor p.asIdeal.ResidueField) := by
  apply (Coordinate.CechTensorExactness.GradedHilbert.coordinateCech_tensor_exact_iff (S := p.asIdeal.ResidueField) I d (q + 1)).mpr
  let J := Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I
  apply (Saturation.PositiveCech.GradedHilbert.saturation_positiveCech_exact_iff J d q).mpr
  exact Cech.FlatAugmentation.ProjectiveCech.moduleCechTermDifferential_exact p.asIdeal.ResidueField
    (Hilbert.Polynomial.GradedHilbert.CoordinateRing p.asIdeal.ResidueField n ⧸ (Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation J).toIdeal)
    (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation J)) d (q + 1)
    (FieldCechBound.GradedHilbert.saturated_cech_exact_uniform (Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation J) (Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation_isSaturated J)
      P (hP p) d hd (q + 1 + 1))

variable [IsNoetherianRing R] [Flat (Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))]

include hP in
theorem uniform_projective_sections_flat (d : ℤ) (hd : (RegularCoordinateFlag.GradedHilbert.regularCoordinateFlagBound.{u} n P : ℤ) ≤ d) :
    Module.Flat R (FiberwiseModuleCech.ProjectiveCech.moduleCechSections (σ := Fin (n + 1)) R
      (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d) ∧
      ∀ q : ℕ, Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := Fin (n + 1)) R
        (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d (q + 2) := by
  apply FiberwiseModuleCech.ProjectiveCech.moduleCech_fiberwise_exact_flat R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d
  · intro s hs
    let : Module.Flat R (Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
      (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) s 0) := Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert.coordinateChartDegreeZero_flat I s hs
    exact EventualDegreeFlatness.ProjectiveCech.moduleChartDegree_flat_of_zero R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
      (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) s hs d ((Int.natCast_nonneg _).trans hd)
  · exact coordinateCech_residueField_exact I P hP d hd

include hP in
theorem uniform_projective_sections_projective (d : ℕ) (hd : RegularCoordinateFlag.GradedHilbert.regularCoordinateFlagBound.{u} n P ≤ d) :
    Module.Finite R (FiberwiseModuleCech.ProjectiveCech.moduleCechSections (σ := Fin (n + 1)) R
      (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ)) ∧
    Module.Projective R (FiberwiseModuleCech.ProjectiveCech.moduleCechSections (σ := Fin (n + 1)) R
      (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ)) := by
  let : Module.Finite R (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I (d : ℤ)) :=
    Module.Finite.equiv (Coordinate.IntegerQuotient.GradedHilbert.integerDegreeQuotientEquiv I d)
  let : Module.Finite R (FiberwiseModuleCech.ProjectiveCech.moduleCechSections (σ := Fin (n + 1)) R
    (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ)) :=
    FiberwiseModuleCech.ProjectiveCech.moduleCechSections_finite R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ)
  let : Module.Flat R (FiberwiseModuleCech.ProjectiveCech.moduleCechSections (σ := Fin (n + 1)) R
    (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ)) :=
    (uniform_projective_sections_flat I P hP (d : ℤ) (by exact_mod_cast hd)).1
  let : Module.FinitePresentation R (FiberwiseModuleCech.ProjectiveCech.moduleCechSections (σ := Fin (n + 1)) R
    (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ)) :=
    Module.finitePresentation_of_finite R (FiberwiseModuleCech.ProjectiveCech.moduleCechSections (σ := Fin (n + 1)) R
      (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ))
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation (R := R)
    (M := FiberwiseModuleCech.ProjectiveCech.moduleCechSections (σ := Fin (n + 1)) R
      (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ))⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.ProjectiveSections.GradedHilbert
