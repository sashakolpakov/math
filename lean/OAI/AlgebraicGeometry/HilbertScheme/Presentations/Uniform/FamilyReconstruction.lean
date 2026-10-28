import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.FamilyGeneration
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.EventualSaturatedEquality

/-! # Family Reconstruction -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.FamilyReconstruction.GradedHilbert

noncomputable section

/-! The uniform single-degree Grassmannian coordinates determine actual saturated flat projective families, including over nonreduced noetherian rings. -/

open _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (hSat : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal)
variable [Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))]
variable (P : Polynomial ℚ) (hP : ∀ p : PrimeSpectrum R,
  Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
    (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I)).toIdeal P)

include hSat hP in
theorem uniformFamily_reconstruction (N : ℕ) (hN : FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N) :
    Projective.Saturation.GradedHilbert.projectiveSaturation (DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal I N) = I := by
  obtain ⟨B, hB⟩ := Projective.Saturation.GradedHilbert.projectiveSaturation_eventual_degreeRelations (DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal I N)
  apply EventualSaturatedEquality.GradedHilbert.saturated_eq_of_eventual_degreeRelations _ I
    (Projective.Saturation.GradedHilbert.projectiveSaturation_isSaturated (DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal I N)) hSat (max B N)
  intro d hd
  rw [hB d ((le_max_left _ _).trans hd)]
  exact FamilyGeneration.GradedHilbert.uniformFamily_degreeGenerated_relations I hSat P hP N hN d ((le_max_right _ _).trans hd)

variable (J : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (hSatJ : Hilbert.Polynomial.GradedHilbert.IsSaturated J.toIdeal)
variable [Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading J))]
variable (hPJ : ∀ p : PrimeSpectrum R,
  Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
    (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) J)).toIdeal P)

include hSat hP hSatJ hPJ in
theorem uniformFamily_eq_of_degreeRelations_eq (N : ℕ) (hN : FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
    (heq : Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal N = Hilbert.Polynomial.GradedHilbert.degreeRelations J.toIdeal N) : I = J := by
  rw [← uniformFamily_reconstruction I hSat P hP N hN,
    ← uniformFamily_reconstruction J hSatJ P hPJ N hN]
  exact congrArg Projective.Saturation.GradedHilbert.projectiveSaturation (DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal_eq_of_degreeRelations_eq I J N heq)

include hSat hP hSatJ hPJ in
theorem uniformFamily_eq_of_grassmannian_eq (N : ℕ) (hN : FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
    (heq : FamilyCoordinates.GradedHilbert.uniformFlatFamilyHilbertGrassmannian I hSat P hP N hN =
      FamilyCoordinates.GradedHilbert.uniformFlatFamilyHilbertGrassmannian J hSatJ P hPJ N hN) : I = J :=
  uniformFamily_eq_of_degreeRelations_eq I hSat P hP J hSatJ hPJ N hN
    (congrArg Module.Grassmannian.toSubmodule heq)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.FamilyReconstruction.GradedHilbert
