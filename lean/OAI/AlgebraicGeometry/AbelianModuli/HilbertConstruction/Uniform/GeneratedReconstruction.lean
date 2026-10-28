import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.GeneratedCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.ProjectiveFamily
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.FamilyReconstruction

/-! # Generated Reconstruction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.GeneratedReconstruction

noncomputable section

/-! The finite generated data recover the original saturated homogeneous ideal and its actual projective ideal sheaf. -/

open _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.FamilyReconstruction.GradedHilbert

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
variable (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) (hSat : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal)
variable [Flat (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))]
variable (P : Polynomial ℚ) (hP : ∀ p : PrimeSpectrum R,
  HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
    (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I)).toIdeal P)
variable (N : ℕ) (hN : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N) (B : ℕ) (hB : N ≤ B)

include hB in
theorem uniformGeneratedTruncation_ideal :
    ((GeneratedCoordinates.uniformGeneratedData I hSat P hP N hN).truncate B).generatedIdeal = HilbertScheme.Presentations.DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal I N := by
  let D := (GeneratedCoordinates.uniformGeneratedData I hSat P hP N hN).truncate B
  apply HomogeneousIdeal.ext
  rw [D.generatedIdeal_span_degree N hB (GeneratedCoordinates.uniformGeneratedData_truncate_condition I hSat P hP N hN B)]
  change Ideal.span ((Homogeneous.IdealIncidence.homogeneousDegreeRelations (HilbertScheme.Presentations.DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal I N) N).map
    (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n N).subtype : Set (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n)) = _
  have he : Homogeneous.IdealIncidence.homogeneousDegreeRelations (HilbertScheme.Presentations.DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal I N) N = Homogeneous.IdealIncidence.homogeneousDegreeRelations I N :=
    HilbertScheme.Presentations.Uniform.FamilyGeneration.GradedHilbert.uniformFamily_degreeGenerated_relations I hSat P hP N hN N le_rfl
  rw [he]
  exact (DegreeGeneratedRelations.degreeGeneratedIdeal_span_relations I N).symm

include hB in
theorem uniformGeneratedTruncation_saturation :
    HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation ((GeneratedCoordinates.uniformGeneratedData I hSat P hP N hN).truncate B).generatedIdeal = I := by
  rw [uniformGeneratedTruncation_ideal I hSat P hP N hN B hB]
  exact HilbertScheme.Presentations.Uniform.FamilyReconstruction.GradedHilbert.uniformFamily_reconstruction I hSat P hP N hN

include hB in
theorem uniformGeneratedTruncation_projectiveIdeal :
    ((GeneratedCoordinates.uniformGeneratedData I hSat P hP N hN).truncate B).projectiveEmbedding.left.ker =
      (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I).ker := by
  let D := (GeneratedCoordinates.uniformGeneratedData I hSat P hP N hN).truncate B
  change (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion D.generatedIdeal).ker = _
  rw [← HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation_idealSheaf,
    uniformGeneratedTruncation_saturation I hSat P hP N hN B hB]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.GeneratedReconstruction
