import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.GeneratedParameterPoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ProjectiveFamilies

/-! # Generated Family Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.GeneratedFamilyRecovery

noncomputable section

/-! Pullback of the generated universal family along the uniform parameter map recovers the actual input projective family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : CommRingCat.{u}} [IsNoetherianRing R] {S : Scheme.{u}} {n : ℕ}
variable (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) (hSat : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal)
variable [Flat (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))]
variable (P : Polynomial ℚ) (hP : ∀ p : PrimeSpectrum R,
  HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
    (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I)).toIdeal P)
variable (N : ℕ) (hN : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N) (B : ℕ)

def uniformGeneratedProjectiveFamilyIso (hB : N ≤ B) :
    ((GeneratedCoordinates.uniformGeneratedData I hSat P hP N hN).truncate B).projectiveFamily ≅
      Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I :=
  Closed.EmbeddingKernelIso.closedEmbeddingKernelIso ((GeneratedCoordinates.uniformGeneratedData I hSat P hP N hN).truncate B).projectiveEmbedding
    (Projective.EmbeddingBaseChange.homogeneousProjectiveEmbedding I) (GeneratedReconstruction.uniformGeneratedTruncation_projectiveIdeal I hSat P hP N hN B hB)

def uniformGeneratedParameterFamilyIso (hB : N ≤ B) (f : Spec R ⟶ S) :
    (Over.pullback (GeneratedParameterPoints.uniformGeneratedParameterPoint I hSat P hP N hN B f).left).obj
      (Truncated.GeneratedFamily.truncatedGeneratedFamily S n B (GeneratedCoordinates.generatedHilbertRanks n P N) N) ≅
        Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I :=
  (Generated.FamilyClassification.truncatedGeneratedClassifier_familyIso f
    ⟨(GeneratedCoordinates.uniformGeneratedData I hSat P hP N hN).truncate B,
      GeneratedCoordinates.uniformGeneratedData_truncate_condition I hSat P hP N hN B⟩).symm ≪≫
        uniformGeneratedProjectiveFamilyIso I hSat P hP N hN B hB

def uniformGeneratedFlatParameterFamilyIso (hB : Truncated.FinitePersistence.truncatedFlatnessBound n N ≤ B) (f : Spec R ⟶ S) :
    (Over.pullback (GeneratedParameterPoints.uniformGeneratedParameterPoint I hSat P hP N hN B f).left).obj
      (Generated.FlatUniversalFamily.generatedFlatUniversalFamily S n B (GeneratedCoordinates.generatedHilbertRanks n P N) N hB).scheme ≅
        Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I :=
  (Generated.FamilyClassification.generatedFlatClassifier_familyIso f
    ⟨(GeneratedCoordinates.uniformGeneratedData I hSat P hP N hN).truncate B,
      GeneratedCoordinates.uniformGeneratedData_truncate_condition I hSat P hP N hN B⟩ hB).symm ≪≫
        uniformGeneratedProjectiveFamilyIso I hSat P hP N hN B ((Nat.le_add_right N _).trans hB)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.GeneratedFamilyRecovery
