import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.GeneratedReconstruction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.FamilyClassification

/-! # Generated Parameter Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.GeneratedParameterPoints

noncomputable section

/-! Actual parameter maps for saturated flat projective families, with injectivity on their homogeneous ideals. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : CommRingCat.{u}} [IsNoetherianRing R] {S : Scheme.{u}} {n : ℕ}
variable (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) (hSat : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal)
variable [Flat (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))]
variable (P : Polynomial ℚ) (hP : ∀ p : PrimeSpectrum R,
  HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
    (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I)).toIdeal P)
variable (N : ℕ) (hN : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N) (B : ℕ) (f : Spec R ⟶ S)

def uniformGeneratedParameterPoint :
    Over.mk f ⟶ Truncated.GeneratedParameters.truncatedGeneratedParameters S n B (GeneratedCoordinates.generatedHilbertRanks n P N) N :=
  Truncated.GeneratedParameters.truncatedGeneratedAffinePointEquiv R f
    ⟨(GeneratedCoordinates.uniformGeneratedData I hSat P hP N hN).truncate B,
      GeneratedCoordinates.uniformGeneratedData_truncate_condition I hSat P hP N hN B⟩

variable (J : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) (hSatJ : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.IsSaturated J.toIdeal)
variable [Flat (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading J))]
variable (hPJ : ∀ p : PrimeSpectrum R,
  HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
    (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) J)).toIdeal P)

theorem uniformGeneratedParameterPoint_injective (hB : N ≤ B)
    (heq : uniformGeneratedParameterPoint I hSat P hP N hN B f =
      uniformGeneratedParameterPoint J hSatJ P hPJ N hN B f) : I = J := by
  have hd := (Truncated.GeneratedParameters.truncatedGeneratedAffinePointEquiv R f).injective heq
  have hd' := congrArg Subtype.val hd
  have hi := congrArg (fun D : Truncated.GradedClassification.TruncatedGradedQuotientData R (Fin (n + 1)) B
      (GeneratedCoordinates.generatedHilbertRanks n P N) => HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation D.generatedIdeal) hd'
  rw [GeneratedReconstruction.uniformGeneratedTruncation_saturation I hSat P hP N hN B hB,
    GeneratedReconstruction.uniformGeneratedTruncation_saturation J hSatJ P hPJ N hN B hB] at hi
  exact hi

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.GeneratedParameterPoints
