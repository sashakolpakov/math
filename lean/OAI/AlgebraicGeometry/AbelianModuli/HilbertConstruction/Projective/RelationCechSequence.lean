import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CoefficientCech
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.NegativeTwistRelations

/-! # Relation Cech Sequence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective

noncomputable section

/-! The constructed projective relation sequence gives an actual short exact sequence of finite-length coordinate Čech complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ}
    {I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)} {M : (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotient I).Modules}

theorem NegativeTwistCover.ProjectiveNegativeTwistCover.relationCechSequence_shortExact (D : NegativeTwistCover.ProjectiveNegativeTwistCover I M) [M.IsQuasicoherent] :
    (CoefficientCechExactness.projectiveCoefficientCechMappedShortComplex I D.relationSequence).ShortExact := by
  have h₁ : D.relationSequence.X₁.IsQuasicoherent :=
    @NegativeTwistCover.ProjectiveNegativeTwistCover.relations_quasicoherent R _ n I M D ‹M.IsQuasicoherent›
  have h₂ : D.relationSequence.X₂.IsQuasicoherent := D.source_quasicoherent
  have h₃ : D.relationSequence.X₃.IsQuasicoherent := inferInstanceAs M.IsQuasicoherent
  exact @CoefficientCechExactness.projectiveCoefficientCech_shortExact R _ n I D.relationSequence
    D.relationSequence_shortExact h₁ h₂ h₃

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective
