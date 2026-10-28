import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.PolynomialRepresentation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.TuplePackageAssembly
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ExactSegrePresentation

/-! # Hom -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.Hom.Core

noncomputable section

/-! Full relative Hilbert/Hom existence with the exact Segre polarization,
projective Hilbert parameter scheme and natural open graph locus. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem relative_hilbert_and_hom_loci
    {S : Scheme.{u}} [IsLocallyNoetherian S]
    (X Y : Over S) (BX : Has.Core.ProjectivePresentation X) (BY : Has.Core.ProjectivePresentation Y)
    [Flat X.hom] [IsProper X.hom] [LocallyOfFinitePresentation X.hom]
    [IsSeparated Y.hom] (n : ℕ) (P : Fin n → Polynomial ℚ) :
    ∃ B : Has.Core.ProjectivePresentation (X ⨯ Y),
      Segre.Open.Core.IsSegrePresentation BX BY B ∧ Nonempty (Loci.Core.HilbertHomLoci X Y B n P) := by
  classical
  obtain ⟨B, hB⟩ := ExactSegrePresentation.Core.exists_segrePresentation BX BY
  choose H hH eH using fun i => Hilbert.PolynomialRepresentation.GradedHilbert.exists_projectiveSpace_hilbert_representation S B.dimension (P i)
  exact ⟨B, hB, Hilbert.TuplePackageAssembly.Core.hilbertHomLoci_of_projective_space_components X Y B n P H
    (fun i => Classical.choice (hH i)) (fun i => Classical.choice (eH i))⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.Hom.Core
