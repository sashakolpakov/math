import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.AmbientRepresentation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.PresentationProper

/-! # Representation Projective Reduction -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.RepresentationProjectiveReduction.Core

noncomputable section

/-! The projective-space case of the exact Hilbert functor suffices
for every chosen projective ambient, with a projective parameter scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} [IsLocallyNoetherian S] {X : Over S}

theorem hilbert_representation_of_projective_space
    (BX : Has.Core.ProjectivePresentation X) (P : Polynomial ℚ)
    (H : Over S) (BH : Has.Core.ProjectivePresentation H)
    (eH : yoneda.obj H ≅
      (PolynomialSubfunctor.Core.hilbertPolynomialSubfunctor (Intrinsic.ProjectivePresentation.GradedHilbert.canonicalProjectivePresentation S BX.dimension) P).toFunctor) :
    ∃ Z : Over S, Has.Core.IsProjectiveOver Z ∧
      Nonempty (yoneda.obj Z ≅ (PolynomialSubfunctor.Core.hilbertPolynomialSubfunctor BX P).toFunctor) := by
  let : IsLocallyNoetherian H.left := BH.locallyNoetherian
  obtain ⟨Z, j, _, hZ, eZ, _⟩ := Closed.AmbientRepresentation.Core.closedAmbient_hilbert_representation
    (Intrinsic.ProjectivePresentation.GradedHilbert.canonicalProjectivePresentation S BX.dimension) BH BX.closedAmbientEmbedding P eH
  rw [Has.Core.ProjectivePresentation.canonical_precompose] at eZ
  exact ⟨Z, hZ, ⟨eZ⟩⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.RepresentationProjectiveReduction.Core
