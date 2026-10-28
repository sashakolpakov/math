import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.PolynomialRepresentation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.RepresentationProjectiveReduction

/-! # Hilbert Representation -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.HilbertRepresentation

noncomputable section

/-! The fully proved projective Hilbert representation for the exact
polynomial subfunctor on every test scheme, in an arbitrary chosen
projective ambient. No representation or effectivity hypothesis occurs. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem projective_hilbert_representation
    {S : Scheme.{0}} [IsLocallyNoetherian S] {X : Over S}
    (BX : HilbertScheme.Presentations.Has.Core.ProjectivePresentation X) (P : Polynomial ℚ) :
    ∃ H : Over S, HilbertScheme.Presentations.Has.Core.IsProjectiveOver H ∧
      Nonempty (yoneda.obj H ≅ (HilbertScheme.Presentations.Hilbert.PolynomialSubfunctor.Core.hilbertPolynomialSubfunctor BX P).toFunctor) := by
  obtain ⟨H, ⟨BH⟩, ⟨e⟩⟩ :=
    HilbertScheme.Presentations.Hilbert.PolynomialRepresentation.GradedHilbert.exists_projectiveSpace_hilbert_representation S BX.dimension P
  exact HilbertScheme.Presentations.Hilbert.RepresentationProjectiveReduction.Core.hilbert_representation_of_projective_space BX P H BH e

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.HilbertRepresentation
