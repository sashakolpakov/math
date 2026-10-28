import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.TensorEulerPolynomial
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.IsoGeneratedFactors
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.EmbeddingProjectiveQuotient
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.ProjectiveEmbeddings

/-! # Line Bundle Euler Polynomial -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Actual projective embeddings supply the generated factors used to prove polynomiality of every line-bundle Euler sequence. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem Projective.LineBundleEulerPolynomial.lineBundle_eulerPolynomial_of_projectiveIso
    {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [IsProper p]
    (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading K n)) (e : X ≅ Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))
    (L : Line.Bundles.LineBundle X) :
    ∃ P : Polynomial ℚ, ∀ m : ℕ,
      P.eval (m : ℚ) = (CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (L.tensorPower m).sheaf : ℚ) := by
  obtain ⟨H, hH, hLH⟩ := Projective.IsoGeneratedFactors.lineBundle_two_generated_factors_of_projectiveIso I e L
  exact Generated.TensorEulerPolynomial.lineBundle_eulerPolynomial_of_two_generated p L H hH hLH

theorem Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.lineBundle_eulerPolynomial
    {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    {L : Line.Bundles.LineBundle X} (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L p) (M : Line.Bundles.LineBundle X) :
    ∃ P : Polynomial ℚ, ∀ m : ℕ,
      P.eval (m : ℚ) = (CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (M.tensorPower m).sheaf : ℚ) := by
  have : IsClosedImmersion (SectionsProjectiveMorphism.sectionProjectiveMorphism p E.sections E.covers).left :=
    E.closedImmersion
  have : Flat (Over.mk p).hom := inferInstanceAs (Flat p)
  have : LocallyOfFinitePresentation (Over.mk p).hom :=
    inferInstanceAs (LocallyOfFinitePresentation p)
  obtain ⟨I, ⟨e⟩⟩ := Relative.EmbeddingProjectiveQuotient.relativeEmbedding_has_projectiveQuotient_iso
    (SectionsProjectiveMorphism.sectionProjectiveMorphism p E.sections E.covers)
  exact Projective.LineBundleEulerPolynomial.lineBundle_eulerPolynomial_of_projectiveIso p I e M

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
