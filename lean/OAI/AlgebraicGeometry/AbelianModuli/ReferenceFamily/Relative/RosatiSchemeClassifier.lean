import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.RosatiLocus
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.UniqueOverHom

/-! # Rosati Scheme Classifier -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.RosatiSchemeClassifier

noncomputable section

/-! The direct relative Rosati locus has the usual unique scheme-map
classification on all test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.UniqueOverHom

theorem exists_projective_relative_rosati_scheme_classifier
    {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {S : Scheme.{0}} [IsNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation A.abelian.scheme)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian) :
    ∃ (Z : Scheme.{0}) (j : Z ⟶ S), IsClosedImmersion j ∧
      ∀ (T : Scheme.{0}) (x : T ⟶ S),
        ActionData.RosatiConjugation (A.pullback x) (ρ.pullback x) ↔
          ∃! f : T ⟶ Z, f ≫ j = x := by
  obtain ⟨Z, hc, _, hZ⟩ := RosatiLocus.exists_projective_relative_rosati_locus A B ρ
  refine ⟨Z.left, Z.hom, hc, ?_⟩
  intro T x
  let Tx : Over S := Over.mk x
  exact (hZ Tx).trans (PELModuli.IntegralModel.UniqueOverHom.unique_over_hom_iff Tx Z)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.RosatiSchemeClassifier
