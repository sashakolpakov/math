import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.RosatiLocus
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.UniqueOverHom

/-! # Rosati Scheme Classifier -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.RosatiSchemeClassifier

noncomputable section

/-! The direct relative Rosati locus has the usual unique scheme-map
classification on all reduced test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_reduced_relative_rosati_scheme_classifier
    {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {S : Scheme.{0}} [IsReduced S] [IsNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian) :
    ∃ (Z : Scheme.{0}) (j : Z ⟶ S), IsReduced Z ∧ IsClosedImmersion j ∧
      ∀ (T : Scheme.{0}) [IsReduced T] (x : T ⟶ S),
        AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback x) (ρ.pullback x) ↔
          ∃! f : T ⟶ Z, f ≫ j = x := by
  obtain ⟨Z, hr, hc, _, hZ⟩ := RosatiLocus.exists_reduced_relative_rosati_locus A ρ
  refine ⟨Z.left, Z.hom, hr, hc, ?_⟩
  intro T hT x
  let Tx : Over S := Over.mk x
  let : IsReduced Tx.left := hT
  exact (hZ Tx).trans (UniqueOverHom.unique_over_hom_iff Tx Z)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.RosatiSchemeClassifier
