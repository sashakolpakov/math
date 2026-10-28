import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.RosatiSchemeClassifier
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.RosatiRestriction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.OverLocusClassification

/-! # Rosati Action Cutdown -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.RosatiActionCutdown

noncomputable section

/-! Impose the literal Rosati condition on an actual integral-action
ambient, retaining the original abelian family and restriction maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_projective_relative_rosati_action_cutdown
    {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {S : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (Z : Over S)
    [IsNoetherian Z.left]
    (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation (A.abelian.pullback Z.hom).scheme)
    (ρZ : ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.abelian.pullback Z.hom)) :
    ∃ (W : Over S) (j : W ⟶ Z), IsClosedImmersion j.left ∧
      ActionData.RosatiConjugation (A.pullback W.hom) (PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction A.abelian ρZ j) ∧
      ∀ (T : Over S) (f : T ⟶ Z),
        ActionData.RosatiConjugation (A.pullback T.hom) (PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction A.abelian ρZ f) ↔
          ∃! c : T ⟶ W, c ≫ j = f := by
  obtain ⟨C, i, hi, hC⟩ :=
    RosatiSchemeClassifier.exists_projective_relative_rosati_scheme_classifier (A.pullback Z.hom) B ρZ
  let W : Over S := Over.mk (i ≫ Z.hom)
  let j : W ⟶ Z := Over.homMk i rfl
  have : IsClosedImmersion j.left := hi
  have : Mono j := Over.mono_of_mono_left j
  have hclass (T : Over S) (f : T ⟶ Z) :
      ActionData.RosatiConjugation (A.pullback T.hom) (PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction A.abelian ρZ f) ↔
        ∃! c : T ⟶ W, c ≫ j = f :=
    (PELModuli.IntegralModel.RosatiRestriction.rosati_restrictIntegralAction_iff (T := T) (U := Z) A ρZ f).trans
      ((hC T.left f.left).trans (PELModuli.IntegralModel.OverLocusClassification.over_existsUnique_lift_iff j f).symm)
  refine ⟨W, j, hi, (hclass W j).mpr ?_, hclass⟩
  refine ⟨𝟙 W, Category.id_comp j, ?_⟩
  intro c hc
  exact (cancel_mono j).mp (hc.trans (Category.id_comp j).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.RosatiActionCutdown
