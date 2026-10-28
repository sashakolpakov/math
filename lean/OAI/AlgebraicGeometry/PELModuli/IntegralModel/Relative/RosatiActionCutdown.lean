import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.RosatiSchemeClassifier
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.RosatiRestriction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.OverLocusClassification

/-! # Rosati Action Cutdown -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.RosatiActionCutdown

noncomputable section

/-! Impose the literal Rosati condition on an actual integral-action
ambient, retaining the original abelian family and restriction maps. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_reduced_relative_rosati_action_cutdown
    {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {S : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (Z : Over S)
    [IsReduced Z.left] [IsNoetherian Z.left]
    (ρZ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.abelian.pullback Z.hom)) :
    ∃ (W : Over S) (j : W ⟶ Z), IsReduced W.left ∧ IsClosedImmersion j.left ∧
      AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback W.hom) (Integral.ActionScheme.restrictIntegralAction A.abelian ρZ j) ∧
      ∀ (T : Over S) [IsReduced T.left] (f : T ⟶ Z),
        AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback T.hom) (Integral.ActionScheme.restrictIntegralAction A.abelian ρZ f) ↔
          ∃! c : T ⟶ W, c ≫ j = f := by
  obtain ⟨C, i, hr, hi, hC⟩ := RosatiSchemeClassifier.exists_reduced_relative_rosati_scheme_classifier (A.pullback Z.hom) ρZ
  let W : Over S := Over.mk (i ≫ Z.hom)
  let j : W ⟶ Z := Over.homMk i rfl
  let : IsReduced W.left := hr
  have : IsClosedImmersion j.left := hi
  have : Mono j := Over.mono_of_mono_left j
  have hclass (T : Over S) [IsReduced T.left] (f : T ⟶ Z) :
      AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback T.hom) (Integral.ActionScheme.restrictIntegralAction A.abelian ρZ f) ↔
        ∃! c : T ⟶ W, c ≫ j = f :=
    (RosatiRestriction.rosati_restrictIntegralAction_iff (T := T) (U := Z) A ρZ f).trans
      ((hC T.left f.left).trans (OverLocusClassification.over_existsUnique_lift_iff j f).symm)
  refine ⟨W, j, hr, hi, (hclass W j).mpr ?_, hclass⟩
  refine ⟨𝟙 W, Category.id_comp j, ?_⟩
  intro c hc
  exact (cancel_mono j).mp (hc.trans (Category.id_comp j).symm)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.RosatiActionCutdown
