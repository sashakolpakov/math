import OAI.AlgebraicGeometry.PELModuli.CMPoints.SpreadData
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ArithmeticFieldPointSpreading

/-! # Spread Reference Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints

noncomputable section

/-! The original object of the spread CM diagram retains an actual
generic isomorphism to the PEL family at the specified component point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {M : Models.RankThreePELModel E K} {hM : M.HasPrescribedBallPeriods}
  {a : M.Family} {t : Fin (M.componentCount a)} (C : M.CMSpreadData hM a t)

def Models.RankThreePELModel.CMSpreadData.fieldPoint : Spec (.of C.base.extension.carrier) ⟶ ((M.components a).S t).left :=
  Spec.map (CommRingCat.ofHom C.pointFieldEmbedding) ≫ C.component.point

theorem Models.RankThreePELModel.CMSpreadData.fieldPoint_base : C.fieldPoint ≫ ((M.components a).S t).hom =
    Spec.map (CommRingCat.ofHom C.originalFieldEmbedding) ≫ M.arithmetic.generic := by
  dsimp only [Models.RankThreePELModel.CMSpreadData.fieldPoint]
  rw [Category.assoc, C.component.point_base, ← Category.assoc, ← Spec.map_comp]
  rfl

def Models.RankThreePELModel.CMSpreadData.originalGenericComparison :
    (C.original.pullback C.base.generic).scheme ≅
      ((M.componentPolarized a t).abelian.pullback C.fieldPoint).scheme :=
  C.arithmetic.spreadGenericModelComparison C.spread (0 : Fin 4) ≪≫
    IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso (M.componentPolarized a t).abelian.scheme
      C.component.point (Spec.map (CommRingCat.ofHom C.pointFieldEmbedding)) C.fieldPoint rfl

theorem Models.RankThreePELModel.CMSpreadData.originalGenericComparison_group : IsMonHom C.originalGenericComparison.hom := by
  exact @CategoryTheory.instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _
    (C.arithmetic.spreadGenericModelComparison_group C.spread (0 : Fin 4))
    (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso_isMonHom _ _ _ _ _)

theorem Models.RankThreePELModel.CMSpreadData.exists_integral_component_section :
    ∃ (D : ℕ) (hD : D ≠ 0) (hdiv : C.base.denominator ∣ D),
      ∃ z : (C.base.withDenominator D hD).base ⟶ ((M.components a).S t).left,
        z ≫ ((M.components a).S t).hom =
          ArithmeticBaseMaps.arithmeticBaseMap M.arithmetic (C.base.withDenominator D hD) C.originalFieldEmbedding
            (C.denominator_divides.trans hdiv) ∧
        (C.base.withDenominator D hD).generic ≫ z = C.fieldPoint := by
  have hs : Smooth ((M.components a).S t).hom := (hM.2.2 a).2.2.2.2.2.2.2.2.2 t |>.1
  have hp : IsProper ((M.components a).S t).hom := (hM.2.2 a).2.2.2.2.2.2.2.2.2 t |>.2.1
  let : Smooth ((M.components a).S t).hom := hs
  let : IsProper ((M.components a).S t).hom := hp
  exact ArithmeticFieldPointSpreading.field_point_on_fixed_arithmetic_model_spreads M.arithmetic C.base
    C.originalFieldEmbedding C.denominator_divides ((M.components a).S t)
    ⟨inferInstance, inferInstance, inferInstance⟩ C.fieldPoint C.fieldPoint_base

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints
