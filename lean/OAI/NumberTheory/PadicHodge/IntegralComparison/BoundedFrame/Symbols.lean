import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.Symbols

/-! # Symbols -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Symbols

noncomputable section

/-!
# IntegralComparison: canonical frame symbols on the native bounded product diagram
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} [IsSeparated f]
  {n : ℕ} (F : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f n

def frameProjection : Diagram.productDiagram F ⟶ (Functor.const _).obj F.obj where
  app U := (Q).map ((Over.star F).obj U).hom
  naturality U V α := by
    exact ((Q).map_comp ((Over.star F).map α).left ((Over.star F).obj V).hom).symm.trans
      ((congrArg (Q).map (Over.w ((Over.star F).map α))).trans
        (Category.comp_id ((Q).map ((Over.star F).obj U).hom)).symm)

theorem frameProjection_app (U : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n) :
    (frameProjection F).app U = (Q).map (prod.fst : F ⨯ U ⟶ F) :=
  congrArg (Q).map (prod.lift_fst (prod.fst : F ⨯ U ⟶ F) (𝟙 (F ⨯ U)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Symbols
