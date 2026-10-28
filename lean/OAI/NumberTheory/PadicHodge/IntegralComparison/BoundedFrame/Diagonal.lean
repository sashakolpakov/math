import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Symbols

/-! # Diagonal -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagonal

noncomputable section

/-!
# IntegralComparison: the diagonal recovers coefficients pulled back from the frame
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} [IsSeparated f]
  {n : ℕ} (F : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

theorem diagonal_projection :
    (BoundedCrystalline.Site.inclusion f n).map (prod.lift (𝟙 F) (𝟙 F)) ≫ (Symbols.frameProjection F).app F = 𝟙 F.obj := by
  have h := Symbols.frameProjection_app F F
  exact (congrArg (fun t => (BoundedCrystalline.Site.inclusion f n).map (prod.lift (𝟙 F) (𝟙 F)) ≫ t) h).trans
    (((BoundedCrystalline.Site.inclusion f n).map_comp _ _).symm.trans
      ((congrArg (BoundedCrystalline.Site.inclusion f n).map (prod.lift_fst (𝟙 F) (𝟙 F))).trans ((BoundedCrystalline.Site.inclusion f n).map_id F)))

theorem diagonal_ringMap (a : F.obj.ring) :
    ((BoundedCrystalline.Site.inclusion f n).map (prod.lift (𝟙 F) (𝟙 F))).ringMap
      (((Symbols.frameProjection F).app F).ringMap a) = a :=
  congrArg (fun g : F.obj ⟶ F.obj => g.ringMap a) (diagonal_projection F)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagonal
