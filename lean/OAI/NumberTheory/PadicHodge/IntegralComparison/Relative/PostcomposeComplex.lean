import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.ModuleComplex

/-! # Postcompose Complex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.PostcomposeComplex

noncomputable section

/-!
# IntegralComparison: geometric postcomposition retains the original relative crystalline form complex
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

universe u v w

variable {C : Type v} [Category.{w} C] {p : ℕ} {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) (hg : g ≫ fY = f) (H Q : C ⥤ BigCrystallineSite.Object p B J δ f) (π : H ⟶ Q)

def complexIso : RelativeCrystalline.ModuleComplex.complex
    (H ⋙ BigCrystallineSite.postcompose g hg) (Q ⋙ BigCrystallineSite.postcompose g hg) (Functor.whiskerRight π (BigCrystallineSite.postcompose g hg)) ≅
      RelativeCrystalline.ModuleComplex.complex H Q π := Iso.refl _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.PostcomposeComplex
