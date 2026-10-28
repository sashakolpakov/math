import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps

/-! # Level Underlying Diagram -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.LevelUnderlyingDiagram.BoundedLevelUnderlyingDiagram

noncomputable section

/-! A bounded-level map of diagrams gives its original underlying map
of diagrams in the big crystalline category. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite
universe u v w
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (n m : ℕ) (hnm : n ≤ m)
  {C : Type v} [Category.{w} C]
  (Fn : C ⥤ IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)
  (Fm : C ⥤ IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f m)
  (a : Fn ⋙ IntegralComparison.BoundedCrystalline.LevelMaps.inclusion f n m hnm ⟶ Fm)

def transformation : Fn ⋙ IntegralComparison.BoundedCrystalline.Site.inclusion f n ⟶ Fm ⋙ IntegralComparison.BoundedCrystalline.Site.inclusion f m :=
  Functor.whiskerRight a (IntegralComparison.BoundedCrystalline.Site.inclusion f m)

def opTransformation : Fm.op ⋙ (IntegralComparison.BoundedCrystalline.Site.inclusion f m).op ⟶ Fn.op ⋙ (IntegralComparison.BoundedCrystalline.Site.inclusion f n).op :=
  NatTrans.op (transformation f n m hnm Fn Fm a)

theorem app (U : C) : (transformation f n m hnm Fn Fm a).app U = (a.app U).hom := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.LevelUnderlyingDiagram.BoundedLevelUnderlyingDiagram
