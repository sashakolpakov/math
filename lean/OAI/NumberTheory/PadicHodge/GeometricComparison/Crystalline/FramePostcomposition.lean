import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.PostcomposeComposition

/-! # Frame Postcomposition -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FramePostcomposition.CrystallineFramePostcomposition

noncomputable section

/-! A frame map over a chart restriction induces the actual map between its
global frames, retaining the original divided-power ring map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y Z : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of B)}
  {fY : Y ⟶ Spec (CommRingCat.of B)} {fZ : Z ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) (jY : Y ⟶ Z) (jX : X ⟶ Z)
  (hg : g ≫ fY = fX) (hjY : jY ≫ fZ = fY) (hjX : jX ≫ fZ = fX)
  (h : g ≫ jY = jX) (n : ℕ)
  {FX : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fX n}
  {FY : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n}
  (α : (IntegralComparison.BoundedOpen.Equivalence.postcompose g hg n).obj FX ⟶ FY)

def map : (IntegralComparison.BoundedOpen.Equivalence.postcompose jX hjX n).obj FX ⟶
    (IntegralComparison.BoundedOpen.Equivalence.postcompose jY hjY n).obj FY := by
  subst jX
  exact ((IntegralComparison.Crystalline.PostcomposeComposition.boundedIso g jY hg hjY n).app FX).inv ≫
    (IntegralComparison.BoundedOpen.Equivalence.postcompose jY hjY n).map α

theorem ringMap : (CrystallineFramePostcomposition.map g jY jX hg hjY hjX h n α).hom.ringMap = α.hom.ringMap := by
  subst jX
  ext x
  rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FramePostcomposition.CrystallineFramePostcomposition
