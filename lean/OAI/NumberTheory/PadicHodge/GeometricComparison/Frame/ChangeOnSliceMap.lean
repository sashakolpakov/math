import OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.ChangeOnSlice
import OAI.NumberTheory.PadicHodge.GeometricComparison.RelativeRestriction

/-! # Change On Slice Map -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.ChangeOnSliceMap.FrameChangeOnSliceMap

noncomputable section

/-! The original frame-change cochain map is itself invertible on a slice
where its actual product-diagram morphisms are invertible. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
universe u
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)
  (I F G : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n) (α : G ⟶ F)
  (h : ∀ (T : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n) (_ : T ⟶ I), IsIso (prod.map α (𝟙 T)))

include h in
theorem isIso : IsIso
    (((IntegralComparison.Relative.ComplexRestriction.restriction (B := B) (Over.forget I)).mapHomologicalComplex (.up ℕ)).map
      (IntegralComparison.BoundedFrame.Change.presheafMap α)) := by
  let : IsIso (Functor.whiskerLeft (Over.forget I) (IntegralComparison.BoundedFrame.Change.diagramMap α)) :=
    ChangeOnSlice.FrameChangeOnSlice.diagramMap_isIso f n I F G α h
  exact RelativeRestriction.RelativeRestrictionMap.isIso (Over.forget I)
    (IntegralComparison.BoundedFrame.Diagram.productDiagram G) (IntegralComparison.BoundedFrame.Diagram.productDiagram F)
    (IntegralComparison.BoundedCrystalline.Site.inclusion f n) (IntegralComparison.BoundedFrame.Diagram.projection G) (IntegralComparison.BoundedFrame.Diagram.projection F)
    (IntegralComparison.BoundedFrame.Change.diagramMap α) (IntegralComparison.BoundedFrame.Change.projection α)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.ChangeOnSliceMap.FrameChangeOnSliceMap
