import OAI.NumberTheory.PadicHodge.GeometricComparison.RelativeRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Change

/-! # Change On Subcategory Map -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.ChangeOnSubcategoryMap.FrameChangeOnSubcategoryMap

noncomputable section

/-! The original frame-change cochain map is invertible after any
restriction on which its actual product maps are invertible. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
universe u v w
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)
  {D : Type v} [Category.{w} D]
  (t : D ⥤ IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)
  (F G : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n) (α : G ⟶ F)
  (h : ∀ T, IsIso (prod.map α (𝟙 (t.obj T))))

include h in
theorem diagram_isIso : IsIso (Functor.whiskerLeft t (IntegralComparison.BoundedFrame.Change.diagramMap α)) := by
  let (T : D) : IsIso ((Functor.whiskerLeft t (IntegralComparison.BoundedFrame.Change.diagramMap α)).app T) := by
    change IsIso ((IntegralComparison.BoundedCrystalline.Site.inclusion f n).map (prod.map α (𝟙 (t.obj T))))
    let := h T
    infer_instance
  exact NatIso.isIso_of_isIso_app _

include h in
theorem isIso : IsIso
    (((IntegralComparison.Relative.ComplexRestriction.restriction (B := B) t).mapHomologicalComplex (.up ℕ)).map
      (IntegralComparison.BoundedFrame.Change.presheafMap α)) := by
  let := diagram_isIso f n t F G α h
  exact RelativeRestriction.RelativeRestrictionMap.isIso t
    (IntegralComparison.BoundedFrame.Diagram.productDiagram G) (IntegralComparison.BoundedFrame.Diagram.productDiagram F)
    (IntegralComparison.BoundedCrystalline.Site.inclusion f n) (IntegralComparison.BoundedFrame.Diagram.projection G) (IntegralComparison.BoundedFrame.Diagram.projection F)
    (IntegralComparison.BoundedFrame.Change.diagramMap α) (IntegralComparison.BoundedFrame.Change.projection α)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.ChangeOnSubcategoryMap.FrameChangeOnSubcategoryMap
