import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.FamilySections
import OAI.NumberTheory.PadicHodge.GeometricComparison.DiagramSectionIsoTransfer

/-! # Family Iso Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.FamilyIsoSections.Family

noncomputable section

/-! The original bounded frame-section comparison is natural under
isomorphisms of a fixed frame and its entire family of open subframes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)
  {C : Type v} [Category.{w} C] (O : C ⥤ Y.Opensᵒᵖ)
  {G G' : C ⥤ (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ}
  (e : G ≅ G')
  {F F' : (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ}
  (a : F ≅ F')
  (ρ : (Functor.const C).obj F ⟶ G)
  (ρ' : (Functor.const C).obj F' ⟶ G')

local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor (p := p) (J := J) (δ := δ) f n
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.FamilySections.Family.sections f n O

variable [hs : IsIso (GeometricComparison.FixedDiagramTransformation.FixedDiagramSections.map (FamilySections.Family.sections f n O)
  ((GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor (p := p) (J := J) (δ := δ) f n).obj F)
  (FamilySections.Family.diagram f n G) (FamilySections.Family.cone f n F ρ))]
  (h : ∀ r, ρ.app r ≫ e.hom.app r = a.hom ≫ ρ'.app r)

include hs h in
theorem fixed_isIso : IsIso (GeometricComparison.FixedDiagramTransformation.FixedDiagramSections.map S ((Q).obj F')
    (FamilySections.Family.diagram f n G') (FamilySections.Family.cone f n F' ρ')) :=
  GeometricComparison.DiagramSectionIsoTransfer.FixedDiagramSectionIsoTransfer.transfer S
    (FamilySections.Family.cone f n F ρ)
    (FamilySections.Family.cone f n F' ρ') ((Q).mapIso a) (Functor.isoWhiskerRight e Q)
    (FamilySections.Family.cone_naturality f n e.hom ρ ρ' a.hom h)

abbrev naturality := by
  let : IsIso (GeometricComparison.FixedDiagramTransformation.FixedDiagramSections.map S ((Q).obj F')
      (FamilySections.Family.diagram f n G') (FamilySections.Family.cone f n F' ρ')) :=
    fixed_isIso f n O e a ρ ρ' h
  exact FamilySections.Family.fixed_naturality f n O e.hom ρ ρ' a.hom h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.FamilyIsoSections.Family
