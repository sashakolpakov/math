import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.FamilySections
import OAI.NumberTheory.PadicHodge.GeometricComparison.FixedFrameEq

/-! # Section Reindex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SectionReindex

noncomputable section

/-! Restriction of an original bounded-frame family commutes with
its absolute-to-relative section comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w v' w'
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)
  {C : Type v} [Category.{w} C] {D : Type v'} [Category.{w'} D]
  (r : D ⥤ C) (O : C ⥤ Y.Opensᵒᵖ)
  (G : C ⥤ (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ)
  (F : (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ)
  (ρ : (Functor.const C).obj F ⟶ G)

local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor (p := p) (J := J) (δ := δ) f n
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.FamilySections.Family.sections f n O
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.FamilySections.Family.diagram f n G
local notation "K" => Functor.obj Q F
local notation "η" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.FamilySections.Family.cone f n F ρ

def cone : (Functor.const D).obj F ⟶ r ⋙ G where
  app d := ρ.app (r.obj d)
  naturality _ _ a := ρ.naturality (r.map a)

theorem fixed_isIso [IsIso (GeometricComparison.FixedDiagramTransformation.FixedDiagramSections.map S K P η)] : IsIso
    (GeometricComparison.FixedDiagramTransformation.FixedDiagramSections.map (FamilySections.Family.sections f n (r ⋙ O)) K
      (FamilySections.Family.diagram f n (r ⋙ G))
      (FamilySections.Family.cone f n F (cone f n r G F ρ))) :=
  GeometricComparison.FixedFrameEq.FixedFrameSectionReindex.reindexed_isIso r S K P η

abbrev comparison [IsIso (GeometricComparison.FixedDiagramTransformation.FixedDiagramSections.map S K P η)] :=
  GeometricComparison.FixedFrameEq.FixedFrameSectionReindex.fixed_eq r S K P η
    (FamilySections.Family.source f n G)
    (FamilySections.Family.openTransformation f n O G)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SectionReindex
