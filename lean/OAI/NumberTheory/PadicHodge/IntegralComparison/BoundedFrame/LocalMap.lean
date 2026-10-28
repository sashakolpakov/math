import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.FamilyIsoSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SectionReindex

/-! # Local Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.LocalMap

noncomputable section

/-! The actual local bounded-frame comparison, including canonical
transport when two descriptions give the same family of geometric opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)
  {C : Type v} [Category.{w} C] (O : C ⥤ Y.Opensᵒᵖ)
  (G : C ⥤ (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ)
  (F : (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ)
  (ρ : (Functor.const C).obj F ⟶ G)

local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor (p := p) (J := J) (δ := δ) f n
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.FamilySections.Family.sections f n O
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.FamilySections.Family.diagram f n G
local notation "K" => Functor.obj Q F
local notation "η" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.FamilySections.Family.cone f n F ρ

abbrev restriction := GeometricComparison.FixedDiagramTransformation.FixedDiagramSections.map S K P η

def map [IsIso (restriction f n O G F ρ)] :=
  GeometricComparison.FixedFrameDiagonalNaturality.FixedFrameSectionNaturality.diagonal S (FamilySections.Family.source f n G) P
      (FamilySections.Family.openTransformation f n O G) ≫
    inv (restriction f n O G F ρ)

variable (O' : C ⥤ Y.Opensᵒᵖ) (h : O = O')

def sectionsIso : FamilySections.Family.sections (p := p) (J := J) (δ := δ) f n O ≅
    FamilySections.Family.sections (p := p) (J := J) (δ := δ) f n O' :=
  eqToIso (congrArg (FamilySections.Family.sections (p := p) (J := J) (δ := δ) f n) h)

include h in
theorem restriction_isIso [IsIso (restriction f n O G F ρ)] :
    IsIso (restriction f n O' G F ρ) := by
  subst O'
  infer_instance

theorem map_opens [IsIso (restriction f n O G F ρ)] [IsIso (restriction f n O' G F ρ)] :
    map f n O G F ρ ≫ ((NatIso.mapHomologicalComplex (sectionsIso f n O O' h) (.up ℕ)).app K).hom =
      map f n O' G F ρ := by
  subst O'
  change map f n O G F ρ ≫ 𝟙 _ = map f n O G F ρ
  exact Category.comp_id _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.LocalMap
