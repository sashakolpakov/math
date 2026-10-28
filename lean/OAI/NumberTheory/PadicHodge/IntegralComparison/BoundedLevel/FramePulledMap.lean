import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FramePulledSource

/-! # Frame Pulled Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FramePulledMap

noncomputable section

/-! The pulled crystalline frame map induces the original coefficient-linear de Rham section map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f]
  (n m : ℕ) (hnm : n ≤ m)
  {FX : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n}
  {FY : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f m}
  (α : (BoundedCrystalline.LevelMaps.inclusion (p := p) (J := J) (δ := δ) f n m hnm).obj FX ⟶ FY)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.inclusion (p := p) (J := J) (δ := δ) f n m hnm
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.restriction (p := p) (J := J) (δ := δ) f n m hnm

def map : ((constantSheaf (BoundedCrystalline.Site.topology f n) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))).mapHomologicalComplex (.up ℕ)).obj
    (BoundedFrame.DeRhamSections.frameComplex f m FY) ⟶
      ((R).mapHomologicalComplex (.up ℕ)).obj (Bounded.RelativeSheafComplex.complex f m FY) :=
  ConstantSection.ComplexRestriction.pulled G (Crystalline.ExactRestriction.Coeff (B := B)) (BoundedCrystalline.Site.topology f n) (BoundedCrystalline.Site.topology f m)
    (BoundedFrame.DeRhamSections.frameComplex f m FY) (Bounded.RelativeSheafComplex.complex f m FY)
    (BoundedFrame.DeRhamSections.sheafMap f m FY)

theorem square : FramePulledMap.map f n m hnm (FY := FY) ≫ FrameMap.map f n m hnm α =
    ((constantSheaf (BoundedCrystalline.Site.topology f n) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))).mapHomologicalComplex (.up ℕ)).map
      (BoundedFrame.SectionChange.frameMap α) ≫ BoundedFrame.DeRhamSections.sheafMap f n FX :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun a => (FramePulledSource.sourceIso f n m hnm (FY := FY)).inv ≫ a)
      (FrameSectionMap.complexes f n m hnm α)).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun a => a ≫ BoundedFrame.DeRhamSections.sheafMap f n FX)
            (FramePulledSource.complexes f n m hnm α))))

theorem map_component (i : ℕ) :
    (constantSheaf (BoundedCrystalline.Site.topology f n) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))).map
      ((BoundedFrame.SectionChange.frameMap α).f i) ≫
        (BoundedFrame.DeRhamSections.sheafMap f n FX).f i =
    (FramePulledMap.map f n m hnm (FY := FY)).f i ≫ (FrameMap.map f n m hnm α).f i :=
  (congrArg (fun a => a.f i) (square f n m hnm α)).symm

theorem sections_component (i : ℕ) :
    (ConstantSection.ComplexMap.map (Crystalline.ExactRestriction.Coeff (B := B)) (BoundedCrystalline.Site.topology f n)
      (BoundedFrame.DeRhamSections.frameComplex f m FY) _ (FramePulledMap.map f n m hnm (FY := FY))).f i ≫
        (Ext.ModuleFunctor.functor (Crystalline.ExactRestriction.Coeff (B := B)) (BoundedCrystalline.CrystallineCohomology.constantUnit f n) 0).map
          ((FrameMap.map f n m hnm α).f i) =
    (ModuleCat.uliftFunctor.{u + 2, u + 1} (Crystalline.ExactRestriction.Coeff (B := B))).map
      ((BoundedFrame.SectionChange.frameMap α).f i) ≫ (BoundedFrame.DeRhamSections.sectionsMap f n FX).f i := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact Module.ConstantSections.section_natural (Crystalline.ExactRestriction.Coeff (B := B)) (BoundedCrystalline.Site.topology f n)
    ((BoundedFrame.SectionChange.frameMap α).f i) ((FrameMap.map f n m hnm α).f i)
    ((FramePulledMap.map f n m hnm (FY := FY)).f i) ((BoundedFrame.DeRhamSections.sheafMap f n FX).f i)
    (map_component f n m hnm α i) x.down

theorem sections : ConstantSection.ComplexMap.map (Crystalline.ExactRestriction.Coeff (B := B)) (BoundedCrystalline.Site.topology f n)
    (BoundedFrame.DeRhamSections.frameComplex f m FY) _ (FramePulledMap.map f n m hnm (FY := FY)) ≫
      ((Ext.ModuleFunctor.functor (Crystalline.ExactRestriction.Coeff (B := B))
        (BoundedCrystalline.CrystallineCohomology.constantUnit f n) 0).mapHomologicalComplex (.up ℕ)).map
          (FrameMap.map f n m hnm α) =
    ((ModuleCat.uliftFunctor.{u + 2, u + 1} (Crystalline.ExactRestriction.Coeff (B := B))).mapHomologicalComplex (.up ℕ)).map
      (BoundedFrame.SectionChange.frameMap α) ≫ BoundedFrame.DeRhamSections.sectionsMap f n FX := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact sections_component f n m hnm α i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FramePulledMap
