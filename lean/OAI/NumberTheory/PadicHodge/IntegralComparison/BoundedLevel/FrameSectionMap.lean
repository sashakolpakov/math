import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameSheafSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SectionChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameMap

/-! # Frame Section Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameSectionMap

noncomputable section

/-! Actual frame section maps commute with restriction between bounded levels and change of frame together. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f]
  (n m : ℕ) (hnm : n ≤ m)
  {FX : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n}
  {FY : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f m}
  (α : (BoundedCrystalline.LevelMaps.inclusion (p := p) (J := J) (δ := δ) f n m hnm).obj FX ⟶ FY)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.restriction (p := p) (J := J) (δ := δ) f n m hnm

def sourceMap : ((R).mapHomologicalComplex (.up ℕ)).obj
    (((constantSheaf (BoundedCrystalline.Site.topology f m) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))).mapHomologicalComplex (.up ℕ)).obj (BoundedFrame.DeRhamSections.frameComplex f m FY)) ⟶
      ((constantSheaf (BoundedCrystalline.Site.topology f n) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))).mapHomologicalComplex (.up ℕ)).obj (BoundedFrame.DeRhamSections.frameComplex f n FX) :=
  ((R).mapHomologicalComplex (.up ℕ)).map (((constantSheaf (BoundedCrystalline.Site.topology f m) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))).mapHomologicalComplex (.up ℕ)).map (BoundedFrame.SectionChange.frameMap α)) ≫
    (FrameSheafSections.sourceIso f n m hnm FX).hom

theorem complexes : ((R).mapHomologicalComplex (.up ℕ)).map
    (BoundedFrame.DeRhamSections.sheafMap f m FY) ≫ FrameMap.map f n m hnm α =
      sourceMap f n m hnm α ≫ BoundedFrame.DeRhamSections.sheafMap f n FX := by
  let T := (R).mapHomologicalComplex (.up ℕ)
  have h₁ := (T.map_comp (BoundedFrame.DeRhamSections.sheafMap f m FY)
    (BoundedFrame.Change.sheafMap α)).symm.trans
      ((congrArg T.map (BoundedFrame.SectionChange.sheaf_naturality α)).trans (T.map_comp _ _))
  have h₂ := FrameSheafSections.complexes f n m hnm FX
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ (FrameSheaves.complexIso f n m hnm FX).hom) h₁).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun a => T.map (((constantSheaf (BoundedCrystalline.Site.topology f m) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))).mapHomologicalComplex (.up ℕ)).map (BoundedFrame.SectionChange.frameMap α)) ≫ a) h₂).trans
          (Category.assoc _ _ _).symm)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameSectionMap
