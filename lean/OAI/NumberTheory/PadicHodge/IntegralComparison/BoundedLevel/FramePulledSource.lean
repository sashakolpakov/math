import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameConstant
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameSectionMap

/-! # Frame Pulled Source -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FramePulledSource

noncomputable section

/-! Pulling back the original constant frame source gives the actual coefficient-linear frame map. -/

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

def sourceIso : ((R).mapHomologicalComplex (.up ℕ)).obj
    (((constantSheaf (BoundedCrystalline.Site.topology f m) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))).mapHomologicalComplex (.up ℕ)).obj
      (BoundedFrame.DeRhamSections.frameComplex f m FY)) ≅
    ((constantSheaf (BoundedCrystalline.Site.topology f n) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))).mapHomologicalComplex (.up ℕ)).obj
      (BoundedFrame.DeRhamSections.frameComplex f m FY) :=
  (NatIso.mapHomologicalComplex (ConstantSection.ComplexRestriction.constantIso G (Crystalline.ExactRestriction.Coeff (B := B))
    (BoundedCrystalline.Site.topology f n) (BoundedCrystalline.Site.topology f m)) (.up ℕ)).app (BoundedFrame.DeRhamSections.frameComplex f m FY)

omit [Fact p.Prime] [IsSeparated f]  in
theorem component (i : ℕ) : (sourceIso f n m hnm (FY := FY)).inv.f i ≫
    (FrameSectionMap.sourceMap f n m hnm α).f i =
      (constantSheaf (BoundedCrystalline.Site.topology f n) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))).map
        ((BoundedFrame.SectionChange.frameMap α).f i) := by
  let e := ConstantSection.ComplexRestriction.constantIso G (Crystalline.ExactRestriction.Coeff (B := B)) (BoundedCrystalline.Site.topology f n) (BoundedCrystalline.Site.topology f m)
  let b := (BoundedFrame.SectionChange.frameMap α).f i
  have hn := e.hom.naturality b
  have hx := FrameConstant.component f n m hnm FX i
  have h₁ := congrArg (fun a => (e.app _).inv ≫
    (R).map ((constantSheaf (BoundedCrystalline.Site.topology f m) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))).map b) ≫ a) hx
  have h₂ := congrArg (fun a => (e.app _).inv ≫ a) hn
  exact h₁.trans (h₂.trans (Iso.inv_hom_id_assoc _ _))

omit [Fact p.Prime] [IsSeparated f]  in
theorem complexes : (sourceIso f n m hnm (FY := FY)).inv ≫
    FrameSectionMap.sourceMap f n m hnm α =
      ((constantSheaf (BoundedCrystalline.Site.topology f n) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))).mapHomologicalComplex (.up ℕ)).map
        (BoundedFrame.SectionChange.frameMap α) := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact component f n m hnm α i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FramePulledSource
