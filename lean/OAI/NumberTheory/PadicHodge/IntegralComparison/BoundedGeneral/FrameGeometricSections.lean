import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.FrameSheafSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SectionChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.FrameGeometricMap

/-! # Frame Geometric Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.FrameGeometricSections

noncomputable section

/-! Actual frame section maps commute with geometric restriction and change of frame together. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  [IsSeparated f] [IsSeparated fY] (g : X ⟶ Y) (hg : g ≫ fY = f) (n : ℕ)
  {FX : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n}
  {FY : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n}
  (α : (BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n).obj FX ⟶ FY)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n

def sourceMap : ((R).mapHomologicalComplex (.up ℕ)).obj
    (((constantSheaf (BoundedCrystalline.Site.topology fY n) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))).mapHomologicalComplex (.up ℕ)).obj (BoundedFrame.DeRhamSections.frameComplex fY n FY)) ⟶
      ((constantSheaf (BoundedCrystalline.Site.topology f n) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))).mapHomologicalComplex (.up ℕ)).obj (BoundedFrame.DeRhamSections.frameComplex f n FX) :=
  ((R).mapHomologicalComplex (.up ℕ)).map (((constantSheaf (BoundedCrystalline.Site.topology fY n) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))).mapHomologicalComplex (.up ℕ)).map (BoundedFrame.SectionChange.frameMap α)) ≫
    (FrameSheafSections.sourceIso g hg n FX).hom

theorem complexes : ((R).mapHomologicalComplex (.up ℕ)).map
    (BoundedFrame.DeRhamSections.sheafMap fY n FY) ≫ FrameGeometricMap.map g hg n α =
      sourceMap g hg n α ≫ BoundedFrame.DeRhamSections.sheafMap f n FX := by
  let T := (R).mapHomologicalComplex (.up ℕ)
  have h₁ := (T.map_comp (BoundedFrame.DeRhamSections.sheafMap fY n FY)
    (BoundedFrame.Change.sheafMap α)).symm.trans
      ((congrArg T.map (BoundedFrame.SectionChange.sheaf_naturality α)).trans (T.map_comp _ _))
  have h₂ := FrameSheafSections.complexes g hg n FX
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ FrameSheafMap.map g hg n FX) h₁).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun a => T.map (((constantSheaf (BoundedCrystalline.Site.topology fY n) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))).mapHomologicalComplex (.up ℕ)).map (BoundedFrame.SectionChange.frameMap α)) ≫ a) h₂).trans
          (Category.assoc _ _ _).symm)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.FrameGeometricSections
