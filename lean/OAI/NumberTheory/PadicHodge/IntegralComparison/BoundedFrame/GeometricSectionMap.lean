import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SheafSectionMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SectionChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.GeometricMap

/-! # Geometric Section Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.GeometricSectionMap

noncomputable section

/-! Actual frame section maps commute with geometric restriction and change of frame together. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  [IsSeparated f] [IsSeparated fY] (g : X ⟶ Y) [Mono g] (hg : g ≫ fY = f) (n : ℕ)
  {FX : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n}
  {FY : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n}
  (α : (BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n).obj FX ⟶ FY)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n

def sourceMap : ((R).mapHomologicalComplex (.up ℕ)).obj
    (((constantSheaf (BoundedCrystalline.Site.topology fY n) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))).mapHomologicalComplex (.up ℕ)).obj (DeRhamSections.frameComplex fY n FY)) ⟶
      ((constantSheaf (BoundedCrystalline.Site.topology f n) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))).mapHomologicalComplex (.up ℕ)).obj (DeRhamSections.frameComplex f n FX) :=
  ((R).mapHomologicalComplex (.up ℕ)).map (((constantSheaf (BoundedCrystalline.Site.topology fY n) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))).mapHomologicalComplex (.up ℕ)).map (SectionChange.frameMap α)) ≫
    (SheafSectionMap.sourceIso g hg n FX).hom

theorem complexes : ((R).mapHomologicalComplex (.up ℕ)).map
    (DeRhamSections.sheafMap fY n FY) ≫ GeometricMap.map g hg n α =
      sourceMap g hg n α ≫ DeRhamSections.sheafMap f n FX := by
  let T := (R).mapHomologicalComplex (.up ℕ)
  have h₁ := (T.map_comp (DeRhamSections.sheafMap fY n FY)
    (Change.sheafMap α)).symm.trans
      ((congrArg T.map (SectionChange.sheaf_naturality α)).trans (T.map_comp _ _))
  have h₂ := SheafSectionMap.complexes g hg n FX
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ (SheafRestriction.complexIso g hg n FX).hom) h₁).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun a => T.map (((constantSheaf (BoundedCrystalline.Site.topology fY n) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))).mapHomologicalComplex (.up ℕ)).map (SectionChange.frameMap α)) ≫ a) h₂).trans
          (Category.assoc _ _ _).symm)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.GeometricSectionMap
