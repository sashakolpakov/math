import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.FrameSource

/-! # Frame Pulled Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.FramePulledMap

noncomputable section

/-! The pulled crystalline frame map induces the original coefficient-linear de Rham section map. -/

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

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n

def map : ((constantSheaf (BoundedCrystalline.Site.topology f n) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))).mapHomologicalComplex (.up ℕ)).obj
    (BoundedFrame.DeRhamSections.frameComplex fY n FY) ⟶
      ((R).mapHomologicalComplex (.up ℕ)).obj (Bounded.RelativeSheafComplex.complex fY n FY) :=
  ConstantSection.ComplexRestriction.pulled G (Crystalline.ExactRestriction.Coeff (B := B)) (BoundedCrystalline.Site.topology f n) (BoundedCrystalline.Site.topology fY n)
    (BoundedFrame.DeRhamSections.frameComplex fY n FY) (Bounded.RelativeSheafComplex.complex fY n FY)
    (BoundedFrame.DeRhamSections.sheafMap fY n FY)

theorem square : FramePulledMap.map g hg n (FY := FY) ≫ FrameGeometricMap.map g hg n α =
    ((constantSheaf (BoundedCrystalline.Site.topology f n) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))).mapHomologicalComplex (.up ℕ)).map
      (BoundedFrame.SectionChange.frameMap α) ≫ BoundedFrame.DeRhamSections.sheafMap f n FX :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun a => (FrameSource.sourceIso g hg n (FY := FY)).inv ≫ a)
      (FrameGeometricSections.complexes g hg n α)).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun a => a ≫ BoundedFrame.DeRhamSections.sheafMap f n FX)
            (FrameSource.complexes g hg n α))))

theorem map_component (i : ℕ) :
    (constantSheaf (BoundedCrystalline.Site.topology f n) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))).map
      ((BoundedFrame.SectionChange.frameMap α).f i) ≫
        (BoundedFrame.DeRhamSections.sheafMap f n FX).f i =
    (FramePulledMap.map g hg n (FY := FY)).f i ≫ (FrameGeometricMap.map g hg n α).f i :=
  (congrArg (fun a => a.f i) (square g hg n α)).symm

theorem sections_component (i : ℕ) :
    (ConstantSection.ComplexMap.map (Crystalline.ExactRestriction.Coeff (B := B)) (BoundedCrystalline.Site.topology f n)
      (BoundedFrame.DeRhamSections.frameComplex fY n FY) _ (FramePulledMap.map g hg n (FY := FY))).f i ≫
        (Ext.ModuleFunctor.functor (Crystalline.ExactRestriction.Coeff (B := B)) (BoundedCrystalline.CrystallineCohomology.constantUnit f n) 0).map
          ((FrameGeometricMap.map g hg n α).f i) =
    (ModuleCat.uliftFunctor.{u + 2, u + 1} (Crystalline.ExactRestriction.Coeff (B := B))).map
      ((BoundedFrame.SectionChange.frameMap α).f i) ≫ (BoundedFrame.DeRhamSections.sectionsMap f n FX).f i := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact Module.ConstantSections.section_natural (Crystalline.ExactRestriction.Coeff (B := B)) (BoundedCrystalline.Site.topology f n)
    ((BoundedFrame.SectionChange.frameMap α).f i) ((FrameGeometricMap.map g hg n α).f i)
    ((FramePulledMap.map g hg n (FY := FY)).f i) ((BoundedFrame.DeRhamSections.sheafMap f n FX).f i)
    (map_component g hg n α i) x.down

theorem sections : ConstantSection.ComplexMap.map (Crystalline.ExactRestriction.Coeff (B := B)) (BoundedCrystalline.Site.topology f n)
    (BoundedFrame.DeRhamSections.frameComplex fY n FY) _ (FramePulledMap.map g hg n (FY := FY)) ≫
      ((Ext.ModuleFunctor.functor (Crystalline.ExactRestriction.Coeff (B := B))
        (BoundedCrystalline.CrystallineCohomology.constantUnit f n) 0).mapHomologicalComplex (.up ℕ)).map
          (FrameGeometricMap.map g hg n α) =
    ((ModuleCat.uliftFunctor.{u + 2, u + 1} (Crystalline.ExactRestriction.Coeff (B := B))).mapHomologicalComplex (.up ℕ)).map
      (BoundedFrame.SectionChange.frameMap α) ≫ BoundedFrame.DeRhamSections.sectionsMap f n FX := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact sections_component g hg n α i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.FramePulledMap
