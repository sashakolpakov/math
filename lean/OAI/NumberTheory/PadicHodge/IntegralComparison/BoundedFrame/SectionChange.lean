import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.ChangeNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Change
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.DeRhamSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexNaturality

/-! # Section Change -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SectionChange

noncomputable section

/-!
# IntegralComparison: changing actual bounded frames commutes with their de Rham section maps
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} [IsSeparated f] {n : ℕ}
  {F G : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n} (α : G ⟶ F)

def frameMap : DeRhamSections.frameComplex f n F ⟶
    DeRhamSections.frameComplex f n G :=
  ((Crystalline.RelativeResolution.coefficientFunctor (B := B)).mapHomologicalComplex (ComplexShape.up ℕ)).map
    (RelativeFrame.ChangeNaturality.frameMap F.obj G.obj α.hom)

theorem sheaf_naturality : DeRhamSections.sheafMap f n F ≫ Change.sheafMap α =
    ((constantSheaf (BoundedCrystalline.Site.topology f n) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))).mapHomologicalComplex
      (ComplexShape.up ℕ)).map (frameMap α) ≫ DeRhamSections.sheafMap f n G := by
  let S := (Bounded.RelativeSheafComplex.sheafification (p := p) (J := J) (δ := δ) f n).mapHomologicalComplex
    (ComplexShape.up ℕ)
  have h := RelativeFrame.ChangeNaturality.complexes
    (Diagram.productDiagram G) (Diagram.productDiagram F)
    Diagram.baseDiagram (Diagram.projection G) (Diagram.projection F)
    (Change.diagramMap α) (Change.projection α) F.obj G.obj α.hom
    (Symbols.frameProjection G) (Symbols.frameProjection F)
    (Change.frameProjection α)
  exact (S.map_comp _ _).symm.trans ((congrArg S.map h).trans (S.map_comp _ _))

theorem sheaf_component (i : ℕ) :
    (constantSheaf (BoundedCrystalline.Site.topology f n) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))).map ((frameMap α).f i) ≫
      (DeRhamSections.sheafMap f n G).f i =
    (DeRhamSections.sheafMap f n F).f i ≫ (Change.sheafMap α).f i :=
  (congrArg (fun φ => φ.f i) (sheaf_naturality α)).symm

theorem sections_component (i : ℕ) : (DeRhamSections.sectionsMap f n F).f i ≫
    (Ext.ModuleFunctor.functor (Crystalline.ExactRestriction.Coeff (B := B)) (BoundedCrystalline.CrystallineCohomology.constantUnit f n) 0).map
      ((Change.sheafMap α).f i) =
    (ModuleCat.uliftFunctor.{u + 2, u + 1} (Crystalline.ExactRestriction.Coeff (B := B))).map ((frameMap α).f i) ≫
      (DeRhamSections.sectionsMap f n G).f i := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact Module.ConstantSections.section_natural (Crystalline.ExactRestriction.Coeff (B := B)) (BoundedCrystalline.Site.topology f n)
    ((frameMap α).f i) ((Change.sheafMap α).f i)
    ((DeRhamSections.sheafMap f n F).f i)
    ((DeRhamSections.sheafMap f n G).f i) (sheaf_component α i) x.down

theorem sections_naturality : DeRhamSections.sectionsMap f n F ≫
    ((Ext.ModuleFunctor.functor (Crystalline.ExactRestriction.Coeff (B := B)) (BoundedCrystalline.CrystallineCohomology.constantUnit f n) 0).mapHomologicalComplex
      (ComplexShape.up ℕ)).map (Change.sheafMap α) =
    ((ModuleCat.uliftFunctor.{u + 2, u + 1} (Crystalline.ExactRestriction.Coeff (B := B))).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (frameMap α) ≫ DeRhamSections.sectionsMap f n G := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact sections_component α i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SectionChange
