import OAI.AlgebraicGeometry.Picard.PoincareBundle.StructureUnitComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles

/-! # Pullback Section Squares -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PullbackSectionSquares.Construction

noncomputable section

/-! Actual sections respect the canonical pullback composition and
commuting-square isomorphisms, including their structure-module units. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles

universe u
variable {X Y Z : Scheme.{u}}

theorem pullbackSection_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    {L : Z.Modules} (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Z ⟶ L) :
    AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection g s) ≫ (Scheme.Modules.pullbackComp f g).hom.app L =
      AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (f ≫ g) s := by
  have hi := congrArg Iso.inv (Picard.PoincareBundle.StructureUnitComposition.unitIso_comp f g)
  change (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).inv ≫
      (Scheme.Modules.pullback f).map (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso g).inv =
    (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (f ≫ g)).inv ≫
      (Scheme.Modules.pullbackComp f g).inv.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Z) at hi
  have hn := (Scheme.Modules.pullbackComp f g).hom.naturality s
  change (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map s) ≫
      (Scheme.Modules.pullbackComp f g).hom.app L =
    (Scheme.Modules.pullbackComp f g).hom.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Z) ≫
      (Scheme.Modules.pullback (f ≫ g)).map s at hn
  simp only [AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection, Functor.map_comp, Category.assoc]
  rw [hn]
  simp only [← Category.assoc]
  rw [hi]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

theorem pullbackSection_congr {f g : X ⟶ Y} (h : f = g)
    {L : Y.Modules} (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ L) :
    AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s ≫ (Scheme.Modules.pullbackCongr h).hom.app L =
      AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection g s := by
  subst g
  exact Category.comp_id _

def sectionPullbackSquareIso {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (j : X' ⟶ X) (i : Y' ⟶ Y)
    (h : j ≫ f = g ≫ i) (L : Y.Modules) :
    (Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback f).obj L) ≅
      (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback i).obj L) :=
  ((Scheme.Modules.pullbackComp j f) ≪≫ Scheme.Modules.pullbackCongr h ≪≫
    (Scheme.Modules.pullbackComp g i).symm).app L

theorem sectionPullbackSquareIso_section {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (j : X' ⟶ X) (i : Y' ⟶ Y)
    (h : j ≫ f = g ≫ i) {L : Y.Modules} (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ L) :
    AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection j (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s) ≫ (sectionPullbackSquareIso f g j i h L).hom =
      AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection g (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection i s) := by
  change AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection j (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s) ≫
      ((Scheme.Modules.pullbackComp j f).hom.app L ≫
        (Scheme.Modules.pullbackCongr h).hom.app L ≫ (Scheme.Modules.pullbackComp g i).inv.app L) = _
  simp only [← Category.assoc]
  rw [pullbackSection_comp, pullbackSection_congr]
  apply (cancel_mono ((Scheme.Modules.pullbackComp g i).hom.app L)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id, pullbackSection_comp]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PullbackSectionSquares.Construction
