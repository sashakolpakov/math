import OAI.AlgebraicGeometry.Picard.PoincareBundle.StructureUnitComposition
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization

/-! # Structure Unit Gluing -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.StructureUnitGluing

noncomputable section

/-!
# The actual structure-sheaf pullback identifications respect geometric gluing
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization

/-- Equality of scheme maps intertwines their actual structure-sheaf pullback identifications. -/
theorem unitIso_congr {X Y : Scheme.{u}} (f g : X ⟶ Y) (h : f = g) :
    (Scheme.Modules.pullbackCongr h).app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso g =
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f := by
  cases h
  change Iso.refl _ ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f = _
  exact Iso.refl_trans _

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (p q : Z ⟶ X) (h : p ≫ f = q ≫ f)

/-- The standard geometric gluing takes one iterated structure-sheaf identification to the other. -/
theorem unit_gluing :
    (Scheme.Modules.pullback p).map (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom ≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso p).hom =
      (Cech.MateNormalization.standardGluing f p q h).hom.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) ≫
        (Scheme.Modules.pullback q).map (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom ≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso q).hom := by
  have hp := congrArg Iso.hom (StructureUnitComposition.unitIso_comp p f)
  have hq := congrArg Iso.hom (StructureUnitComposition.unitIso_comp q f)
  have hc := congrArg Iso.hom (unitIso_congr (p ≫ f) (q ≫ f) h)
  change (Scheme.Modules.pullback p).map (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom ≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso p).hom =
    (Scheme.Modules.pullbackComp p f).hom.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) ≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (p ≫ f)).hom at hp
  change (Scheme.Modules.pullback q).map (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom ≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso q).hom =
    (Scheme.Modules.pullbackComp q f).hom.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) ≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (q ≫ f)).hom at hq
  rw [hp, hq]
  change (Scheme.Modules.pullbackComp p f).hom.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) ≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (p ≫ f)).hom =
    ((Scheme.Modules.pullbackComp p f).hom.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) ≫
      (Scheme.Modules.pullbackCongr h).hom.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) ≫
      (Scheme.Modules.pullbackComp q f).inv.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y)) ≫
        (Scheme.Modules.pullbackComp q f).hom.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) ≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (q ≫ f)).hom
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  exact congrArg (fun a => (Scheme.Modules.pullbackComp p f).hom.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) ≫ a) hc.symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.StructureUnitGluing
