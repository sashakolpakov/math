import OAI.AlgebraicGeometry.Picard.PoincareBundle.StructureUnitComposition
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FrameRatioPullback

/-! # Frame Pullback Composition -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.FramePullbackComposition

noncomputable section

/-!
# Canonical pullback of normalized line frames respects composition and equality of base maps
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FrameRatioPullback

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The inverse unit identifications have the exact composition formula needed by normalized frames. -/
theorem unit_inverse_comp :
    (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).inv ≫ (Scheme.Modules.pullback f).map (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso g).inv =
      (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (f ≫ g)).inv ≫ (Scheme.Modules.pullbackComp f g).inv.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Z) :=
  congrArg Iso.inv (StructureUnitComposition.unitIso_comp f g)

/-- Pulling a normalized frame twice is canonically the same actual frame as pulling it along the composite. -/
theorem pullFrame_comp {M : Z.Modules} (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Z ≅ M) :
    FrameRatioPullback.pullFrame f (FrameRatioPullback.pullFrame g s) ≪≫ (Scheme.Modules.pullbackComp f g).app M = FrameRatioPullback.pullFrame (f ≫ g) s := by
  apply Iso.ext
  change ((AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).inv ≫ (Scheme.Modules.pullback f).map
      ((AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso g).inv ≫ (Scheme.Modules.pullback g).map s.hom)) ≫
      (Scheme.Modules.pullbackComp f g).hom.app M =
    (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (f ≫ g)).inv ≫ (Scheme.Modules.pullback (f ≫ g)).map s.hom
  rw [(Scheme.Modules.pullback f).map_comp]
  simp only [Category.assoc]
  slice_lhs 1 2 => exact unit_inverse_comp f g
  slice_lhs 3 4 => exact (Scheme.Modules.pullbackComp f g).hom.naturality s.hom
  simp only [Iso.inv_hom_id_app_assoc]

/-- Equality of base maps identifies their pulled normalized frames through the actual pullback congruence. -/
theorem pullFrame_congr {M : Y.Modules} (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ M) (f' : X ⟶ Y) (h : f = f') :
    FrameRatioPullback.pullFrame f s ≪≫ (Scheme.Modules.pullbackCongr h).app M = FrameRatioPullback.pullFrame f' s := by
  cases h
  apply Iso.ext
  exact Category.comp_id _

/-- Pullback of a normalized frame followed by an isomorphism is the pullback frame followed by that isomorphism. -/
theorem pullFrame_trans {M N : Y.Modules} (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ M) (e : M ≅ N) :
    FrameRatioPullback.pullFrame f (s ≪≫ e) = FrameRatioPullback.pullFrame f s ≪≫ (Scheme.Modules.pullback f).mapIso e := by
  apply Iso.ext
  change (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).inv ≫ (Scheme.Modules.pullback f).map (s.hom ≫ e.hom) =
    ((AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).inv ≫ (Scheme.Modules.pullback f).map s.hom) ≫
      (Scheme.Modules.pullback f).map e.hom
  rw [Functor.map_comp, Category.assoc]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.FramePullbackComposition
