import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackComposition
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.UnitPullback

/-! # Structure Unit Composition -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.StructureUnitComposition

noncomputable section

/-!
# The canonical structure-sheaf pullback identifications respect composition
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.UnitPullback

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The actual structure-sheaf map of a composite is the composite of the two actual maps. -/
theorem baseUnitMap_comp :
    Tensor.UnitPullback.baseUnitMap g ≫ (Scheme.Modules.pushforward g).map (Tensor.UnitPullback.baseUnitMap f) ≫
      (Scheme.Modules.pushforwardComp f g).hom.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) = Tensor.UnitPullback.baseUnitMap (f ≫ g) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  rfl

/-- Transposition gives the exact inverse-composition formula for the canonical structure-sheaf identifications. -/
theorem unitIso_comp_inv :
    (Scheme.Modules.pullbackComp f g).inv.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Z) ≫
      (Scheme.Modules.pullback f).map (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso g).hom ≫
        (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom = (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (f ≫ g)).hom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _).injective
  rw [Tensor.PullbackComposition.homEquiv_composition,
    Adjunction.homEquiv_naturality_left, Tensor.UnitPullback.unitIso_homEquiv,
    Adjunction.homEquiv_naturality_right, Tensor.UnitPullback.unitIso_homEquiv, Tensor.UnitPullback.unitIso_homEquiv]
  exact baseUnitMap_comp f g

/-- The whole canonical structure-sheaf pullback isomorphism is coherent for composition. -/
theorem unitIso_comp :
    (Scheme.Modules.pullback f).mapIso (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso g) ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f =
      (Scheme.Modules.pullbackComp f g).app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Z) ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (f ≫ g) := by
  apply Iso.ext
  apply (cancel_epi ((Scheme.Modules.pullbackComp f g).inv.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Z))).mp
  change (Scheme.Modules.pullbackComp f g).inv.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Z) ≫
      (Scheme.Modules.pullback f).map (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso g).hom ≫
        (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom =
    (Scheme.Modules.pullbackComp f g).inv.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Z) ≫
      (Scheme.Modules.pullbackComp f g).hom.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Z) ≫
        (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (f ≫ g)).hom
  rw [unitIso_comp_inv, Iso.inv_hom_id_app_assoc]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.StructureUnitComposition
