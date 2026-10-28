import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections

/-! # Unit Pullback Scalars -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.UnitPullbackScalars

noncomputable section

/-! Pullback of a structure-module endomorphism pulls back its actual
global scalar, through the canonical structure-module comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

def unitEndPullback (a : End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y)) : End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) :=
  (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).inv ≫ (Scheme.Modules.pullback f).map a ≫
    (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom

theorem unitEndPullback_comparison (a : End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y)) :
    (Scheme.Modules.pullback f).map a ≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom =
      (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom ≫ unitEndPullback f a := by
  simp [unitEndPullback]

theorem unitEndPullback_adjunction (a : End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y)) :
    a ≫ SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward f).map (unitEndPullback f a) := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  have he : adj.homEquiv _ _ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  have h := congrArg (adj.homEquiv (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X))
    (unitEndPullback_comparison f a)
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right, he] at h
  exact h

theorem unitEndPullback_scalar (a : End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y)) :
    AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X (unitEndPullback f a) = f.appTop (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue Y a) := by
  have h := congrArg (fun q : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶
    (Scheme.Modules.pushforward f).obj (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) => q.app ⊤ (1 : Γ(Y, ⊤)))
    (unitEndPullback_adjunction f a)
  change f.appTop (a.app ⊤ (1 : Γ(Y, ⊤))) =
    (unitEndPullback f a).app ⊤ (f.appTop (1 : Γ(Y, ⊤))) at h
  change (unitEndPullback f a).app ⊤ (1 : Γ(X, ⊤)) =
    f.appTop (a.app ⊤ (1 : Γ(Y, ⊤)))
  rw [map_one] at h
  exact h.symm

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.UnitPullbackScalars
