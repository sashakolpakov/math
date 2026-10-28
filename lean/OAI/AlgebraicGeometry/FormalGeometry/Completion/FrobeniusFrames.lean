import OAI.AlgebraicGeometry.FormalGeometry.Completion.FrobeniusFinite
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.FrameCoordinates
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PullbackScalarsValue

/-! # Frobenius Frames -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.FrobeniusFrames.Construction

noncomputable section

/-! Actual Frobenius pullback and tensor powers have the same line-bundle transition functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.FrameCoordinates

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

/-- Ratios in frames pull back along every actual scheme morphism. -/
theorem frameCoordinate_arbitrary_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : Y.Modules} (s t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ M) [IsIso s] :
    AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s) (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f t) =
      f.appTop (AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate s t) := by
  have he : AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinateEnd (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s) (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f t) =
      (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).inv ≫
        (Scheme.Modules.pullback f).map (AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinateEnd s t) ≫
          (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom := by
    apply (cancel_mono (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s)).mp
    rw [AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinateEnd_frame]
    simp only [AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinateEnd, AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection, Category.assoc,
      Iso.hom_inv_id_assoc, ← Functor.map_comp, IsIso.inv_hom_id, Category.comp_id]
  exact (congrArg (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X) he).trans
    (Quotients.FiniteDescent.PullbackScalarsValue.Construction.PullbackScalars.value_pullback f (AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinateEnd s t))

/-- Matching transition coordinates make the two frame-defined isomorphisms equal. -/
theorem frameIso_eq_of_coordinates {X : Scheme.{u}} {M N : X.Modules}
    (s t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) (a b : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ N)
    [IsIso s] [IsIso t] [IsIso a] [IsIso b]
    (h : AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate s t = AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate a b) :
    (asIso s).symm ≪≫ asIso a = (asIso t).symm ≪≫ asIso b := by
  have hc : AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinateEnd s t = AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinateEnd a b :=
    AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndValue_injective X h
  apply Iso.ext
  apply (cancel_epi t).mp
  change t ≫ (inv s ≫ a) = t ≫ (inv t ≫ b)
  rw [← Category.assoc, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  change AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinateEnd s t ≫ a = b
  rw [hc, AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinateEnd_frame]

variable (k : Type u) [Field k] [Fintype k]
  (X : Scheme.{u}) (κ : k →+* Γ(X, ⊤)) {M : X.Modules}

/-- The actual pullback-power comparison defined in any trivializing frame. -/
def frobeniusFrameIso (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) [IsIso s] :
    (Scheme.Modules.pullback (Frobenius.Construction.qPowerSchemeFrobenius k X κ)).obj M ≅
      AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule M (Fintype.card k) :=
  (asIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (Frobenius.Construction.qPowerSchemeFrobenius k X κ) s)).symm ≪≫
    asIso (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerSection s (Fintype.card k))

/-- Frobenius pullback and tensor powers have exactly equal transition coordinates. -/
theorem frobeniusFrame_coordinates (s t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) [IsIso s] :
    AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (Frobenius.Construction.qPowerSchemeFrobenius k X κ) s)
      (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (Frobenius.Construction.qPowerSchemeFrobenius k X κ) t) =
    AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerSection s (Fintype.card k))
      (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerSection t (Fintype.card k)) := by
  rw [frameCoordinate_arbitrary_pullback, Frobenius.Construction.qPowerSchemeFrobenius_appTop,
    AbelianModuli.HilbertConstruction.Power.FrameCoordinates.frameCoordinate_tensorPowerSection]

/-- The local Frobenius comparison is independent of the chosen frame. -/
theorem frobeniusFrameIso_independent (s t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) [IsIso s] [IsIso t] :
    frobeniusFrameIso k X κ s = frobeniusFrameIso k X κ t :=
  frameIso_eq_of_coordinates _ _ _ _ (frobeniusFrame_coordinates k X κ s t)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.FrobeniusFrames.Construction
