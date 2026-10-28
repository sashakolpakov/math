import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.FrameCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Comparison

/-! # Power Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.PowerCoordinates

noncomputable section

/-!
Tensor-power coordinate formulas for sections which become frames only after
restriction. The comparison uses the actual pullback and tensor-power functors.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (n : ℕ)

/-- The restriction comparison is natural in the module sheaf. -/
def tensorPowerRestrictNatIso :
    Scheme.Modules.restrictFunctor f ⋙ TensorPower.Maps.tensorPowerFunctor X n ≅
      TensorPower.Maps.tensorPowerFunctor Y n ⋙ Scheme.Modules.restrictFunctor f :=
  NatIso.ofComponents (fun L => TensorPower.RestrictionMaps.tensorPowerRestrictIso f L n)
    (fun a => TensorPower.RestrictionMaps.tensorPowerRestrictIso_naturality f a)

/-- Tensor powers commute with pullback along open immersions, naturally in
the original module sheaf. -/
def tensorPowerPullbackNatIso :
    Scheme.Modules.pullback f ⋙ TensorPower.Maps.tensorPowerFunctor X n ≅
      TensorPower.Maps.tensorPowerFunctor Y n ⋙ Scheme.Modules.pullback f :=
  Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback f).symm
      (TensorPower.Maps.tensorPowerFunctor X n) ≪≫
    tensorPowerRestrictNatIso f n ≪≫
    Functor.isoWhiskerLeft (TensorPower.Maps.tensorPowerFunctor Y n) (Scheme.Modules.restrictFunctorIsoPullback f)

/-- Unit comparison for taking a tensor power after pullback. -/
def powerPullbackUnitIso :
    (Scheme.Modules.pullback f ⋙ TensorPower.Maps.tensorPowerFunctor X n).obj (Line.Bundles.structureModule Y) ≅
      Line.Bundles.structureModule X :=
  (TensorPower.Maps.tensorPowerFunctor X n).mapIso (Line.Bundles.structureModulePullbackIso f) ≪≫ TensorPower.Maps.tensorPowerUnitIso X n

/-- Unit comparison for pulling back a tensor power. -/
def pullbackPowerUnitIso :
    (TensorPower.Maps.tensorPowerFunctor Y n ⋙ Scheme.Modules.pullback f).obj (Line.Bundles.structureModule Y) ≅
      Line.Bundles.structureModule X :=
  (Scheme.Modules.pullback f).mapIso (TensorPower.Maps.tensorPowerUnitIso Y n) ≪≫ Line.Bundles.structureModulePullbackIso f

omit [IsOpenImmersion f] in
theorem powerPullbackUnitIso_section {L : Y.Modules} (s : Line.Bundles.structureModule Y ⟶ L) :
    (powerPullbackUnitIso f n).inv ≫
      (Scheme.Modules.pullback f ⋙ TensorPower.Maps.tensorPowerFunctor X n).map s =
        TensorPower.Maps.tensorPowerSection (Ample.LineBundles.pullbackSection f s) n := by
  change ((TensorPower.Maps.tensorPowerUnitIso X n).inv ≫ TensorPower.Maps.tensorPowerMap (Line.Bundles.structureModulePullbackIso f).inv n) ≫
    TensorPower.Maps.tensorPowerMap ((Scheme.Modules.pullback f).map s) n =
      (TensorPower.Maps.tensorPowerUnitIso X n).inv ≫
        TensorPower.Maps.tensorPowerMap ((Line.Bundles.structureModulePullbackIso f).inv ≫ (Scheme.Modules.pullback f).map s) n
  rw [TensorPower.Maps.tensorPowerMap_comp, Category.assoc]

omit [IsOpenImmersion f] in
theorem pullbackPowerUnitIso_section {L : Y.Modules} (s : Line.Bundles.structureModule Y ⟶ L) :
    (pullbackPowerUnitIso f n).inv ≫
      (TensorPower.Maps.tensorPowerFunctor Y n ⋙ Scheme.Modules.pullback f).map s =
        Ample.LineBundles.pullbackSection f (TensorPower.Maps.tensorPowerSection s n) := by
  change ((Line.Bundles.structureModulePullbackIso f).inv ≫
      (Scheme.Modules.pullback f).map (TensorPower.Maps.tensorPowerUnitIso Y n).inv) ≫
    (Scheme.Modules.pullback f).map (TensorPower.Maps.tensorPowerMap s n) =
      (Line.Bundles.structureModulePullbackIso f).inv ≫ (Scheme.Modules.pullback f).map
        ((TensorPower.Maps.tensorPowerUnitIso Y n).inv ≫ TensorPower.Maps.tensorPowerMap s n)
  rw [Functor.map_comp, Category.assoc]

/-- If a denominator section is a frame on an open subscheme, the coordinates
of its powers on that open are the ordinary powers of the original coordinates. -/
theorem frameCoordinate_local_tensorPower {L : Y.Modules}
    (s t : Line.Bundles.structureModule Y ⟶ L) [IsIso (Ample.LineBundles.pullbackSection f s)] :
    letI := Power.Nonvanishing.tensorPowerSection_pullback_isIso f s n
    Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection f (TensorPower.Maps.tensorPowerSection s n))
      (Ample.LineBundles.pullbackSection f (TensorPower.Maps.tensorPowerSection t n)) =
        (Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection f s) (Ample.LineBundles.pullbackSection f t)) ^ n := by
  have : IsIso (Ample.LineBundles.pullbackSection f (TensorPower.Maps.tensorPowerSection s n)) :=
    Power.Nonvanishing.tensorPowerSection_pullback_isIso f s n
  let F := Scheme.Modules.pullback f ⋙ TensorPower.Maps.tensorPowerFunctor X n
  let G := TensorPower.Maps.tensorPowerFunctor Y n ⋙ Scheme.Modules.pullback f
  let uF := powerPullbackUnitIso f n
  let uG := pullbackPowerUnitIso f n
  have hFs : uF.inv ≫ F.map s = TensorPower.Maps.tensorPowerSection (Ample.LineBundles.pullbackSection f s) n :=
    powerPullbackUnitIso_section f n s
  have hFt : uF.inv ≫ F.map t = TensorPower.Maps.tensorPowerSection (Ample.LineBundles.pullbackSection f t) n :=
    powerPullbackUnitIso_section f n t
  have hGs : uG.inv ≫ G.map s = Ample.LineBundles.pullbackSection f (TensorPower.Maps.tensorPowerSection s n) :=
    pullbackPowerUnitIso_section f n s
  have hGt : uG.inv ≫ G.map t = Ample.LineBundles.pullbackSection f (TensorPower.Maps.tensorPowerSection t n) :=
    pullbackPowerUnitIso_section f n t
  have hFi : IsIso (uF.inv ≫ F.map s) := hFs.symm ▸ inferInstanceAs
    (IsIso (TensorPower.Maps.tensorPowerSection (Ample.LineBundles.pullbackSection f s) n))
  have hGi : IsIso (uG.inv ≫ G.map s) := hGs.symm ▸ Power.Nonvanishing.tensorPowerSection_pullback_isIso f s n
  have hGc := @Frame.FrameRestriction.frameCoordinate_congr X (G.obj L) _ _ _ _ hGi
    (Power.Nonvanishing.tensorPowerSection_pullback_isIso f s n) hGs hGt
  have hFc := @Frame.FrameRestriction.frameCoordinate_congr X (F.obj L) _ _ _ _ hFi
    (inferInstanceAs (IsIso (TensorPower.Maps.tensorPowerSection (Ample.LineBundles.pullbackSection f s) n))) hFs hFt
  exact hGc.symm.trans
    ((Frame.Comparison.frameCoordinate_functorComparison F G (tensorPowerPullbackNatIso f n) uF uG s t).trans
      (hFc.trans
        (Power.FrameCoordinates.frameCoordinate_tensorPowerSection (Ample.LineBundles.pullbackSection f s) (Ample.LineBundles.pullbackSection f t) n)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.PowerCoordinates
