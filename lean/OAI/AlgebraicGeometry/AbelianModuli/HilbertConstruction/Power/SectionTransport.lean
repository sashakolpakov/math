import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.PowerCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.FrameTransport

/-! # Section Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.SectionTransport

noncomputable section

/-!
Transfer sections of a power of a pulled-back line bundle into the pullback of
the original power. The unit correction makes the power of each original
section transfer to its prescribed pullback exactly.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (n : ℕ)

def tensorPowerPullbackSourceIso : Line.Bundles.structureModule X ≅ Line.Bundles.structureModule X :=
  (Local.PowerCoordinates.pullbackPowerUnitIso f n).symm ≪≫
    (Local.PowerCoordinates.tensorPowerPullbackNatIso f n).symm.app (Line.Bundles.structureModule Y) ≪≫ Local.PowerCoordinates.powerPullbackUnitIso f n

/-- Transfer a local power-section into the pullback of the original power. -/
def transportPowerSection {L : Y.Modules}
    (t : Line.Bundles.structureModule X ⟶ TensorPower.PowerSheaf.tensorPowerModule ((Scheme.Modules.pullback f).obj L) n) :
    Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj (TensorPower.PowerSheaf.tensorPowerModule L n) :=
  (tensorPowerPullbackSourceIso f n).hom ≫ t ≫ ((Local.PowerCoordinates.tensorPowerPullbackNatIso f n).app L).hom

/-- The transfer sends the power of a pulled-back section to the pullback of its power. -/
theorem transportPowerSection_power {L : Y.Modules} (s : Line.Bundles.structureModule Y ⟶ L) :
    transportPowerSection f n (TensorPower.Maps.tensorPowerSection (Ample.LineBundles.pullbackSection f s) n) =
      Ample.LineBundles.pullbackSection f (TensorPower.Maps.tensorPowerSection s n) := by
  let F := Scheme.Modules.pullback f ⋙ TensorPower.Maps.tensorPowerFunctor X n
  let G := TensorPower.Maps.tensorPowerFunctor Y n ⋙ Scheme.Modules.pullback f
  have h := Frame.Comparison.framedSection_functorComparison F G (Local.PowerCoordinates.tensorPowerPullbackNatIso f n)
    (Local.PowerCoordinates.powerPullbackUnitIso f n) (Local.PowerCoordinates.pullbackPowerUnitIso f n) s
  have hs := Local.PowerCoordinates.powerPullbackUnitIso_section f n s
  have ht := Local.PowerCoordinates.pullbackPowerUnitIso_section f n s
  exact (congrArg (fun z => (tensorPowerPullbackSourceIso f n).hom ≫ z ≫
      ((Local.PowerCoordinates.tensorPowerPullbackNatIso f n).app L).hom) hs.symm).trans
    ((Category.assoc _ _ _).symm.trans (h.trans ht))

/-- The power transfer preserves ratios after any further scheme pullback. -/
theorem frameCoordinate_transportPowerSection (h : Z ⟶ X) {L : Y.Modules}
    (s t : Line.Bundles.structureModule X ⟶ TensorPower.PowerSheaf.tensorPowerModule ((Scheme.Modules.pullback f).obj L) n)
    [hs : IsIso (Ample.LineBundles.pullbackSection h s)] :
    letI : IsIso (Ample.LineBundles.pullbackSection h (transportPowerSection f n s)) :=
      @Section.FrameTransport.pullbackSection_frameTransport_isIso Z X h _ _ (tensorPowerPullbackSourceIso f n)
        ((Local.PowerCoordinates.tensorPowerPullbackNatIso f n).app L) s hs
    Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection h (transportPowerSection f n s))
      (Ample.LineBundles.pullbackSection h (transportPowerSection f n t)) =
        Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection h s) (Ample.LineBundles.pullbackSection h t) :=
  @Section.FrameTransport.frameCoordinate_pullback_frameTransport Z X h _ _ (tensorPowerPullbackSourceIso f n)
    ((Local.PowerCoordinates.tensorPowerPullbackNatIso f n).app L) s t hs

/-- A section that frames after two restrictions still frames there after any tensor power. -/
theorem iteratedPullback_power_isIso (h : Z ⟶ X) [IsOpenImmersion h] {L : Y.Modules}
    (s : Line.Bundles.structureModule Y ⟶ L) [IsIso (Ample.LineBundles.pullbackSection h (Ample.LineBundles.pullbackSection f s))] :
    IsIso (Ample.LineBundles.pullbackSection h (Ample.LineBundles.pullbackSection f (TensorPower.Maps.tensorPowerSection s n))) := by
  have : IsIso (Ample.LineBundles.pullbackSection (h ≫ f) s) :=
    (Section.Nonvanishing.isIso_pullbackSection_comp_iff f h s).mp inferInstance
  have hp := Nonvanishing.tensorPowerSection_pullback_isIso (h ≫ f) s n
  exact (Section.Nonvanishing.isIso_pullbackSection_comp_iff f h (TensorPower.Maps.tensorPowerSection s n)).mpr hp

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.SectionTransport
