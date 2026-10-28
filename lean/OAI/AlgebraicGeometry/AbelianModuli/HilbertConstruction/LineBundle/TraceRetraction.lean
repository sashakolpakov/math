import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.PairingRetraction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TracedInversePairing

/-! # Trace Retraction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TraceRetraction

noncomputable section

/-! Every structure-sheaf trace retraction induces a retraction of the pullback unit for every line bundle. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem lineBundle_pullbackUnit_splitMono_of_structureTrace {X Y : Scheme.{u}}
    (f : Y ⟶ X) (L : Line.Bundles.LineBundle X)
    (t : (Scheme.Modules.pushforward f).obj (Line.Bundles.structureModule Y) ⟶ Line.Bundles.structureModule X)
    (ht : SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫ t = 𝟙 _) :
    IsSplitMono ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L.sheaf) := by
  obtain ⟨r, hr⟩ := PairingRetraction.lineBundlePairing_exists_retraction L.reciprocalFrameBundle
    (show L.sheaf ⟶ (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj L.sheaf) from
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L.sheaf)
    L.tensorReciprocalFrameIso
    (TracedInversePairing.tracedInversePairing f L L.reciprocalFrameBundle L.tensorReciprocalFrameIso t)
    (TracedInversePairing.tracedInversePairing_unit f L L.reciprocalFrameBundle L.tensorReciprocalFrameIso t ht)
  exact ⟨⟨r, hr⟩⟩

theorem lineBundle_pullbackUnit_splitMono_of_structureUnit_splitMono {X Y : Scheme.{u}}
    (f : Y ⟶ X) (L : Line.Bundles.LineBundle X)
    (h : IsSplitMono (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) :
    IsSplitMono ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L.sheaf) := by
  obtain ⟨⟨t, ht⟩⟩ := h
  exact lineBundle_pullbackUnit_splitMono_of_structureTrace f L t ht

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TraceRetraction
