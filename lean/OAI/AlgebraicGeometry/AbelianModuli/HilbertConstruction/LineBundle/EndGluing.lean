import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.LineBundleEndValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapCoverEquality

/-! # End Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Glue the frame-independent local scalar of a line-bundle endomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

structure LineBundle.EndGluing.LineEndFrameOpen (L : Line.Bundles.LineBundle X) where
  openSet : X.Opens
  frame : Line.Bundles.structureModule openSet.toScheme ≅ (Scheme.Modules.pullback openSet.ι).obj L.sheaf

def LineBundle.EndGluing.lineEndFrameCover (L : Line.Bundles.LineBundle X) : LineBundle.EndGluing.LineEndFrameOpen L → X.Opens :=
  LineBundle.EndGluing.LineEndFrameOpen.openSet

theorem LineBundle.EndGluing.lineEndFrameCover_covers (L : Line.Bundles.LineBundle X) (x : X) :
    ∃ i : LineBundle.EndGluing.LineEndFrameOpen L, x ∈ LineBundle.EndGluing.lineEndFrameCover L i := by
  obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyTrivial x
  exact ⟨⟨U, e.symm⟩, hx⟩

def LineBundle.EndGluing.lineEndTransferData (L : Line.Bundles.LineBundle X) (φ : End L.sheaf) :
    Module.OpenMapGluing.OpenCoverModuleMaps (LineBundle.EndGluing.lineEndFrameCover L) (Line.Bundles.structureModule X) (Line.Bundles.structureModule X) where
  localMap i := OpenPullback.ModuleValues.pullbackModuleRestrictionMap i.openSet.ι (Local.LineBundleEndTransfer.localLineEndTransfer i.openSet.ι φ i.frame)
  agree i j V hi hj := by
    change V ≤ i.openSet at hi
    change V ≤ j.openSet at hj
    let f : V.toScheme ⟶ i.openSet.toScheme := X.homOfLE hi
    let g : V.toScheme ⟶ j.openSet.toScheme := X.homOfLE hj
    have : IsOpenImmersion f := inferInstanceAs (IsOpenImmersion (X.homOfLE hi))
    have : IsOpenImmersion g := inferInstanceAs (IsOpenImmersion (X.homOfLE hj))
    have hfi : f ≫ i.openSet.ι = V.ι := X.homOfLE_ι hi
    have hgj : g ≫ j.openSet.ι = V.ι := X.homOfLE_ι hj
    have hiV : V ≤ (f ≫ i.openSet.ι).opensRange := by
      intro x hx
      change ∃ y : V.toScheme, (f ≫ i.openSet.ι) y = x
      exact ⟨⟨x, hx⟩, congrArg (fun k : V.toScheme ⟶ X => k ⟨x, hx⟩) hfi⟩
    have hjV : V ≤ (g ≫ j.openSet.ι).opensRange := by
      intro x hx
      change ∃ y : V.toScheme, (g ≫ j.openSet.ι) y = x
      exact ⟨⟨x, hx⟩, congrArg (fun k : V.toScheme ⟶ X => k ⟨x, hx⟩) hgj⟩
    have hiR : V ≤ i.openSet.ι.opensRange := by rwa [i.openSet.opensRange_ι]
    have hjR : V ≤ j.openSet.ι.opensRange := by rwa [j.openSet.opensRange_ι]
    have H : Local.LineBundleEndValues.localLineEndValue i.openSet.ι φ i.frame V hiR =
        Local.LineBundleEndValues.localLineEndValue j.openSet.ι φ j.frame V hjR :=
      (Local.LineBundleEndValues.localLineEndValue_comp f i.openSet.ι φ i.frame V hiV).symm.trans
      ((Local.LineBundleEndValues.localLineEndValue_congr (hfi.trans hgj.symm) φ
        (Local.TensorPowerValues.refinedPullbackFrame f i.openSet.ι i.frame) (Local.TensorPowerValues.refinedPullbackFrame g j.openSet.ι j.frame)
        V hiV hjV).trans
          (Local.LineBundleEndValues.localLineEndValue_comp g j.openSet.ι φ j.frame V hjV))
    exact (Local.LineBundleEndValues.localLineEndValue_restriction i.openSet.ι φ i.frame V hiR).trans
      (H.trans (Local.LineBundleEndValues.localLineEndValue_restriction j.openSet.ι φ j.frame V hjR).symm)

def Line.Bundles.LineBundle.endTransfer (L : Line.Bundles.LineBundle X) (φ : End L.sheaf) : End (Line.Bundles.structureModule X) :=
  (LineBundle.EndGluing.lineEndTransferData L φ).glue (LineBundle.EndGluing.lineEndFrameCover_covers L)

theorem Line.Bundles.LineBundle.endTransfer_restrict (L : Line.Bundles.LineBundle X) (φ : End L.sheaf)
    (i : LineBundle.EndGluing.LineEndFrameOpen L) :
    (Scheme.Modules.restrictFunctor i.openSet.ι).map (L.endTransfer φ) =
      OpenPullback.ModuleValues.pullbackModuleRestrictionMap i.openSet.ι (Local.LineBundleEndTransfer.localLineEndTransfer i.openSet.ι φ i.frame) :=
  (LineBundle.EndGluing.lineEndTransferData L φ).glue_restrict (LineBundle.EndGluing.lineEndFrameCover_covers L) i

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
