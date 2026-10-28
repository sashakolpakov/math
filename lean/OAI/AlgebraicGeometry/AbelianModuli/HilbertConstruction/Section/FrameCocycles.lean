import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NaturalSheaf
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.LocalLinearFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.FrameRecognition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.FromOpenFrames

/-! # Frame Cocycles -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.FrameCocycles

noncomputable section

/-! Global sections whose nonvanishing opens cover recover their actual module sheaf from the regular-function ratios of their local frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X : Scheme.{u}} {ι : Type v} {M : X.Modules}

def sectionNaturalFrames (s : ι → (Line.Bundles.structureModule X ⟶ M)) :
    NaturalSheaf.NaturalSheafFrames (fun i => Ample.LineBundles.sectionNonvanishing (s i)) M where
  frame V i hi := LocalLinearFrames.sectionLocalFrameEquiv (s i) V hi
  restrict V W h i hi r := by
    have hv := LocalLinearFrames.sectionLocalFrameEquiv_apply (s i) V hi r
    have hw := LocalLinearFrames.sectionLocalFrameEquiv_apply (s i) W (h.trans hi) (X.presheaf.map (homOfLE h).op r)
    have hn := ConcreteCategory.congr_hom ((s i).mapPresheaf.naturality (homOfLE h).op) r
    exact (congrArg (M.presheaf.map (homOfLE h).op) hv).trans (hn.symm.trans hw.symm)

def sectionFrameTransitions (s : ι → (Line.Bundles.structureModule X ⟶ M)) :
    OpenFrame.Transitions.OpenFrameTransitions (fun i => Ample.LineBundles.sectionNonvanishing (s i)) :=
  (sectionNaturalFrames s).transitions

theorem sectionFrameTransitions_value (s : ι → (Line.Bundles.structureModule X ⟶ M))
    (V : X.Opens) (i j : ι) (hi : V ≤ Ample.LineBundles.sectionNonvanishing (s i)) (hj : V ≤ Ample.LineBundles.sectionNonvanishing (s j)) :
    ((sectionFrameTransitions s).value V i j hi hj).val =
      (LocalLinearFrames.sectionLocalFrameEquiv (s i) V hi).symm ((s j).app V (1 : Γ(X, V))) :=
  congrArg (LocalLinearFrames.sectionLocalFrameEquiv (s i) V hi).symm (LocalLinearFrames.sectionLocalFrameEquiv_apply (s j) V hj 1)

def sectionFrameBundleIso {κ : Type u} (s : κ → (Line.Bundles.structureModule X ⟶ M))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i)) :
    (LineBundle.FromOpenFrames.lineBundleFromOpenFrames (sectionFrameTransitions s) hs).sheaf ≅ M :=
  Sheaf.FrameRecognition.openFrameSheafRecognitionIso (sectionFrameTransitions s) (sectionNaturalFrames s).compatible hs

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.FrameCocycles
