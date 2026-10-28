import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EqualReductionOpenSquares
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SquareLineDifferenceFrames
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.PullbackDifference
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.ClassFromOpenFrames

/-! # Difference Open Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.DifferenceOpenFrames

noncomputable section

/-! The actual difference of two equally reduced line pullbacks is
computed on a common affine cover. Its original transition units reduce
to one, giving its native Picard H1 class without assumed normalized frames. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) {Y : Scheme.{0}}
    (f g : (LieRanks.dualNumberTest ℂ ⊗ X).left ⟶ Y)
    (h : (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ≫ f = (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ≫ g)
    (L : HilbertConstruction.Line.Bundles.LineBundle Y)

def dualDifferenceOpenFrame (s : LineFrameAtlas.LocalLineFrame L.sheaf) :
    LineFrameAtlas.LocalLineFrame (DualLine.PullbackDifference.dualLinePullbackDifference X f g L).sheaf :=
  SquareLineDifferenceFrames.squareLineDifferenceFrame f g L s (g ⁻¹ᵁ s.domain)
    (EqualReductionOpenSquares.equalDualReductionOpenMap X f g h s.domain) (g ∣_ s.domain)
    (EqualReductionOpenSquares.equalDualReductionOpenMap_square X f g h s.domain) (morphismRestrict_ι g s.domain)

theorem dualDifferenceOpenFrame_transition (s t : LineFrameAtlas.LocalLineFrame L.sheaf)
    (W : Y.Opens) (hs : W ≤ s.domain) (ht : W ≤ t.domain) :
    (dualDifferenceOpenFrame X f g h L s).transition (dualDifferenceOpenFrame X f g h L t)
      (g ⁻¹ᵁ W) (g.preimage_mono hs) (g.preimage_mono ht) =
    Open.UnitCoordinates.openUnitToRegular (g ⁻¹ᵁ W)
        (Units.map (EqualReductionOpenSquares.equalDualReductionOpenMap X f g h W).appTop.hom.toMonoidHom
          (Open.UnitCoordinates.regularUnitToOpen W (s.transition t W hs ht))) /
      Open.UnitCoordinates.openUnitToRegular (g ⁻¹ᵁ W) (Units.map (g ∣_ W).appTop.hom.toMonoidHom
        (Open.UnitCoordinates.regularUnitToOpen W (s.transition t W hs ht))) :=
  SquareLineDifferenceFrames.squareLineDifferenceFrame_transition f g L s t (g ⁻¹ᵁ s.domain) (g ⁻¹ᵁ t.domain) (g ⁻¹ᵁ W) W
    hs ht (g.preimage_mono hs) (g.preimage_mono ht)
    (EqualReductionOpenSquares.equalDualReductionOpenMap X f g h s.domain) (g ∣_ s.domain)
    (EqualReductionOpenSquares.equalDualReductionOpenMap X f g h t.domain) (g ∣_ t.domain)
    (EqualReductionOpenSquares.equalDualReductionOpenMap X f g h W) (g ∣_ W)
    (EqualReductionOpenSquares.equalDualReductionOpenMap_square X f g h s.domain) (EqualReductionOpenSquares.equalDualReductionOpenMap_square X f g h t.domain)
    (morphismRestrict_ι g s.domain) (morphismRestrict_ι g t.domain)
    (EqualReductionOpenSquares.equalDualReductionOpenMap_square X f g h W) (morphismRestrict_ι g W)

theorem dualDifferenceOpenFrame_transition_reduces (s t : LineFrameAtlas.LocalLineFrame L.sheaf)
    (W : Y.Opens) (hs : W ≤ s.domain) (ht : W ≤ t.domain) :
    Units.map ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left.app (g ⁻¹ᵁ W)).hom.toMonoidHom
      ((dualDifferenceOpenFrame X f g h L s).transition (dualDifferenceOpenFrame X f g h L t)
        (g ⁻¹ᵁ W) (g.preimage_mono hs) (g.preimage_mono ht)) = 1 := by
  rw [dualDifferenceOpenFrame_transition X f g h L s t W hs ht, map_div]
  have he := SquareLineDifferenceFrames.openSquare_equal_reduction (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left f g h W (g ⁻¹ᵁ W)
    (EqualReductionOpenSquares.equalDualReductionOpenMap X f g h W) (g ∣_ W)
    (EqualReductionOpenSquares.equalDualReductionOpenMap_square X f g h W) (morphismRestrict_ι g W)
  rw [Open.UnitPullbackReduction.openUnitToRegular_equal_reduction (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left (g ⁻¹ᵁ W)
    (EqualReductionOpenSquares.equalDualReductionOpenMap X f g h W) (g ∣_ W) he, div_self']

theorem dualDifferenceOpenFrames_cover {I : Type} (s : I → LineFrameAtlas.LocalLineFrame L.sheaf)
    (hs : iSup (fun i => (s i).domain) = ⊤) :
    iSup (fun i => (dualDifferenceOpenFrame X f g h L (s i)).domain) = ⊤ :=
  Local.LineFramePullback.localLineFrame_pullback_cover g s hs

variable [LocallyOfFiniteType X.hom] [IsReduced X.left]
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ X).left))]

theorem dualLinePullbackDifferenceClass_eq_openFrames [IsAffineHom g]
    {I : Type} (s : I → LineFrameAtlas.LocalLineFrame L.sheaf) (ha : ∀ i, IsAffineOpen (s i).domain)
    (hs : iSup (fun i => (s i).domain) = ⊤) :
    ∃ (hc : iSup (CechCoefficient.dualReducedCechCover X (fun i => g ⁻¹ᵁ (s i).domain)) = ⊤)
      (hn : UnitCechCoefficients.DualUnitCechNormalized X.left.sheaf.obj (CechCoefficient.dualReducedCechCover X (fun i => g ⁻¹ᵁ (s i).domain))
        (LineFrameDualCech.lineFrameDualCech X (fun i => dualDifferenceOpenFrame X f g h L (s i)) (fun i => (ha i).preimage g))),
      DualLine.PullbackDifference.dualLinePullbackDifferenceClass X f g h L =
        Regular.DualUnitClass.regularDualUnitClass X.left (CechCoefficient.dualReducedCechCover X (fun i => g ⁻¹ᵁ (s i).domain)) hc
          (LineFrameDualCech.lineFrameDualCech X (fun i => dualDifferenceOpenFrame X f g h L (s i)) (fun i => (ha i).preimage g)) hn
          (LineFrameDualCech.lineFrameDualCech_cocycle X (fun i => dualDifferenceOpenFrame X f g h L (s i)) (fun i => (ha i).preimage g)) := by
  obtain ⟨hc, hn, he⟩ := DualLine.ClassFromOpenFrames.dualLineDeformationClass_eq_openFrames X (DualLine.PullbackDifference.dualLinePullbackDifference X f g L)
    (DualLine.PullbackDifference.dualLinePullbackDifferenceFrame X f g h L) (fun i => dualDifferenceOpenFrame X f g h L (s i))
    (fun i => (ha i).preimage g) (dualDifferenceOpenFrames_cover X f g h L s hs)
    (fun i j => dualDifferenceOpenFrame_transition_reduces X f g h L (s i) (s j)
      ((s i).domain ⊓ (s j).domain) inf_le_left inf_le_right)
  exact ⟨hc, hn, (DualLine.ClassKernel.dualLineKernelCohomology_of_line X (DualLine.PullbackDifference.dualLinePullbackDifference X f g L)
    (DualLine.PullbackDifference.dualLinePullbackDifferenceFrame X f g h L)).trans he⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.DifferenceOpenFrames
