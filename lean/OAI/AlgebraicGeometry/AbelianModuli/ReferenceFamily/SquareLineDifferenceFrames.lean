import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SquareFrameTransitionRecovery
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.DualFrameTransitions
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.UnitPullbackReduction

/-! # Square Line Difference Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SquareLineDifferenceFrames

noncomputable section

/-! The actual tensor difference of two line pullbacks has frames
on common open squares. Their transition is the quotient of the two
original pulled units, and it reduces to one when the maps agree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem openSquare_maps_restrict {X Y : Scheme.{0}} (f : X ⟶ Y)
    {U W : Y.Opens} {V Z : X.Opens} (hU : W ≤ U) (hV : Z ≤ V)
    (p : V.toScheme ⟶ U.toScheme) (q : Z.toScheme ⟶ W.toScheme)
    (hp : p ≫ U.ι = V.ι ≫ f) (hq : q ≫ W.ι = Z.ι ≫ f) :
    q ≫ Y.homOfLE hU = X.homOfLE hV ≫ p := by
  apply (cancel_mono U.ι).mp
  calc
    (q ≫ Y.homOfLE hU) ≫ U.ι = q ≫ W.ι := by rw [Category.assoc, Scheme.homOfLE_ι]
    _ = Z.ι ≫ f := hq
    _ = (X.homOfLE hV ≫ p) ≫ U.ι := by rw [Category.assoc, hp, ← Category.assoc, Scheme.homOfLE_ι]

theorem openSquare_equal_reduction {X Y Z : Scheme.{0}} (r : Z ⟶ X) (f g : X ⟶ Y)
    (h : r ≫ f = r ≫ g) (U : Y.Opens) (V : X.Opens)
    (p q : V.toScheme ⟶ U.toScheme)
    (hp : p ≫ U.ι = V.ι ≫ f) (hq : q ≫ U.ι = V.ι ≫ g) :
    (r ∣_ V) ≫ p = (r ∣_ V) ≫ q := by
  apply (cancel_mono U.ι).mp
  calc
    ((r ∣_ V) ≫ p) ≫ U.ι = ((r ∣_ V) ≫ V.ι) ≫ f := by rw [Category.assoc, hp, Category.assoc]
    _ = (r ⁻¹ᵁ V).ι ≫ (r ≫ f) := by rw [morphismRestrict_ι, Category.assoc]
    _ = (r ⁻¹ᵁ V).ι ≫ (r ≫ g) := congrArg (fun a => (r ⁻¹ᵁ V).ι ≫ a) h
    _ = ((r ∣_ V) ≫ V.ι) ≫ g := (Category.assoc (r ⁻¹ᵁ V).ι r g).symm.trans
      (congrArg (fun a => a ≫ g) (morphismRestrict_ι r V)).symm
    _ = ((r ∣_ V) ≫ q) ≫ U.ι := (Category.assoc (r ∣_ V) V.ι g).trans
      ((congrArg (fun a => (r ∣_ V) ≫ a) hq).symm.trans (Category.assoc (r ∣_ V) q U.ι).symm)

def squarePulledLocalLineFrame {X Y : Scheme.{0}} (f : X ⟶ Y) {M : Y.Modules}
    (s : LineFrameAtlas.LocalLineFrame M) (V : X.Opens) (p : V.toScheme ⟶ s.domain.toScheme)
    (hp : p ≫ s.domain.ι = V.ι ≫ f) : LineFrameAtlas.LocalLineFrame ((Scheme.Modules.pullback f).obj M) :=
  Dual.TensorCechCoefficients.localFrameFromPullback V (RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame f V.ι s.domain.ι p hp M s.pullbackFrame)

theorem squarePulledLocalLineFrame_transition {X Y : Scheme.{0}} (f : X ⟶ Y) {M : Y.Modules}
    (s t : LineFrameAtlas.LocalLineFrame M) (V V' W' : X.Opens) (W : Y.Opens)
    (hs : W ≤ s.domain) (ht : W ≤ t.domain) (hV : W' ≤ V) (hV' : W' ≤ V')
    (p : V.toScheme ⟶ s.domain.toScheme) (p' : V'.toScheme ⟶ t.domain.toScheme)
    (q : W'.toScheme ⟶ W.toScheme)
    (hp : p ≫ s.domain.ι = V.ι ≫ f) (hp' : p' ≫ t.domain.ι = V'.ι ≫ f)
    (hq : q ≫ W.ι = W'.ι ≫ f) :
    (squarePulledLocalLineFrame f s V p hp).transition
      (squarePulledLocalLineFrame f t V' p' hp') W' hV hV' =
    Open.UnitCoordinates.openUnitToRegular W' (Units.map q.appTop.hom.toMonoidHom
      (Open.UnitCoordinates.regularUnitToOpen W (s.transition t W hs ht))) := by
  have h := SquareFrameTransitionRecovery.squarePulledFrame_transition f M s.domain t.domain W V V' W' hs ht hV hV'
    p p' q hp hp' hq (openSquare_maps_restrict f hs hV p q hp hq)
    (openSquare_maps_restrict f ht hV' p' q hp' hq) s.pullbackFrame t.pullbackFrame
  exact h.trans (congrArg (fun u => Open.UnitCoordinates.openUnitToRegular W' (Units.map q.appTop.hom.toMonoidHom
    (Open.UnitCoordinates.regularUnitToOpen W u))) (LineFrameAtlas.LocalLineFrame.transition_congr s.fromPullbackFrame t.fromPullbackFrame W hs ht hs ht))

def squareLineDifferenceFrame {X Y : Scheme.{0}} (f g : X ⟶ Y) (L : HilbertConstruction.Line.Bundles.LineBundle Y)
    (s : LineFrameAtlas.LocalLineFrame L.sheaf) (V : X.Opens) (p q : V.toScheme ⟶ s.domain.toScheme)
    (hp : p ≫ s.domain.ι = V.ι ≫ f) (hq : q ≫ s.domain.ι = V.ι ≫ g) :
    LineFrameAtlas.LocalLineFrame (LineBundleIsoFrames.lineBundleDifference (L.pullback g) (L.pullback f)).sheaf :=
  Intrinsic.DualFrameTransitions.nativeDifferenceLocalFrame (L.pullback g) (L.pullback f) V
    (squarePulledLocalLineFrame g s V q hq).frame (squarePulledLocalLineFrame f s V p hp).frame

theorem squareLineDifferenceFrame_transition {X Y : Scheme.{0}} (f g : X ⟶ Y) (L : HilbertConstruction.Line.Bundles.LineBundle Y)
    (s t : LineFrameAtlas.LocalLineFrame L.sheaf) (V V' W' : X.Opens) (W : Y.Opens)
    (hs : W ≤ s.domain) (ht : W ≤ t.domain) (hV : W' ≤ V) (hV' : W' ≤ V')
    (p q : V.toScheme ⟶ s.domain.toScheme) (p' q' : V'.toScheme ⟶ t.domain.toScheme)
    (a b : W'.toScheme ⟶ W.toScheme)
    (hp : p ≫ s.domain.ι = V.ι ≫ f) (hp' : p' ≫ t.domain.ι = V'.ι ≫ f)
    (hq : q ≫ s.domain.ι = V.ι ≫ g) (hq' : q' ≫ t.domain.ι = V'.ι ≫ g)
    (ha : a ≫ W.ι = W'.ι ≫ f) (hb : b ≫ W.ι = W'.ι ≫ g) :
    (squareLineDifferenceFrame f g L s V p q hp hq).transition
      (squareLineDifferenceFrame f g L t V' p' q' hp' hq') W' hV hV' =
    Open.UnitCoordinates.openUnitToRegular W' (Units.map a.appTop.hom.toMonoidHom (Open.UnitCoordinates.regularUnitToOpen W (s.transition t W hs ht))) /
      Open.UnitCoordinates.openUnitToRegular W' (Units.map b.appTop.hom.toMonoidHom (Open.UnitCoordinates.regularUnitToOpen W (s.transition t W hs ht))) := by
  exact (Intrinsic.DualFrameTransitions.nativeDifferenceLocalFrame_transition (L.pullback g) (L.pullback f) V V' W' hV hV'
    (squarePulledLocalLineFrame g s V q hq).frame (squarePulledLocalLineFrame g t V' q' hq').frame
    (squarePulledLocalLineFrame f s V p hp).frame (squarePulledLocalLineFrame f t V' p' hp').frame).trans
      (congrArg₂ (· / ·) (squarePulledLocalLineFrame_transition f s t V V' W' W hs ht hV hV' p p' a hp hp' ha)
        (squarePulledLocalLineFrame_transition g s t V V' W' W hs ht hV hV' q q' b hq hq' hb))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SquareLineDifferenceFrames
