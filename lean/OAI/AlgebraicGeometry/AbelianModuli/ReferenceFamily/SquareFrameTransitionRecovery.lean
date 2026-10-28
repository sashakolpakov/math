import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.SquareRestriction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.FrameTransitionCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.UnitCoordinates

/-! # Square Frame Transition Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Frame transitions on arbitrary commuting open squares are the
actual pullbacks of the original regular units. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem SquareFrameTransitionRecovery.squarePulledFrame_transition {X Y : Scheme.{0}} (f : X ⟶ Y) (M : Y.Modules)
    (U V W : Y.Opens) (U' V' W' : X.Opens)
    (hU : W ≤ U) (hV : W ≤ V) (hU' : W' ≤ U') (hV' : W' ≤ V')
    (pU : U'.toScheme ⟶ U.toScheme) (pV : V'.toScheme ⟶ V.toScheme)
    (pW : W'.toScheme ⟶ W.toScheme)
    (hpU : pU ≫ U.ι = U'.ι ≫ f) (hpV : pV ≫ V.ι = V'.ι ≫ f)
    (hpW : pW ≫ W.ι = W'.ι ≫ f)
    (hcU : pW ≫ Y.homOfLE hU = X.homOfLE hU' ≫ pU)
    (hcV : pW ≫ Y.homOfLE hV = X.homOfLE hV' ≫ pV)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme)
    (d : (Scheme.Modules.pullback V.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule V.toScheme) :
    (Dual.TensorCechCoefficients.localFrameFromPullback U' (RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame f U'.ι U.ι pU hpU M e)).transition
      (Dual.TensorCechCoefficients.localFrameFromPullback V' (RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame f V'.ι V.ι pV hpV M d)) W' hU' hV' =
      Open.UnitCoordinates.openUnitToRegular W' (Units.map pW.appTop.hom.toMonoidHom
        (Open.UnitCoordinates.regularUnitToOpen W ((Dual.TensorCechCoefficients.localFrameFromPullback U e).transition (Dual.TensorCechCoefficients.localFrameFromPullback V d) W hU hV))) := by
  have h₁ := Pullback.FrameTransitionCoordinates.localPullbackFrame_transition ((Scheme.Modules.pullback f).obj M) U' V' W' hU' hV'
    (RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame f U'.ι U.ι pU hpU M e) (RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame f V'.ι V.ι pV hpV M d)
  have h₂ := congrArg₂ (fun a b => Open.UnitCoordinates.openUnitToRegular W' (RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionTopUnit a b))
    (Pullback.SquareRestriction.pullbackSquareFrame_restrict f M hU hU' pU pW hpU hpW hcU e)
    (Pullback.SquareRestriction.pullbackSquareFrame_restrict f M hV hV' pV pW hpV hpW hcV d)
  have h₃ := congrArg (Open.UnitCoordinates.openUnitToRegular W')
    (Pullback.FrameTransitionCoordinates.pullbackSquareFrame_transition f W'.ι W.ι pW hpW M
      (Dual.TensorCechCoefficients.restrictPullbackFrame M hU e) (Dual.TensorCechCoefficients.restrictPullbackFrame M hV d))
  have h₄ := (congrArg (Open.UnitCoordinates.regularUnitToOpen W) (Pullback.FrameTransitionCoordinates.localPullbackFrame_transition M U V W hU hV e d)).trans
    (Open.UnitCoordinates.regularUnitToOpen_toRegular W (RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionTopUnit (Dual.TensorCechCoefficients.restrictPullbackFrame M hU e) (Dual.TensorCechCoefficients.restrictPullbackFrame M hV d)))
  exact h₁.trans (h₂.trans (h₃.trans
    (congrArg (fun a => Open.UnitCoordinates.openUnitToRegular W' (Units.map pW.appTop.hom.toMonoidHom a)) h₄.symm)))

def LineFrameAtlas.LocalLineFrame.pullbackFrame {X : Scheme.{0}} {M : X.Modules} (s : LineFrameAtlas.LocalLineFrame M) :
    (Scheme.Modules.pullback s.domain.ι).obj M ≅ HilbertConstruction.Line.Bundles.structureModule s.domain.toScheme :=
  (Scheme.Modules.restrictFunctorIsoPullback s.domain.ι).symm.app M ≪≫ s.frame

theorem LineFrameAtlas.LocalLineFrame.fromPullbackFrame {X : Scheme.{0}} {M : X.Modules} (s : LineFrameAtlas.LocalLineFrame M) :
    Dual.TensorCechCoefficients.localFrameFromPullback s.domain s.pullbackFrame = s := by
  cases s with
  | mk U e =>
    exact congrArg (fun frame => (⟨U, frame⟩ : LineFrameAtlas.LocalLineFrame M))
      (Iso.self_symm_id_assoc ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M) e)

theorem LineFrameAtlas.LocalLineFrame.transition_congr {X : Scheme.{0}} {M : X.Modules}
    {s s' t t' : LineFrameAtlas.LocalLineFrame M} (hs : s = s') (ht : t = t')
    (W : X.Opens) (ha : W ≤ s.domain) (hb : W ≤ t.domain)
    (ha' : W ≤ s'.domain) (hb' : W ≤ t'.domain) :
    s.transition t W ha hb = s'.transition t' W ha' hb' := by
  cases hs
  cases ht
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
