import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TensorCechCoefficients
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineFrameIsoTransport
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.IsoUnitPullback
import OAI.RepresentationTheory.Theta.Geometric.Pullback.SquareFrames

/-! # Frame Transition Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.FrameTransitionCoordinates

noncomputable section

/-! The actual transition unit can be computed in restricted
pullback frames, and square-pulled frames use the original section map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem localPullbackFrame_transition {X : Scheme.{0}} (M : X.Modules) (U V W : X.Opens)
    (hU : W ≤ U) (hV : W ≤ V)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme)
    (d : (Scheme.Modules.pullback V.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule V.toScheme) :
    (Dual.TensorCechCoefficients.localFrameFromPullback U e).transition (Dual.TensorCechCoefficients.localFrameFromPullback V d) W hU hV =
      Units.map W.topIso.hom.hom.toMonoidHom
        (RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionTopUnit (Dual.TensorCechCoefficients.restrictPullbackFrame M hU e) (Dual.TensorCechCoefficients.restrictPullbackFrame M hV d)) := by
  have h₁ := LineFrameAtlas.LocalLineFrame.transition_native M (Dual.TensorCechCoefficients.localFrameFromPullback U e) (Dual.TensorCechCoefficients.localFrameFromPullback V d) W hU hV
  have h₂ := congrArg₂ (RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit M W)
    (Dual.TensorCechCoefficients.restrictPullbackFrame_open M hU e).symm (Dual.TensorCechCoefficients.restrictPullbackFrame_open M hV d).symm
  have h₃ := congrArg (Units.map W.topIso.hom.hom.toMonoidHom)
    (LineFrameIsoTransport.nativeFrameTransitionTopUnit_precomp ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app M)
      (Dual.TensorCechCoefficients.restrictPullbackFrame M hU e) (Dual.TensorCechCoefficients.restrictPullbackFrame M hV d))
  exact h₁.trans (h₂.trans h₃)

theorem pullbackSquareFrame_transition {X Y U P : Scheme.{0}} (f : X ⟶ Y) (u : P ⟶ X)
    (a : U ⟶ Y) (p : P ⟶ U) (h : p ≫ a = u ≫ f) (M : Y.Modules)
    (e d : (Scheme.Modules.pullback a).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U) :
    RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionTopUnit (RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame f u a p h M e)
      (RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame f u a p h M d) =
        Units.map p.appTop.hom.toMonoidHom (RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionTopUnit e d) := by
  let R := (Scheme.Modules.pullbackComp u f).app M ≪≫
    (Scheme.Modules.pullbackCongr h.symm).app M ≪≫ ((Scheme.Modules.pullbackComp p a).app M).symm
  exact (LineFrameIsoTransport.nativeFrameTransitionTopUnit_precomp R (RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackGlobalFrame p e) (RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackGlobalFrame p d)).trans
    (RepresentationTheory.Theta.Geometric.Intrinsic.IsoUnitPullback.frameTransitionTopUnit_pullback p e d)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.FrameTransitionCoordinates
