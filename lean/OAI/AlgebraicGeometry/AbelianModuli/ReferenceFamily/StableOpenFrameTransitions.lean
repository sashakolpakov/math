import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.SquareRestriction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.FrameTransitionCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UnitMapConjugation

/-! # Stable Open Frame Transitions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StableOpenFrameTransitions

noncomputable section

/-! On opens fixed by a scheme endomorphism, the actual pulled
frame transitions are obtained by its original local section-ring map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem stableOpenFrame_transition {X : Scheme.{0}} (q : X ⟶ X) (M : X.Modules) (U V W : X.Opens)
    (hU : W ≤ U) (hV : W ≤ V) (qU : U.toScheme ⟶ U.toScheme) (qV : V.toScheme ⟶ V.toScheme)
    (qW : W.toScheme ⟶ W.toScheme) (hqu : qU ≫ U.ι = U.ι ≫ q) (hqv : qV ≫ V.ι = V.ι ≫ q)
    (hqw : qW ≫ W.ι = W.ι ≫ q)
    (hcu : qW ≫ X.homOfLE hU = X.homOfLE hU ≫ qU)
    (hcv : qW ≫ X.homOfLE hV = X.homOfLE hV ≫ qV)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme)
    (d : (Scheme.Modules.pullback V.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule V.toScheme) :
    (Dual.TensorCechCoefficients.localFrameFromPullback U (RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame q U.ι U.ι qU hqu M e)).transition
      (Dual.TensorCechCoefficients.localFrameFromPullback V (RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame q V.ι V.ι qV hqv M d)) W hU hV =
    Units.map (W.topIso.hom.hom.comp (qW.appTop.hom.comp W.topIso.inv.hom)).toMonoidHom
      ((Dual.TensorCechCoefficients.localFrameFromPullback U e).transition (Dual.TensorCechCoefficients.localFrameFromPullback V d) W hU hV) := by
  have h₁ := Pullback.FrameTransitionCoordinates.localPullbackFrame_transition ((Scheme.Modules.pullback q).obj M) U V W hU hV
    (RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame q U.ι U.ι qU hqu M e) (RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame q V.ι V.ι qV hqv M d)
  have h₂ := congrArg₂ (fun a b => Units.map W.topIso.hom.hom.toMonoidHom (RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionTopUnit a b))
    (Pullback.SquareRestriction.pullbackSquareFrame_restrict q M hU hU qU qW hqu hqw hcu e)
    (Pullback.SquareRestriction.pullbackSquareFrame_restrict q M hV hV qV qW hqv hqw hcv d)
  have h₃ := congrArg (Units.map W.topIso.hom.hom.toMonoidHom)
    (Pullback.FrameTransitionCoordinates.pullbackSquareFrame_transition q W.ι W.ι qW hqw M (Dual.TensorCechCoefficients.restrictPullbackFrame M hU e) (Dual.TensorCechCoefficients.restrictPullbackFrame M hV d))
  have h₄ := UnitMapConjugation.units_map_conjugate W.topIso.commRingCatIsoToRingEquiv qW.appTop.hom
    (RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionTopUnit (Dual.TensorCechCoefficients.restrictPullbackFrame M hU e) (Dual.TensorCechCoefficients.restrictPullbackFrame M hV d))
  have h₅ := congrArg (Units.map (W.topIso.hom.hom.comp (qW.appTop.hom.comp W.topIso.inv.hom)).toMonoidHom)
    (Pullback.FrameTransitionCoordinates.localPullbackFrame_transition M U V W hU hV e d).symm
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StableOpenFrameTransitions
