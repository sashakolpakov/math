import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReducedFrame
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineFrameIsoTransport

/-! # Frame Iso Transitions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.FrameIsoTransitions

noncomputable section

/-! Conversion of pullback frames to restriction frames preserves
isomorphism invariance of their actual transition units. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem pullbackLocalFrame_precomp_transition {X : Scheme.{0}} {M N : X.Modules}
    (q : N ≅ M) (U V W : X.Opens) (hU : W ≤ U) (hV : W ≤ V)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ HilbertConstruction.Line.Bundles.structureModule U.toScheme)
    (f : (Scheme.Modules.pullback V.ι).obj M ≅ HilbertConstruction.Line.Bundles.structureModule V.toScheme) :
    (⟨U, (Scheme.Modules.restrictFunctorIsoPullback U.ι).app N ≪≫
      (Scheme.Modules.pullback U.ι).mapIso q ≪≫ e⟩ : LineFrameAtlas.LocalLineFrame N).transition
      ⟨V, (Scheme.Modules.restrictFunctorIsoPullback V.ι).app N ≪≫
        (Scheme.Modules.pullback V.ι).mapIso q ≪≫ f⟩ W hU hV =
    (⟨U, (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M ≪≫ e⟩ : LineFrameAtlas.LocalLineFrame M).transition
      ⟨V, (Scheme.Modules.restrictFunctorIsoPullback V.ι).app M ≪≫ f⟩ W hU hV := by
  have h := congrArg₂
    (fun (ea : N.restrict U.ι ≅ HilbertConstruction.Line.Bundles.structureModule U.toScheme)
      (eb : N.restrict V.ι ≅ HilbertConstruction.Line.Bundles.structureModule V.toScheme) =>
        (⟨U, ea⟩ : LineFrameAtlas.LocalLineFrame N).transition ⟨V, eb⟩ W hU hV)
    (ReducedFrame.transportedFrame_precomp (Scheme.Modules.restrictFunctorIsoPullback U.ι) q e)
    (ReducedFrame.transportedFrame_precomp (Scheme.Modules.restrictFunctorIsoPullback V.ι) q f)
  exact h.trans (LineFrameAtlas.LocalLineFrame.precomp_transition
    ⟨U, (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M ≪≫ e⟩
    ⟨V, (Scheme.Modules.restrictFunctorIsoPullback V.ι).app M ≪≫ f⟩ q W hU hV)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.FrameIsoTransitions
