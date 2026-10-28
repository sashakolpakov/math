import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.FrameCoordinates
import OAI.RepresentationTheory.Theta.Geometric.FrameGlobalIsoRestriction

/-! # Line Frame Iso Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Actual local line-sheaf frames transport through a module
isomorphism without changing their literal regular transition units. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem LineFrameIsoTransport.nativeFrameTransitionTopUnit_precomp {X : Scheme.{0}} {M N : X.Modules}
    (q : N ≅ M) (e f : M ≅ HilbertConstruction.Line.Bundles.structureModule X) :
    RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionTopUnit (q ≪≫ e) (q ≪≫ f) = RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionTopUnit e f := by
  apply Units.ext
  rw [RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionTopUnit_value, RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionTopUnit_value]
  congr 1
  simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]

theorem LineFrameIsoTransport.nativeFrameTransitionUnit_precomp {X : Scheme.{0}} (M N : X.Modules) (U : X.Opens)
    (q : N.restrict U.ι ≅ M.restrict U.ι)
    (e f : M.restrict U.ι ≅ HilbertConstruction.Line.Bundles.structureModule U.toScheme) :
    RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit N U (q ≪≫ e) (q ≪≫ f) = RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit M U e f :=
  congrArg (Units.map U.topIso.hom.hom.toMonoidHom) (LineFrameIsoTransport.nativeFrameTransitionTopUnit_precomp q e f)

variable {X : Scheme.{0}} {M N : X.Modules}

def LineFrameAtlas.LocalLineFrame.precomp (s : LineFrameAtlas.LocalLineFrame M) (q : N ≅ M) : LineFrameAtlas.LocalLineFrame N :=
  ⟨s.domain, (Scheme.Modules.restrictFunctor s.domain.ι).mapIso q ≪≫ s.frame⟩

theorem LineFrameAtlas.LocalLineFrame.precomp_transition (s t : LineFrameAtlas.LocalLineFrame M) (q : N ≅ M)
    (U : X.Opens) (hs : U ≤ s.domain) (ht : U ≤ t.domain) :
    (s.precomp q).transition (t.precomp q) U hs ht = s.transition t U hs ht := by
  have h₁ := LineFrameAtlas.LocalLineFrame.transition_native N (s.precomp q) (t.precomp q) U hs ht
  have h₂ := congrArg₂ (RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit N U)
    (RepresentationTheory.Theta.Geometric.FrameGlobalIsoRestriction.restrictOpenFrame_globalIso q hs s.frame) (RepresentationTheory.Theta.Geometric.FrameGlobalIsoRestriction.restrictOpenFrame_globalIso q ht t.frame)
  have h₃ := LineFrameIsoTransport.nativeFrameTransitionUnit_precomp M N U ((Scheme.Modules.restrictFunctor U.ι).mapIso q)
    (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hs s.frame) (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization ht t.frame)
  exact h₁.trans (h₂.trans (h₃.trans (LineFrameAtlas.LocalLineFrame.transition_native M s t U hs ht).symm))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
