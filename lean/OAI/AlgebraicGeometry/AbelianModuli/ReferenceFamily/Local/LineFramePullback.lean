import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.FrameTransitionPullback
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.FrameCoordinates
import OAI.RepresentationTheory.Theta.Geometric.Pullback.OpenFrameRestriction

/-! # Line Frame Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Actual local line frames pull back to the inverse-image cover.
Their transition units are the original structure-sheaf pullbacks,
including for a nonflat reduction morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Scheme.{0}} {M : Y.Modules}

def LineFrameAtlas.LocalLineFrame.pullbackBy (f : X ⟶ Y) (s : LineFrameAtlas.LocalLineFrame M) :
    LineFrameAtlas.LocalLineFrame ((Scheme.Modules.pullback f).obj M) :=
  ⟨f ⁻¹ᵁ s.domain, RepresentationTheory.Theta.Geometric.Pullback.Algebraic.pullbackOpenFrame f M s.domain s.frame⟩

theorem LineFrameAtlas.LocalLineFrame.pullbackBy_transition (f : X ⟶ Y) (s t : LineFrameAtlas.LocalLineFrame M)
    (W : Y.Opens) (hs : W ≤ s.domain) (ht : W ≤ t.domain) :
    (s.pullbackBy f).transition (t.pullbackBy f) (f ⁻¹ᵁ W) (f.preimage_mono hs) (f.preimage_mono ht) =
      Units.map (f.app W).hom.toMonoidHom (s.transition t W hs ht) := by
  have h₀ := LineFrameAtlas.LocalLineFrame.transition_native ((Scheme.Modules.pullback f).obj M)
    (s.pullbackBy f) (t.pullbackBy f) (f ⁻¹ᵁ W) (f.preimage_mono hs) (f.preimage_mono ht)
  have h₁ := congrArg₂ (RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ W))
    (RepresentationTheory.Theta.Geometric.Pullback.OpenFrameRestriction.pullbackOpenFrame_restrict f M hs s.frame) (RepresentationTheory.Theta.Geometric.Pullback.OpenFrameRestriction.pullbackOpenFrame_restrict f M ht t.frame)
  have h₂ := Open.FrameTransitionPullback.nativeOpenFrameTransition_pullback f M W
    (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hs s.frame) (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization ht t.frame)
  have h₃ := congrArg (Units.map (f.app W).hom.toMonoidHom)
    (LineFrameAtlas.LocalLineFrame.transition_native M s t W hs ht).symm
  exact h₀.trans (h₁.trans (h₂.symm.trans h₃))

theorem Local.LineFramePullback.localLineFrame_pullback_cover (f : X ⟶ Y) {I : Type} (s : I → LineFrameAtlas.LocalLineFrame M)
    (hs : iSup (fun i => (s i).domain) = ⊤) :
    iSup (fun i => ((s i).pullbackBy f).domain) = ⊤ := by
  apply top_unique
  intro x _
  have hx : f x ∈ iSup (fun i => (s i).domain) := by rw [hs]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
