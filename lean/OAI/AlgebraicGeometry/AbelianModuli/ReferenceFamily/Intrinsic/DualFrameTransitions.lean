import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.TensorTransition
import OAI.AlgebraicGeometry.SheafCohomology.Projective.DualFrameTransition
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineBundleIsoFrames

/-! # Dual Frame Transitions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Actual dual line frames reverse the original regular transition
unit. Consequently simultaneous frames of two line bundles frame their
actual tensor difference with the quotient transition unit. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.SheafCohomology.Projective.DualFrameTransition

variable {X : Scheme.{0}} {M : X.Modules}

theorem LineFrameAtlas.LocalLineFrame.transition_self (s : LineFrameAtlas.LocalLineFrame M) (W : X.Opens) (h : W ≤ s.domain) :
    s.transition s W h h = 1 := by
  apply Units.ext
  exact (s.coordinates W h).apply_symm_apply 1

theorem LineFrameAtlas.LocalLineFrame.transition_reverse (s t : LineFrameAtlas.LocalLineFrame M) (W : X.Opens)
    (hs : W ≤ s.domain) (ht : W ≤ t.domain) :
    t.transition s W ht hs = (s.transition t W hs ht)⁻¹ :=
  ((inv_eq_iff_mul_eq_one).mpr
    ((s.transition_cocycle t s W hs ht hs).trans (s.transition_self W hs))).symm

def LineFrameAtlas.LocalLineFrame.dualFrame (s : LineFrameAtlas.LocalLineFrame M) : LineFrameAtlas.LocalLineFrame (SheafCohomology.Projective.Dual.Scheme.Modules.dualObj M) :=
  ⟨s.domain, SheafCohomology.Projective.Dual.Scheme.Modules.dualRestrictIsoOfRestrictIso M s.domain s.frame⟩

theorem LineFrameAtlas.LocalLineFrame.dualFrame_transition (s t : LineFrameAtlas.LocalLineFrame M) (W : X.Opens)
    (hs : W ≤ s.domain) (ht : W ≤ t.domain) :
    s.dualFrame.transition t.dualFrame W hs ht = t.transition s W ht hs := by
  let e := SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hs s.frame
  let g := SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization ht t.frame
  let u := RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit M W g e
  have ho := SheafCohomology.Projective.OverFrameScalarTransfer.overTrivializationOfRestrictIso_hom_eq_comp_scalar M W g e u.val
    (RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit_spec M W g e)
  have hg := congrArg Iso.hom (SheafCohomology.Projective.OpenFrames.Scheme.Modules.overTrivializationOfRestrictOpenTrivialization ht t.frame)
  have he := congrArg Iso.hom (SheafCohomology.Projective.OpenFrames.Scheme.Modules.overTrivializationOfRestrictOpenTrivialization hs s.frame)
  have ho' := hg.symm.trans (ho.trans (congrArg (fun q => q ≫
    SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf W u.val) he))
  have hd := SheafCohomology.Projective.DualFrameTransition.dualOpenOverlap_frameTransition M hs ht s.frame t.frame s.dualFrame.frame t.dualFrame.frame
    rfl rfl u.val ho'
  have hu := RepresentationTheory.Theta.Geometric.FrameTransitionUnitCoherence.frameTransitionUnit_unique (SheafCohomology.Projective.Dual.Scheme.Modules.dualObj M) W
    (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hs s.dualFrame.frame)
    (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization ht t.dualFrame.frame) u hd
  exact (LineFrameAtlas.LocalLineFrame.transition_native (SheafCohomology.Projective.Dual.Scheme.Modules.dualObj M) s.dualFrame t.dualFrame W hs ht).trans
    (hu.symm.trans (LineFrameAtlas.LocalLineFrame.transition_native M t s W ht hs).symm)

def Intrinsic.DualFrameTransitions.nativeDifferenceLocalFrame (L K : HilbertConstruction.Line.Bundles.LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ HilbertConstruction.Line.Bundles.structureModule U.toScheme)
    (f : K.sheaf.restrict U.ι ≅ HilbertConstruction.Line.Bundles.structureModule U.toScheme) :
    LineFrameAtlas.LocalLineFrame (LineBundleIsoFrames.lineBundleDifference L K).sheaf :=
  Intrinsic.TensorTransition.nativeTensorLocalFrame U f (SheafCohomology.Projective.Dual.Scheme.Modules.dualRestrictIsoOfRestrictIso L.sheaf U e)

theorem Intrinsic.DualFrameTransitions.nativeDifferenceLocalFrame_transition (L K : HilbertConstruction.Line.Bundles.LineBundle X) (U V W : X.Opens)
    (hU : W ≤ U) (hV : W ≤ V)
    (e : L.sheaf.restrict U.ι ≅ HilbertConstruction.Line.Bundles.structureModule U.toScheme)
    (e' : L.sheaf.restrict V.ι ≅ HilbertConstruction.Line.Bundles.structureModule V.toScheme)
    (f : K.sheaf.restrict U.ι ≅ HilbertConstruction.Line.Bundles.structureModule U.toScheme)
    (f' : K.sheaf.restrict V.ι ≅ HilbertConstruction.Line.Bundles.structureModule V.toScheme) :
    (Intrinsic.DualFrameTransitions.nativeDifferenceLocalFrame L K U e f).transition (Intrinsic.DualFrameTransitions.nativeDifferenceLocalFrame L K V e' f') W hU hV =
      (⟨U, f⟩ : LineFrameAtlas.LocalLineFrame K.sheaf).transition ⟨V, f'⟩ W hU hV /
        (⟨U, e⟩ : LineFrameAtlas.LocalLineFrame L.sheaf).transition ⟨V, e'⟩ W hU hV := by
  have h := Intrinsic.TensorTransition.nativeTensorLocalFrame_transition U V W hU hV f f'
    (SheafCohomology.Projective.Dual.Scheme.Modules.dualRestrictIsoOfRestrictIso L.sheaf U e)
    (SheafCohomology.Projective.Dual.Scheme.Modules.dualRestrictIsoOfRestrictIso L.sheaf V e')
  have hd := (LineFrameAtlas.LocalLineFrame.dualFrame_transition (⟨U, e⟩ : LineFrameAtlas.LocalLineFrame L.sheaf) ⟨V, e'⟩ W hU hV).trans
    (LineFrameAtlas.LocalLineFrame.transition_reverse (⟨U, e⟩ : LineFrameAtlas.LocalLineFrame L.sheaf) ⟨V, e'⟩ W hU hV)
  exact h.trans ((congrArg (fun u => (⟨U, f⟩ : LineFrameAtlas.LocalLineFrame K.sheaf).transition ⟨V, f'⟩ W hU hV * u) hd).trans
    (div_eq_mul_inv _ _).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
