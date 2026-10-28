import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.FrameCoordinates

/-! # Restricted Frame Transition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RestrictedFrameTransition

noncomputable section

/-! The transition of two restricted algebraic frames is the original
regular unit on their common open, with all restriction maps explicit. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem restrictedFrame_transition {X : Scheme} {M : X.Modules}
    (r s : LineFrameAtlas.LocalLineFrame M) (U V : X.Opens) (hr : U ≤ r.domain) (hs : V ≤ s.domain) :
    (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (show U ⊓ V ≤ U from inf_le_left)
      (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hr r.frame)).hom =
    (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (show U ⊓ V ≤ V from inf_le_right)
      (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hs s.frame)).hom ≫
        SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection ((U ⊓ V).topIso.inv
          (r.transition s (U ⊓ V) (inf_le_left.trans hr) (inf_le_right.trans hs) : Γ(X, U ⊓ V))) := by
  let e := SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (show U ⊓ V ≤ r.domain from inf_le_left.trans hr) r.frame
  let f := SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (show U ⊓ V ≤ s.domain from inf_le_right.trans hs) s.frame
  have hl := congrArg Iso.hom
    (SheafCohomology.Projective.OpenFrameTransitivity.Scheme.Modules.restrictOpenTrivialization_comp hr (show U ⊓ V ≤ U from inf_le_left) r.frame)
  have hh := congrArg Iso.hom
    (SheafCohomology.Projective.OpenFrameTransitivity.Scheme.Modules.restrictOpenTrivialization_comp hs (show U ⊓ V ≤ V from inf_le_right) s.frame)
  have he := RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit_spec M (U ⊓ V) e f
  have hu := LineFrameAtlas.LocalLineFrame.transition_native M r s (U ⊓ V) (inf_le_left.trans hr) (inf_le_right.trans hs)
  have hc := congrArg (fun u : Γ(X, U ⊓ V)ˣ => f.hom ≫
    SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection ((U ⊓ V).topIso.inv (u : Γ(X, U ⊓ V)))) hu.symm
  exact hl.trans (he.trans (hc.trans (congrArg (fun h => h ≫
    SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection ((U ⊓ V).topIso.inv
      (r.transition s (U ⊓ V) (inf_le_left.trans hr) (inf_le_right.trans hs) : Γ(X, U ⊓ V)))) hh.symm)))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RestrictedFrameTransition
