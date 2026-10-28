import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.FrameCoordinates

/-! # Line Frame Over Transitions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.LineFrameOverTransitions

noncomputable section

/-! The original local line-frame transition equation on the
native over-site, with both restricted frames retained explicitly. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem localLineFrame_over_transition {X : Scheme.{0}} {M : X.Modules}
    (s t : LineFrameAtlas.LocalLineFrame M) (W : X.Opens) (hs : W ≤ s.domain) (ht : W ≤ t.domain) :
    (SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M s.domain
      (SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso M s.domain s.frame) (Over.mk (homOfLE hs))).hom =
    (SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M t.domain
      (SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso M t.domain t.frame) (Over.mk (homOfLE ht))).hom ≫
        SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf W (s.transition t W hs ht).val := by
  let e := SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hs s.frame
  let g := SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization ht t.frame
  let u := RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit M W e g
  have ho := SheafCohomology.Projective.OverFrameScalarTransfer.overTrivializationOfRestrictIso_hom_eq_comp_scalar M W e g u.val
    (RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit_spec M W e g)
  have he := congrArg Iso.hom (SheafCohomology.Projective.OpenFrames.Scheme.Modules.overTrivializationOfRestrictOpenTrivialization hs s.frame)
  have hg := congrArg Iso.hom (SheafCohomology.Projective.OpenFrames.Scheme.Modules.overTrivializationOfRestrictOpenTrivialization ht t.frame)
  have h := he.symm.trans (ho.trans (congrArg (fun q => q ≫
    SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf W u.val) hg))
  exact h.trans (congrArg (fun v : Γ(X, W)ˣ =>
    (SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M t.domain
      (SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso M t.domain t.frame) (Over.mk (homOfLE ht))).hom ≫
        SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf W v.val)
          (LineFrameAtlas.LocalLineFrame.transition_native M s t W hs ht).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.LineFrameOverTransitions
