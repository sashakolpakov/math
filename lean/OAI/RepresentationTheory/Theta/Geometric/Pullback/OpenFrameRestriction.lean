import OAI.RepresentationTheory.Theta.Geometric.NestedPullbackChartFrames

/-! # Open Frame Restriction -/

namespace OAI.RepresentationTheory.Theta.Geometric.Pullback.OpenFrameRestriction

noncomputable section

/-! Pulling back a native open frame commutes with its restriction to a
smaller algebraic open. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem pullbackOpenFrame_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    {U V : Y.Opens} (h : V ≤ U)
    (e : M.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme) :
    AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (f.preimage_mono h) (Algebraic.pullbackOpenFrame f M U e) =
      Algebraic.pullbackOpenFrame f M V (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization h e) := by
  let P := (Scheme.Modules.pullback f).obj M
  let r := (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).symm.app P
  let eU := (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app M ≪≫ e
  have hleft := OpenFramesFactored.restrictOpenFrame_as_factored P (f.preimage_mono h) (Algebraic.pullbackOpenFrame f M U e)
  have hright := OpenFramesFactored.pullbackOpenFrame_as_chart f M V (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization h e)
  have hU := OpenFramesFactored.pullbackOpenFrame_as_chart f M U e
  have hV := OpenFramesFactored.restrictOpenFrame_as_factored M h e
  have hmiddle := NestedPullbackChartFrames.pullbackChartFrame_nested f M h eU
  have hchangeLeft := congrArg
    (fun t => (Scheme.Modules.pullbackCongr (X.homOfLE_ι (f.preimage_mono h)).symm).app P ≪≫
      FactoredPullbackFrames.factoredPullbackFrame (X.homOfLE (f.preimage_mono h)) (f ⁻¹ᵁ U).ι t) hU
  have hchangeRight := congrArg (OpenFramesFactored.pullbackChartFrame f M V) hV
  have hh : r ≪≫ AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (f.preimage_mono h) (Algebraic.pullbackOpenFrame f M U e) =
      r ≪≫ Algebraic.pullbackOpenFrame f M V (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization h e) :=
    hleft.trans (hchangeLeft.trans (hmiddle.trans (hchangeRight.symm.trans hright.symm)))
  apply Iso.ext
  apply (cancel_epi r.hom).1
  exact congrArg Iso.hom hh

end

end OAI.RepresentationTheory.Theta.Geometric.Pullback.OpenFrameRestriction
