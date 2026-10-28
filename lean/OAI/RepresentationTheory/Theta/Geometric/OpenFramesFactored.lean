import OAI.RepresentationTheory.Theta.Geometric.Pullback.FrameEqualities
import OAI.RepresentationTheory.Theta.Geometric.Pullback.Algebraic

/-! # Open Frames Factored -/

namespace OAI.RepresentationTheory.Theta.Geometric.OpenFramesFactored

noncomputable section

/-! The actual open-scheme frames, expressed using canonical factored
pullbacks, so that nested-open compatibility reduces to composition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def pullbackChartFrame {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme) :
    (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback f).obj M) ≅
      AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj (f ⁻¹ᵁ U).toScheme :=
  (Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f).app M ≪≫
    (Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm).app M ≪≫
      FactoredPullbackFrames.factoredPullbackFrame (f ∣_ U) U.ι e

set_option backward.isDefEq.respectTransparency false in
theorem restrictOpenFrame_as_factored {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens}
    (h : V ≤ U) (e : M.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme) :
    (Scheme.Modules.restrictFunctorIsoPullback V.ι).symm.app M ≪≫
      AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization h e =
    (Scheme.Modules.pullbackCongr (X.homOfLE_ι h).symm).app M ≪≫
      FactoredPullbackFrames.factoredPullbackFrame (X.homOfLE h) U.ι
        ((Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app M ≪≫ e) := by
  rw [AlgebraicGeometry.SheafCohomology.Projective.OpenPullbackFrame.Scheme.Modules.restrictOpenTrivialization_eq_pullback]
  apply Iso.ext
  simp only [AlgebraicGeometry.SheafCohomology.Projective.OpenPullbackFrame.Scheme.Modules.restrictOpenTrivializationPullback, AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.restrictTrivialization,
    FactoredPullbackFrames.factoredPullbackFrame, Pullback.FrameComposition.pullbackGlobalFrame, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.app_inv, Iso.inv_hom_id_app_assoc]

set_option backward.isDefEq.respectTransparency false in
theorem pullbackOpenFrame_as_chart {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)
    (e : M.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme) :
    (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).symm.app ((Scheme.Modules.pullback f).obj M) ≪≫
      Pullback.Algebraic.pullbackOpenFrame f M U e =
    pullbackChartFrame f M U ((Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app M ≪≫ e) := by
  apply Iso.ext
  simp only [Pullback.Algebraic.pullbackOpenFrame, pullbackChartFrame, FactoredPullbackFrames.factoredPullbackFrame, Pullback.FrameComposition.pullbackGlobalFrame,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, Iso.inv_hom_id_app_assoc]

end

end OAI.RepresentationTheory.Theta.Geometric.OpenFramesFactored
