import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCechFactors
import OAI.AlgebraicGeometry.SheafCohomology.Projective.RankOneMapCoordinates

/-! # Frame Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.FrameEvaluation

noncomputable section

/-! Evaluating a native base-linear frame agrees with the corresponding
over-site frame, including after restriction to a smaller open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.AlgebraicGeometry.SheafCohomology.Projective.RankOneMapCoordinates _root_.MvPolynomial

universe u

theorem baseIso_apply {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (x : Γ(M, U)) :
    (AlgebraicGeometry.SheafCohomology.Projective.TwistCechFactors.MvPolynomial.baseModulePresheafObjIsoUnitOfOverIso π M U e).hom x =
      (AlgebraicGeometry.SheafCohomology.Projective.RankOneMapCoordinates.overFrameSectionEquiv M U e).symm x := rfl

theorem restriction_apply {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {U V : X.Opens} (h : V ≤ U) (e : M.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme)
    (x : Γ(M, V)) :
    (AlgebraicGeometry.SheafCohomology.Projective.TwistCechFactors.MvPolynomial.baseModulePresheafObjIsoUnitOfOverIso π M V
      (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso M V
        (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization h e))).hom x =
      (AlgebraicGeometry.SheafCohomology.Projective.RankOneMapCoordinates.overFrameSectionEquiv M V
        (AlgebraicGeometry.SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M U
          (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U e) (Over.mk (homOfLE h)))).symm x := by
  exact (baseIso_apply π M V _ x).trans
    (congrArg (fun q => (AlgebraicGeometry.SheafCohomology.Projective.RankOneMapCoordinates.overFrameSectionEquiv M V q).symm x)
      (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.overTrivializationOfRestrictOpenTrivialization h e))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.FrameEvaluation
