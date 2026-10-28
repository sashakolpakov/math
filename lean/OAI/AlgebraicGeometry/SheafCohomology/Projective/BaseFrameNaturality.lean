import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCechFactors
import OAI.AlgebraicGeometry.SheafCohomology.Projective.DualFrameTransition

/-! # Base Frame Naturality -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseFrameNaturality.MvPolynomial

noncomputable section

/-! Base-linear section coordinates respect a scalar change of restricted frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
universe u
open _root_.MvPolynomial

theorem baseModulePresheafFrame_naturality_scalar
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {U V : X.Opens} (h : V ≤ U)
    (e : M.restrict U.ι ≅ Invertible.Scheme.Modules.unitObj U.toScheme)
    (g : M.restrict V.ι ≅ Invertible.Scheme.Modules.unitObj V.toScheme)
    (s : Γ(X, V))
    (hg : DualFrameTransition.FrameTransition g
      (OpenFrames.Scheme.Modules.restrictOpenTrivialization h e)
      (UnitScalar.unitEndomorphismOfTopSection
        (OpenFrames.Scheme.Modules.openTopSection V s))) :
    (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).map (homOfLE h).op ≫
      (TwistCechFactors.MvPolynomial.baseModulePresheafObjIsoUnitOfOverIso π M V
        (Invertible.Scheme.Modules.overTrivializationOfRestrictIso M V g)).hom =
    (TwistCechFactors.MvPolynomial.baseModulePresheafObjIsoUnitOfOverIso π M U
      (Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U e)).hom ≫
      (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π (Invertible.Scheme.Modules.unitObj X)).map
        (homOfLE h).op ≫ TwistCechFactors.MvPolynomial.baseModulePresheafObjUnitScalar π V s := by
  have hOver := OverFrameScalarTransfer.overTrivializationOfRestrictIso_hom_eq_comp_scalar
    M V g (OpenFrames.Scheme.Modules.restrictOpenTrivialization h e) s hg
  rw [OpenFrames.Scheme.Modules.overTrivializationOfRestrictOpenTrivialization] at hOver
  rw [TwistCechFactors.MvPolynomial.baseModulePresheafObjIsoUnitOfOverIso_comp_scalar π M V _ _ s hOver,
    ← Category.assoc, TwistCechFactors.MvPolynomial.baseModulePresheafObjIsoUnitOfOverIso_naturality,
    Category.assoc]

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseFrameNaturality.MvPolynomial
