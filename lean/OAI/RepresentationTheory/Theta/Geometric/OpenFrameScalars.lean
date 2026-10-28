import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.TwistOverFrames

/-! # Open Frame Scalars -/

namespace OAI.RepresentationTheory.Theta.Geometric.OpenFrameScalars

noncomputable section

/-! Native frame scalar relations restrict as regular sections do. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem restrictOpenFrame_scalar {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens} (hVU : V ≤ U)
    (e g : M.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme) (r : Γ(X, U))
    (h : e.hom = g.hom ≫ AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection (U.topIso.inv r)) :
    (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hVU e).hom =
      (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hVU g).hom ≫ AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection
        (V.topIso.inv (X.presheaf.map (homOfLE hVU).op r)) := by
  let eOver := AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U e
  let gOver := AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U g
  have hOver := AlgebraicGeometry.SheafCohomology.Projective.OverFrameScalarTransfer.overTrivializationOfRestrictIso_hom_eq_comp_scalar M U e g r h
  have hRes := AlgebraicGeometry.SheafCohomology.Projective.OverFrameTransitions.restrictOverTrivialization_hom_eq_comp_scalar M hVU gOver eOver r hOver
  exact AlgebraicGeometry.SheafCohomology.Projective.OverScalarRestriction.restrictTrivializationOfOverIso_hom_eq_comp_scalar M V _ _
    (X.presheaf.map (homOfLE hVU).op r) hRes

end

end OAI.RepresentationTheory.Theta.Geometric.OpenFrameScalars
