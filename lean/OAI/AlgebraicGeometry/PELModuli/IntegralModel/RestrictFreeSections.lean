import OAI.AlgebraicGeometry.SheafCohomology.Projective.CanonicalAffineFrame

/-! # Restrict Free Sections -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.RestrictFreeSections

noncomputable section

/-! Freeness of sections over an open is preserved by the actual
top-section comparison for restriction, including its native ring action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.SheafCohomology.Projective.CanonicalAffineFrame

universe u

theorem restrict_globalSections_free
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    [Module.Free Γ(X, U) Γ(M, U)] :
    Module.Free Γ(U.toScheme, ⊤) Γ(M.restrict U.ι, ⊤) := by
  let eR := U.topIso.commRingCatIsoToRingEquiv
  let : RingHomInvPair eR.toRingHom eR.symm.toRingHom := RingHomInvPair.of_ringEquiv eR
  let : RingHomInvPair eR.symm.toRingHom eR.toRingHom := RingHomInvPair.of_ringEquiv eR.symm
  let l : Γ(M.restrict U.ι, ⊤) →ₛₗ[eR.toRingHom] Γ(M, U) :=
    { toFun := (SheafCohomology.Projective.CanonicalAffineFrame.restrictionTopIso M U).hom
      map_add' := (SheafCohomology.Projective.CanonicalAffineFrame.restrictionTopIso M U).hom.hom.map_add
      map_smul' := SheafCohomology.Projective.CanonicalAffineFrame.restrictionTopIso_smul M U }
  let e := LinearEquiv.ofBijective l (ConcreteCategory.bijective_of_isIso (SheafCohomology.Projective.CanonicalAffineFrame.restrictionTopIso M U).hom)
  exact Module.Free.of_equiv e.symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.RestrictFreeSections
