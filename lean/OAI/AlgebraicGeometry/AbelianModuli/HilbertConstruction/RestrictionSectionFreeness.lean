import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RestrictionSectionFiniteness

/-! # Restriction Section Freeness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RestrictionSectionFreeness

noncomputable section

/-! Freeness survives the actual native scalar comparison between an open and its restricted scheme. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules
universe u

theorem restrict_globalSections_free
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    [Module.Free Γ(X, U) Γ(M, U)] :
    Module.Free Γ(U.toScheme, ⊤) Γ(M.restrict U.ι, ⊤) := by
  let eR' := U.ι.appIso (⊤ : U.toScheme.Opens)
  let eR := eR'.commRingCatIsoToRingEquiv.symm
  let : RingHomInvPair eR.toRingHom eR.symm.toRingHom := RingHomInvPair.of_ringEquiv eR
  let : RingHomInvPair eR.symm.toRingHom eR.toRingHom := RingHomInvPair.of_ringEquiv eR.symm
  let eM' := M.restrictAppIso U.ι ⊤
  let l : Γ(M.restrict U.ι, ⊤) →ₛₗ[eR.toRingHom]
      Γ(M, U.ι ''ᵁ (⊤ : U.toScheme.Opens)) :=
    { toFun := eM'.hom
      map_add' := eM'.hom.hom.map_add
      map_smul' := smul_restrictAppIso_hom_apply U.ι M ⊤ }
  let e := LinearEquiv.ofBijective l (ConcreteCategory.bijective_of_isIso eM'.hom)
  have : Module.Free Γ(X, U.ι ''ᵁ (⊤ : U.toScheme.Opens))
      Γ(M, U.ι ''ᵁ (⊤ : U.toScheme.Opens)) := by
    rw [U.ι_image_top]
    infer_instance
  exact Module.Free.of_equiv e.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RestrictionSectionFreeness
