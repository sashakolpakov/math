import OAI.AlgebraicGeometry.PELModuli.IntegralModel.BaseSectionLocalization

/-! # Quasicoherent Pushforward -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.QuasicoherentPushforward

noncomputable section

/-! Quasi-compact separated direct images preserve quasicoherence.
The proof identifies actual section restrictions with localizations. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem isLocalized_of_linearEquiv_square
    {R : Type*} [CommRing R] (S : Submonoid R)
    {M N M' N' : Type*} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup M'] [AddCommGroup N']
    [Module R M] [Module R N] [Module R M'] [Module R N']
    (a : M →ₗ[R] N) (b : M' →ₗ[R] N')
    (eM : M ≃ₗ[R] M') (eN : N ≃ₗ[R] N')
    (h : eN.toLinearMap.comp a = b.comp eM.toLinearMap)
    [IsLocalizedModule S a] : IsLocalizedModule S b := by
  have : IsLocalizedModule S (a.comp eM.symm.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right S a eM.symm
  have ht := IsLocalizedModule.of_linearEquiv S (a.comp eM.symm.toLinearMap) eN
  have he : eN.toLinearMap.comp (a.comp eM.symm.toLinearMap) = b := by
    ext x
    have hx := LinearMap.congr_fun h (eM.symm x)
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, eM.apply_symm_apply] using hx
  rw [he] at ht
  exact ht

theorem quasicoherent_pushforward_affineTarget
    {X Y : Scheme.{u}} [X.IsSeparated] [CompactSpace X] [IsAffine Y]
    (f : X ⟶ Y) (M : X.Modules) [M.IsQuasicoherent] :
    ((pushforward f).obj M).IsQuasicoherent := by
  apply SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_of_isLocalized_basicOpen
  intro r
  let U := Y.basicOpen r
  let V := X.basicOpen (f.appTop r)
  let W := (pushforward f).obj M
  let a := (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf f M).map V.leTop.op
  let b := (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf (𝟙 Y) W).map U.leTop.op
  let eT := SheafCohomology.Projective.OrderedBaseCechPushforward.Scheme.Modules.baseModulePresheafPushforwardAppIso f (𝟙 Y) M ⊤
  let eV := (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf f M).mapIso (eqToIso (f.preimage_basicOpen_top r)).op ≪≫
    SheafCohomology.Projective.OrderedBaseCechPushforward.Scheme.Modules.baseModulePresheafPushforwardAppIso f (𝟙 Y) M U
  have hsquare : a ≫ eV.hom = eT.hom ≫ b := by
    apply ModuleCat.hom_ext
    ext x
    let x' : Γ(M, ⊤) := x
    change M.presheaf.map (eqToIso (f.preimage_basicOpen_top r)).op.hom
      (M.presheaf.map V.leTop.op x') =
      M.presheaf.map ((Opens.map f.base).map U.leTop).op x'
    rw [← M.presheaf.map_comp_apply]
    rfl
  have : IsLocalizedModule.Away r a.hom := BaseSectionLocalization.baseGlobalBasicOpen_isLocalized f M r
  exact isLocalized_of_linearEquiv_square (Submonoid.powers r) a.hom b.hom
    eT.toLinearEquiv eV.toLinearEquiv (congrArg ModuleCat.Hom.hom hsquare)

theorem quasicoherent_pushforward_of_quasiCompact_separated
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [IsSeparated f]
    (M : X.Modules) [M.IsQuasicoherent] :
    ((pushforward f).obj M).IsQuasicoherent := by
  have hlocal (U : Y.affineOpens) :
      (((pushforward f).obj M).over (U : Y.Opens)).IsQuasicoherent := by
    let V := f ⁻¹ᵁ U.1
    let fU := f ∣_ U.1
    let MU := M.restrict V.ι
    have : IsAffine U.1.toScheme := U.2
    have : V.toScheme.IsSeparated := ⟨by
      rw [← terminal.comp_from fU]
      infer_instance⟩
    have : CompactSpace V.toScheme := QuasiCompact.compactSpace_of_compactSpace fU
    have hPush : ((pushforward fU).obj MU).IsQuasicoherent :=
      quasicoherent_pushforward_affineTarget fU MU
    have hRestrict :
        (((pushforward f).obj M).restrict U.1.ι).IsQuasicoherent :=
      (SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent U.1).prop_of_iso
        (SheafCohomology.Projective.ModuleRestrictPushforward.Scheme.Modules.restrictPushforwardIsoOfIsPullbackApp f fU V.ι U.1.ι
          (isPullback_morphismRestrict f U.1) M).symm hPush
    let := hRestrict
    exact SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_over_of_restrict_of_isAffineOpen ((pushforward f).obj M) U.1
  have hcover : (_root_.Opens.grothendieckTopology Y).CoversTop
      (fun U : Y.affineOpens => (U : Y.Opens)) := by
    rw [Opens.coversTop_iff, IsOpenCover, iSup_affineOpens_eq_top Y]
  exact @SheafOfModules.IsQuasicoherent.of_coversTop
    _ _ _ _ _ _ _ _ ((pushforward f).obj M) _
      (fun U : Y.affineOpens => (U : Y.Opens)) hcover hlocal

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.QuasicoherentPushforward
