import OAI.AlgebraicGeometry.SheafCohomology.Projective.FaithfullyFlatQuasicoherentIso

/-! # Quasicoherent Affine Pullback -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.QuasicoherentAffinePullback

noncomputable section

/-! Pullback along an affine scheme morphism preserves actual quasicoherent modules. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

theorem affine_pullback_quasicoherent [IsAffine X] [IsAffine Y]
    (M : Y.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pullback f).obj M).IsQuasicoherent := by
  let i := X.isoSpec.symm
  let j := Y.isoSpec.symm
  let G := Scheme.Modules.pullback j.hom
  let H := Scheme.Modules.pullback i.hom
  have : (G.obj M).IsQuasicoherent :=
    ObjectProperty.prop_of_iso _ ((Scheme.Modules.restrictFunctorIsoPullback j.hom).app M)
      (inferInstanceAs ((Scheme.Modules.restrictFunctor j.hom).obj M).IsQuasicoherent)
  have hp : ((Scheme.Modules.pullback (Spec.map f.appTop)).obj (G.obj M)).IsQuasicoherent :=
    Picard.PoincareBundle.Affine.QuasiCoherent.pullback_isQuasicoherent f.appTop (G.obj M)
  let α := Picard.PoincareBundle.IsoDescent.pullbackSquareIso f (Spec.map f.appTop) i j (Scheme.isoSpec_inv_naturality f)
  have hH : (H.obj ((Scheme.Modules.pullback f).obj M)).IsQuasicoherent :=
    ObjectProperty.prop_of_iso _ (α.app M) hp
  have hrestrict : (((Scheme.Modules.pullback f).obj M).restrict i.hom).IsQuasicoherent :=
    ObjectProperty.prop_of_iso _
      ((Scheme.Modules.restrictFunctorIsoPullback i.hom).app ((Scheme.Modules.pullback f).obj M)).symm hH
  exact (Quasicoherent.Scheme.Modules.isQuasicoherent_restrictFunctor_iff i).mp hrestrict

theorem quasicoherent_pullback_of_isAffineHom [IsAffineHom f]
    (M : Y.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pullback f).obj M).IsQuasicoherent := by
  let P := (Scheme.Modules.pullback f).obj M
  have hlocal (U : Y.affineOpens) : (P.over (f ⁻¹ᵁ U.1)).IsQuasicoherent := by
    have : IsAffine U.1.toScheme := U.2
    have : IsAffine (f ⁻¹ᵁ U.1).toScheme := U.2.preimage f
    have hq : ((Scheme.Modules.pullback (f ∣_ U.1)).obj
        ((Scheme.Modules.restrictFunctor U.1.ι).obj M)).IsQuasicoherent :=
      affine_pullback_quasicoherent (f ∣_ U.1) _
    have : (P.restrict (f ⁻¹ᵁ U.1).ι).IsQuasicoherent :=
      ObjectProperty.prop_of_iso _ ((Picard.PoincareBundle.Open.BaseChange.pullbackRestrictIso f U.1).app M).symm hq
    exact Quasicoherent.Scheme.Modules.isQuasicoherent_over_of_restrict_of_isAffineOpen P
      (f ⁻¹ᵁ U.1)
  have hcover : (Opens.grothendieckTopology X).CoversTop
      (fun U : Y.affineOpens => f ⁻¹ᵁ U.1) := by
    rw [Opens.coversTop_iff, IsOpenCover, ← f.preimage_iSup, iSup_affineOpens_eq_top, f.preimage_top]
  exact @SheafOfModules.IsQuasicoherent.of_coversTop _ _ _ _ _ _ _ _ P _
    (fun U : Y.affineOpens => f ⁻¹ᵁ U.1) hcover hlocal

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.QuasicoherentAffinePullback
