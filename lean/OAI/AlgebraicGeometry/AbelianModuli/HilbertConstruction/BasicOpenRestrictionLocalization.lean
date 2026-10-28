import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BasicOpenModuleRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.GlobalCoefficientLocalization

/-! # Basic Open Restriction Localization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BasicOpenRestrictionLocalization

noncomputable section

/-! On every affine open, the basic-open restriction adjunction localizes the actual section module. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent] (r : Γ(X, ⊤))

theorem basicOpenRestrictionMap_affine_isLocalized (U : X.affineOpens) :
    IsLocalizedModule.Away r ((BasicOpenModuleRestriction.basicOpenRestrictionMap M r).app (op U.1)).hom := by
  let a := ((BasicOpenModuleRestriction.basicOpenRestrictionMap M r).app (op U.1)).hom
  let e := (BasicOpenModuleRestriction.basicOpenRestrictionAppIso M r U.1).toLinearEquiv
  have ha : e.toLinearMap.comp a =
      ((Coefficient.ModulePresheaf.coefficientModulePresheaf (RingHom.id Γ(X, ⊤)) M).map
        (homOfLE (X.basicOpen_le (X.presheaf.map U.1.leTop.op r))).op).hom :=
    congrArg ModuleCat.Hom.hom (BasicOpenModuleRestriction.basicOpenRestrictionMap_app_iso M r U.1)
  have hloc : IsLocalizedModule.Away r (e.toLinearMap.comp a) :=
    ha.symm ▸ AffineOpen.GlobalCoefficientLocalization.affineOpen_globalCoefficientSection_isLocalized M U r
  let := hloc
  have hback := IsLocalizedModule.of_linearEquiv (Submonoid.powers r)
    (e.toLinearMap.comp a) e.symm
  have he : e.symm.toLinearMap.comp (e.toLinearMap.comp a) = a := by
    apply LinearMap.ext
    intro x
    exact e.symm_apply_apply (a x)
  rw [he] at hback
  exact hback

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BasicOpenRestrictionLocalization
