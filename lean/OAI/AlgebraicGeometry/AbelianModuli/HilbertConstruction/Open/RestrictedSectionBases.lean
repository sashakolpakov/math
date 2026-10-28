import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections

/-! # Restricted Section Bases -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.RestrictedSectionBases

noncomputable section

/-! A basis of sections on an open transfers to global sections of the actually restricted sheaf, with the correct open-subscheme coefficient ring. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)

def moduleRestrictTopIso : Γ(M.restrict U.ι, ⊤) ≅ Γ(M, U) :=
  M.restrictAppIso U.ι ⊤ ≪≫ M.presheaf.mapIso (eqToIso U.ι_image_top.symm).op

theorem moduleRestrictTopIso_smul (r : Γ(U.toScheme, ⊤)) (x : Γ(M.restrict U.ι, ⊤)) :
    (moduleRestrictTopIso M U).hom (r • x) =
      U.topIso.hom r • (moduleRestrictTopIso M U).hom x := by
  change M.presheaf.map (eqToHom U.ι_image_top.symm).op
      ((M.restrictAppIso U.ι ⊤).hom (r • x)) = _
  rw [Scheme.Modules.smul_restrictAppIso_hom_apply, Scheme.Opens.ι_appIso]
  exact M.map_smul (eqToHom U.ι_image_top.symm) r ((M.restrictAppIso U.ι ⊤).hom x)

def moduleRestrictTopBasisEquiv (e : Γ(M, U) ≃ₗ[Γ(X, U)] Γ(X, U)) :
    Γ(M.restrict U.ι, ⊤) ≃ₗ[Γ(U.toScheme, ⊤)] Γ(U.toScheme, ⊤) where
  __ := ((moduleRestrictTopIso M U).addCommGroupIsoToAddEquiv.trans e.toAddEquiv).trans
    U.topIso.commRingCatIsoToRingEquiv.symm.toAddEquiv
  map_smul' r x := by
    change U.topIso.inv (e ((moduleRestrictTopIso M U).hom (r • x))) =
      r • U.topIso.inv (e ((moduleRestrictTopIso M U).hom x))
    rw [moduleRestrictTopIso_smul, map_smul]
    change U.topIso.inv (U.topIso.hom r * e ((moduleRestrictTopIso M U).hom x)) = _
    rw [map_mul]
    exact congrArg (fun z => z * U.topIso.inv (e ((moduleRestrictTopIso M U).hom x)))
      (ConcreteCategory.congr_hom U.topIso.hom_inv_id r)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.RestrictedSectionBases
