import OAI.AlgebraicGeometry.SheafCohomology.Projective.IdealModule

/-! # Canonical Affine Frame -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.CanonicalAffineFrame

noncomputable section

/-! Canonical affine frames with a prescribed generator on the ambient open. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
universe u

variable {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)

def restrictionTopIso : Γ(M.restrict U.ι, (⊤ : U.toScheme.Opens)) ≅ Γ(M, U) :=
  M.restrictAppIso U.ι ⊤ ≪≫ M.presheaf.mapIso (eqToIso U.ι_image_top.symm).op

theorem restrictionTopIso_smul (a : Γ(U.toScheme, ⊤))
    (x : Γ(M.restrict U.ι, (⊤ : U.toScheme.Opens))) :
    (restrictionTopIso M U).hom (a • x) =
      U.topIso.hom a • (restrictionTopIso M U).hom x := by
  change M.presheaf.map (eqToIso U.ι_image_top.symm).op.hom
      ((M.restrictAppIso U.ι ⊤).hom (a • x)) = _
  rw [Scheme.Modules.smul_restrictAppIso_hom_apply]
  change M.presheaf.map (eqToHom U.ι_image_top.symm).op
    ((U.ι.appIso ⊤).inv a • (M.restrictAppIso U.ι ⊤).hom x) = _
  rw [M.map_smul]
  rw [Scheme.Opens.topIso_hom, Scheme.Opens.ι_appIso]
  rfl

/-- The section on the open is the chosen image of one. -/
def openGeneratorHom (s : Γ(M, U)) :
    Invertible.Scheme.Modules.unitObj U.toScheme ⟶ M.restrict U.ι :=
  AffineRankOne.globalGeneratorHom (M.restrict U.ι) ((restrictionTopIso M U).inv s)

theorem openGeneratorHom_top (s : Γ(M, U)) (a : Γ(U.toScheme, ⊤)) :
    (restrictionTopIso M U).hom ((openGeneratorHom M U s).val.app (op ⊤) a) =
      U.topIso.hom a • s := by
  change (restrictionTopIso M U).hom
    ((AffineRankOne.globalGeneratorHom (M.restrict U.ι) _).val.app (op ⊤) a) = _
  rw [AffineRankOne.globalGeneratorHom_top, restrictionTopIso_smul, Iso.inv_hom_id_apply]

theorem openGeneratorHom_isIso [M.IsQuasicoherent] (hU : IsAffineOpen U)
    (s : Γ(M, U)) (hs : Function.Bijective (fun a : Γ(X, U) => a • s)) :
    IsIso (openGeneratorHom M U s) := by
  have : IsAffine U.toScheme := hU
  have : (Invertible.Scheme.Modules.unitObj U.toScheme).IsQuasicoherent :=
    InvertibleFinitePresentation.invertible_quasicoherent Invertible.Scheme.Modules.isInvertible_unit
  apply Quasicoherent.Scheme.Modules.isIso_of_isQuasicoherent_of_isIso_app_top
  rw [ConcreteCategory.isIso_iff_bijective]
  have hTop := ConcreteCategory.bijective_of_isIso (restrictionTopIso M U).hom
  have hRing := ConcreteCategory.bijective_of_isIso U.topIso.hom
  constructor
  · intro a b hab
    apply hRing.1
    apply hs.1
    have h := congrArg (restrictionTopIso M U).hom hab
    simpa only [openGeneratorHom_top] using h
  · intro y
    obtain ⟨a, ha⟩ := hs.2 ((restrictionTopIso M U).hom y)
    obtain ⟨b, hb⟩ := hRing.2 a
    refine ⟨b, hTop.1 ?_⟩
    rw [openGeneratorHom_top, hb]
    exact ha

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.CanonicalAffineFrame
