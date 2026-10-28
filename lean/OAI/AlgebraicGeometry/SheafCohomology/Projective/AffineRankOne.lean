import OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation
import OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent

/-! # Affine Rank One -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.AffineRankOne

noncomputable section

/-! Recovering an affine rank-one frame from a generator of global sections. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable {X : Scheme.{u}} (M : X.Modules)

/-- Restriction of a global section, as a compatible family of sections. -/
def globalSectionFamily (x : Γ(M, (⊤ : X.Opens))) : M.sections :=
  PresheafOfModules.sectionsMk
    (fun U => M.presheaf.map U.unop.leTop.op x)
    (by
      intro U V f
      change M.presheaf.map f (M.presheaf.map U.unop.leTop.op x) =
        M.presheaf.map V.unop.leTop.op x
      rw [← M.presheaf.map_comp_apply]
      congr 2)

/-- The map from the structure sheaf with prescribed image of one. -/
def globalGeneratorHom (x : Γ(M, (⊤ : X.Opens))) :
    Invertible.Scheme.Modules.unitObj X ⟶ M :=
  M.unitHomEquiv.symm (globalSectionFamily M x)

theorem globalGeneratorHom_app (x : Γ(M, (⊤ : X.Opens)))
    (U : X.Opens) (r : Γ(X, U)) :
    (globalGeneratorHom M x).val.app (op U) r =
      r • M.presheaf.map U.leTop.op x := rfl

@[simp]
theorem globalGeneratorHom_top (x : Γ(M, (⊤ : X.Opens)))
    (r : Γ(X, (⊤ : X.Opens))) :
    (globalGeneratorHom M x).val.app (op ⊤) r = r • x := by
  rw [globalGeneratorHom_app]
  have h : (⊤ : X.Opens).leTop.op = 𝟙 (op (⊤ : X.Opens)) := Subsingleton.elim _ _
  rw [h, M.presheaf.map_id]
  rfl

/-- On an affine scheme, a global basis of a quasicoherent module gives a
genuine isomorphism with the structure sheaf. -/
def affineRankOneIso [IsAffine X] [M.IsQuasicoherent]
    (e : Γ(X, (⊤ : X.Opens)) ≃ₗ[Γ(X, (⊤ : X.Opens))] Γ(M, (⊤ : X.Opens))) :
    Invertible.Scheme.Modules.unitObj X ≅ M := by
  let f := globalGeneratorHom M (e 1)
  have htop : f.val.app (op ⊤) = e.toModuleIso.hom := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change (globalGeneratorHom M (e 1)).val.app (op ⊤) r = e r
    rw [globalGeneratorHom_top, ← e.map_smul]
    simp only [smul_eq_mul, mul_one]
  letI : (Invertible.Scheme.Modules.unitObj X).IsQuasicoherent :=
    InvertibleFinitePresentation.invertible_quasicoherent Invertible.Scheme.Modules.isInvertible_unit
  letI : IsIso f := Quasicoherent.Scheme.Modules.isIso_of_isQuasicoherent_of_isIso_app_top f
    (htop ▸ inferInstance)
  exact asIso f

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.AffineRankOne
