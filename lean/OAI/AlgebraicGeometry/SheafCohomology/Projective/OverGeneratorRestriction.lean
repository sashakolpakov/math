import OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleHomGluing
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OverGenerator

/-! # Over Generator Restriction -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.OverGeneratorRestriction

noncomputable section

/-! Restriction and scalar identities for maps specified by a local generator. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
universe u

theorem linearHomRestrict_comp {X : Scheme.{u}} (L M N : X.Modules)
    {U V : X.Opens} (h : V ≤ U) (a : L.over U ⟶ M.over U)
    (b : M.over U ⟶ N.over U) :
    LinearHom.linearHomRestrict X.ringCatSheaf L N (homOfLE h).op (a ≫ b) =
      LinearHom.linearHomRestrict X.ringCatSheaf L M (homOfLE h).op a ≫
        LinearHom.linearHomRestrict X.ringCatSheaf M N (homOfLE h).op b := by
  simp only [LinearHom.linearHomRestrict, Functor.map_comp, Category.assoc,
    Iso.hom_inv_id_app_assoc]

theorem linearHomRestrict_overGeneratorHom {X : Scheme.{u}} (M : X.Modules)
    {U V : X.Opens} (h : V ≤ U) (s : Γ(M, U)) :
    LinearHom.linearHomRestrict X.ringCatSheaf (Invertible.Scheme.Modules.unitObj X) M
      (homOfLE h).op (OverGenerator.overGeneratorHom M U s) =
    OverGenerator.overGeneratorHom M V (M.presheaf.map (homOfLE h).op s) := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro Z
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change (show Γ(X, Z.unop.left) from a) •
      M.presheaf.map (Z.unop.hom ≫ homOfLE h).op s =
    (show Γ(X, Z.unop.left) from a) •
      M.presheaf.map Z.unop.hom.op (M.presheaf.map (homOfLE h).op s)
  rw [op_comp, M.presheaf.map_comp_apply]

theorem overUnitScalarEnd_comp_overGeneratorHom {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (r : Γ(X, U)) (s : Γ(M, U)) :
    Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r ≫ OverGenerator.overGeneratorHom M U s =
      OverGenerator.overGeneratorHom M U (r • s) := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro Z
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change ((show Γ(X, Z.unop.left) from a) * X.presheaf.map Z.unop.hom.op r) •
      M.presheaf.map Z.unop.hom.op s =
    (show Γ(X, Z.unop.left) from a) • M.presheaf.map Z.unop.hom.op (r • s)
  rw [M.map_smul]
  exact mul_smul _ _ _

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.OverGeneratorRestriction
