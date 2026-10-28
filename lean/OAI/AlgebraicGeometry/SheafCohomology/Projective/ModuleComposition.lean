import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Module Composition -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleComposition

/-! Component formulas with the scheme and coefficient modules held fixed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
universe u

theorem module_comp_apply {X : Scheme.{u}} {M N P : X.Modules}
    (f : M ⟶ N) (g : N ⟶ P) (U : X.Opensᵒᵖ) (x : M.val.obj U) :
    (f ≫ g).val.app U x = g.val.app U (f.val.app U x) := rfl

theorem module_pushforward_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : X.Modules} (g : M ⟶ N) (U : Y.Opensᵒᵖ)
    (x : ((Scheme.Modules.pushforward f).obj M).val.obj U) :
    ((Scheme.Modules.pushforward f).map g).val.app U x =
      g.val.app (.op (f ⁻¹ᵁ U.unop)) x := rfl

end OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleComposition
