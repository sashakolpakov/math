import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Module Hom App Evaluation -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleHomAppEvaluation

/-! Forgetting scalar structure does not change the evaluation of a module-sheaf morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
universe u

theorem moduleHom_app_apply {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (U : X.Opens) (x : Γ(M, U)) : f.app U x = f.val.app (op U) x := rfl

end OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleHomAppEvaluation
