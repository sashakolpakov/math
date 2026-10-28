import OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleComposition

/-! # Module Composition Evaluation -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleCompositionEvaluation

noncomputable section

/-! Evaluating identities between composites of actual sheaf-module maps. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
universe u

theorem module_comp_eq_apply {X : Scheme.{u}} {M N P Q : X.Modules}
    (f : M ⟶ N) (g : N ⟶ Q) (h : M ⟶ P) (k : P ⟶ Q)
    (heq : f ≫ g = h ≫ k) (U : X.Opens) (x : Γ(M, U)) :
    g.val.app (op U) (f.val.app (op U) x) =
      k.val.app (op U) (h.val.app (op U) x) := by
  erw [← ModuleComposition.module_comp_apply f g (op U) x, heq, ModuleComposition.module_comp_apply]

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleCompositionEvaluation
