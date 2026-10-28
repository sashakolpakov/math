import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ScalarRestricted

/-! # Scalar Square Evaluation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.ScalarSquareEvaluation.ModuleScalarSquareEvaluation

noncomputable section

/-! # Evaluate a scalar-restricted module square without unfolding the coefficient modules -/

open _root_.CategoryTheory

universe u v

variable {R S : Type u} [Ring R] [Ring S] (φ : R →+* S)
  {M N : ModuleCat.{v} S} {P Q : ModuleCat.{v} R}
  (f : M ⟶ N) (a : (ModuleCat.restrictScalars φ).obj M ⟶ P)
  (b : P ⟶ Q) (c : (ModuleCat.restrictScalars φ).obj N ⟶ Q)
  (h : a ≫ b = (ModuleCat.restrictScalars φ).map f ≫ c)

include h in
theorem apply (x : M) : b.hom (a.hom x) = c.hom (f.hom x) :=
  LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) x

include h in
theorem addHom : b.hom.toAddMonoidHom.comp (ScalarRestricted.ScalarRestrictedAdditiveMap.map φ a) =
    (ScalarRestricted.ScalarRestrictedAdditiveMap.map φ c).comp f.hom.toAddMonoidHom := by
  apply AddMonoidHom.ext
  exact ModuleScalarSquareEvaluation.apply φ f a b c h

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.ScalarSquareEvaluation.ModuleScalarSquareEvaluation
