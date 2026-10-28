import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! # Scalar Forget Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ScalarForgetEvaluation

noncomputable section

/-! Evaluation of a commuting square after forgetting module scalars. -/
open _root_.CategoryTheory
universe u
variable {R : Type u} [Ring R] {M N : ModuleCat.{u} R} {P : AddCommGrpCat.{u}}

theorem composite (f : M ⟶ N)
    (g : (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj N ⟶ P)
    (h : (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj M ⟶ P)
    (he : (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map f ≫ g = h) (x : M) :
    g (f x) = h x := ConcreteCategory.congr_hom he x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ScalarForgetEvaluation
