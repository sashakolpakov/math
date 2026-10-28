import Mathlib.Algebra.Category.ModuleCat.Basic

/-! # Additive Evaluation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.AdditiveEvaluation.ModuleAdditiveEvaluation

/-! # Evaluate the additive map underlying an actual module morphism -/

open _root_.CategoryTheory

universe u v

variable {R : Type u} [Ring R] {M N : ModuleCat.{v} R}

def map (f : M ⟶ N) : M →+ N := f.hom.toAddMonoidHom

theorem map_apply (f : M ⟶ N) (x : M) : map f x = f x := rfl

theorem map_double_apply {O : ModuleCat.{v} R} (f : M ⟶ N) (g : N ⟶ O) (x : M) :
    map g (map f x) = g (f x) := rfl

theorem apply (f : M ⟶ N) (x : M) : f.hom.toAddMonoidHom x = f x := rfl

theorem double {O : ModuleCat.{v} R} (f : M ⟶ N) (g : N ⟶ O) (x : M) :
    g.hom.toAddMonoidHom (f.hom.toAddMonoidHom x) = g (f x) := rfl

theorem triple {O P : ModuleCat.{v} R} (f : M ⟶ N) (g : N ⟶ O) (h : O ⟶ P) (x : M) :
    h.hom.toAddMonoidHom (g.hom.toAddMonoidHom (f.hom.toAddMonoidHom x)) = h (g (f x)) := rfl

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.AdditiveEvaluation.ModuleAdditiveEvaluation
