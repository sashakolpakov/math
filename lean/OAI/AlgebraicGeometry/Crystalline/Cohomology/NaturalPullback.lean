import Mathlib.CategoryTheory.Functor.Category

/-! # Natural Pullback -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.NaturalPullback.NaturalPullbackFactor

/-! # Transport of a pullback factorization through a natural comparison -/

open _root_.CategoryTheory

universe u v w z u' v' w' z'

variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D]
  {C' : Type u'} [Category.{v'} C'] {D' : Type w'} [Category.{z'} D']
  (F₀ : C ⥤ D) (Q₀ : C ⥤ C') (Q₁ : D ⥤ D') (F : C' ⥤ D')
  (η : Q₀ ⋙ F ⟶ F₀ ⋙ Q₁)
  {M M' : C} {N N' : D} (iM : M' ⟶ M) (iN : N' ⟶ N)
  (p : F₀.obj M ⟶ N) (p' : F₀.obj M' ⟶ N')
  (hp : p' ≫ iN = F₀.map iM ≫ p)

include hp in
theorem factor :
    (η.app M' ≫ Q₁.map p') ≫ Q₁.map iN = F.map (Q₀.map iM) ≫ (η.app M ≫ Q₁.map p) := by
  have hn : F.map (Q₀.map iM) ≫ η.app M = η.app M' ≫ Q₁.map (F₀.map iM) := η.naturality iM
  rw [Category.assoc, ← Q₁.map_comp, hp, Q₁.map_comp, ← Category.assoc, ← hn, Category.assoc]

end OAI.AlgebraicGeometry.Crystalline.Cohomology.NaturalPullback.NaturalPullbackFactor
