import Mathlib.CategoryTheory.EffectiveEpi.Basic

/-! # Faithful Factor Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.FaithfulFactorDescent

/-! A faithful functor detects the relations needed to descend a local factorization through an effective epimorphism. -/

open _root_.CategoryTheory

universe u v u' v'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (F : C ⥤ D) [F.Faithful] {X Y Z : C} (q : X ⟶ Y) [EffectiveEpi q] [Epi (F.map q)]
  (r : X ⟶ Z) (m : F.obj Y ⟶ F.obj Z) (hm : F.map q ≫ m = F.map r)

include hm

/-- The local factorization annihilates all global relations, so the actual effective quotient constructs a unique global factor. -/
theorem existsUnique_factor : ∃! d : Y ⟶ Z, q ≫ d = r ∧ F.map d = m := by
  have hr : ∀ {T : C} (a b : T ⟶ X), a ≫ q = b ≫ q → a ≫ r = b ≫ r := by
    intro T a b hab
    apply F.map_injective
    rw [F.map_comp, F.map_comp, ← hm, ← Category.assoc, ← Category.assoc,
      ← F.map_comp, ← F.map_comp, hab]
  let d := EffectiveEpi.desc q r hr
  have hd : q ≫ d = r := EffectiveEpi.fac q r hr
  have hF : F.map d = m := by
    apply (cancel_epi (F.map q)).mp
    exact (F.map_comp q d).symm.trans ((congrArg F.map hd).trans hm.symm)
  exact ⟨d, ⟨hd, hF⟩, fun e he => EffectiveEpi.uniq q r hr e he.1⟩

end OAI.AlgebraicGeometry.Picard.PoincareBundle.FaithfulFactorDescent
