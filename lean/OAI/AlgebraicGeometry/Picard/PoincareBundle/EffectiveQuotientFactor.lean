import Mathlib.CategoryTheory.EffectiveEpi.Basic

/-! # Effective Quotient Factor -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.EffectiveQuotientFactor

noncomputable section

/-! A monomorphism through which an effective quotient factors is an actual isomorphism. -/

open _root_.CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] {X Y D : C}
  (p : X ⟶ Y) [EffectiveEpi p] (j : D ⟶ Y) [Mono j] (r : X ⟶ D) (h : r ≫ j = p)

include h

omit [EffectiveEpi p] in
/-- The factor through the monomorphism coequalizes every pair identified by the original quotient. -/
theorem coequalizes {T : C} (a b : T ⟶ X) (hab : a ≫ p = b ≫ p) : a ≫ r = b ≫ r := by
  apply (cancel_mono j).mp
  simpa only [Category.assoc, h] using hab

/-- The inverse is constructed by the actual universal property of the effective quotient. -/
def inverse : Y ⟶ D := EffectiveEpi.desc p r (coequalizes p j r h)

/-- The constructed inverse recovers the given factor. -/
theorem inverse_fac : p ≫ inverse p j r h = r := EffectiveEpi.fac p r (coequalizes p j r h)

/-- A full actual categorical isomorphism, with both inverse equations proved. -/
def factorIso : D ≅ Y where
  hom := j
  inv := inverse p j r h
  hom_inv_id := by
    apply (cancel_mono j).mp
    have hj : inverse p j r h ≫ j = 𝟙 Y := by
      apply (cancel_epi p).mp
      rw [← Category.assoc, inverse_fac, h, Category.comp_id]
    rw [Category.assoc, hj, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply (cancel_epi p).mp
    rw [← Category.assoc, inverse_fac, h, Category.comp_id]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.EffectiveQuotientFactor
