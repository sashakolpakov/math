import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Splitting
import Mathlib.CategoryTheory.EffectiveEpi.Basic

/-! # Complementary Isogeny -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.ComplementaryIsogeny

noncomputable section

/-! An effective quotient with kernel killed by n has a constructed complementary morphism. -/

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]
  {A B : C} [GrpObj A] [IsCommMonObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f] (n : ℕ)
  (hker : ∀ (T : C) (x : T ⟶ A), x ≫ f = 1 → x ^ n = 1)

include hker

/-- Multiplication by n coequalizes the actual kernel relation on all test objects. -/
theorem scalar_coequalizes {T : C} (x y : T ⟶ A) (hxy : x ≫ f = y ≫ f) :
    x ≫ (𝟙 A) ^ n = y ≫ (𝟙 A) ^ n := by
  have hk : (x / y) ≫ f = 1 := by rw [GrpObj.div_comp, hxy, div_self']
  have hh := hker T (x / y) hk
  rw [div_pow, div_eq_one] at hh
  simpa only [MonObj.comp_pow, Category.comp_id] using hh

variable [EffectiveEpi f]

/-- The complementary morphism is constructed by the genuine effective quotient. -/
def complement : B ⟶ A :=
  EffectiveEpi.desc f ((𝟙 A) ^ n) (scalar_coequalizes f n hker)

/-- The quotient followed by its constructed complement is multiplication by n. -/
theorem left_complement : f ≫ complement f n hker = (𝟙 A) ^ n :=
  EffectiveEpi.fac f ((𝟙 A) ^ n) (scalar_coequalizes f n hker)

/-- The reverse composition is multiplication by n on the quotient as well. -/
theorem right_complement : complement f n hker ≫ f = (𝟙 B) ^ n := by
  apply (cancel_epi f).mp
  rw [← Category.assoc, left_complement, MonObj.pow_comp, MonObj.comp_pow,
    Category.id_comp, Category.comp_id]

variable [Epi (f ⊗ₘ f)]

/-- The constructed complement respects the group structure. -/
theorem complement_isMonHom : IsMonHom (complement f n hker) := by
  have : IsMonHom ((𝟙 A) ^ n) := Kernel.Splitting.power_isMonHom (𝟙 A) n
  constructor
  · rw [← IsMonHom.one_hom f, Category.assoc, left_complement, IsMonHom.one_hom]
  · apply (cancel_epi (f ⊗ₘ f)).mp
    rw [← Category.assoc, ← IsMonHom.mul_hom f, Category.assoc, left_complement,
      IsMonHom.mul_hom]
    rw [← Category.assoc, tensorHom_comp_tensorHom, left_complement]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.ComplementaryIsogeny
