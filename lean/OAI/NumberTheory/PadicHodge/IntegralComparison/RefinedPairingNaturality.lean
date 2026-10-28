import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Iso

/-! # Refined Pairing Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RefinedPairingNaturality

/-! A naturality square descends through a common refinement whenever
the two actual maps compose to the given refined map. -/

open _root_.CategoryTheory

universe u v w t

variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{t} D]

@[reassoc]
theorem of_factorization (F : C ⥤ D) {A B L : C} {E₁ E₂ : D}
    (l : A ⟶ L) (r : B ⟶ L) (f : B ⟶ A) (d : E₂ ⟶ E₁)
    {pA : F.obj A ≅ E₁} {pB : F.obj B ≅ E₂} {pL : F.obj L ≅ E₁}
    (hl : F.map l ≫ pL.hom = pA.hom)
    (hr : F.map r ≫ pL.hom = pB.hom ≫ d) (hf : f ≫ l = r) :
    F.map f ≫ pA.hom = pB.hom ≫ d := by
  rw [← hl, ← Category.assoc, ← F.map_comp, hf]
  exact hr

@[reassoc]
theorem of_factorization_identity (F : C ⥤ D) {A B L : C} {E₁ E₂ : D}
    (l : A ⟶ L) (r : B ⟶ L) (f : B ⟶ A) (d : E₂ ⟶ E₁) (e : E₁ ⟶ E₁)
    {pA : F.obj A ≅ E₁} {pB : F.obj B ≅ E₂} {pL : F.obj L ≅ E₁}
    (hl : F.map l ≫ pL.hom = pA.hom ≫ e)
    (hr : F.map r ≫ pL.hom = pB.hom ≫ d) (he : e = 𝟙 E₁) (hf : f ≫ l = r) :
    F.map f ≫ pA.hom = pB.hom ≫ d := by
  rw [he, Category.comp_id] at hl
  exact of_factorization F l r f d hl hr hf

end OAI.NumberTheory.PadicHodge.IntegralComparison.RefinedPairingNaturality
