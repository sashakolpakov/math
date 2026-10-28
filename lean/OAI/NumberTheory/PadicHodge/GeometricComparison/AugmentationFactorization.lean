import Mathlib.CategoryTheory.Functor.Basic

/-! # Augmentation Factorization -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.AugmentationFactorization.AugmentationFactorizationSource

/-! Precomposition of a typed augmentation factorization, including
the actual image of a composite source map under a functor. -/

open _root_.CategoryTheory

universe u v w z
variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D]

theorem source {O Z A B E T : D} (s : Z ⟶ O) (a : O ⟶ A) (b : O ⟶ B)
    (e : A ⟶ T) (u : B ⟶ E) (m : E ⟶ T) (h : a ≫ e = b ≫ u ≫ m) :
    (s ≫ a) ≫ e = (s ≫ b) ≫ u ≫ m := by
  simp only [Category.assoc]
  exact congrArg (fun k => s ≫ k) h

theorem functorSource (F : C ⥤ D) {O Z A B : C} {E T : D}
    (s : Z ⟶ O) (a : O ⟶ A) (b : O ⟶ B)
    (e : F.obj A ⟶ T) (u : F.obj B ⟶ E) (m : E ⟶ T)
    (h : F.map a ≫ e = F.map b ≫ u ≫ m) :
    F.map (s ≫ a) ≫ e = F.map (s ≫ b) ≫ u ≫ m := by
  rw [F.map_comp, F.map_comp]
  exact source (F.map s) (F.map a) (F.map b) e u m h

end OAI.NumberTheory.PadicHodge.GeometricComparison.AugmentationFactorization.AugmentationFactorizationSource
