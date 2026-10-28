import Mathlib.CategoryTheory.Functor.Basic

/-! # Composite Factor -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.CompositeFactor.FunctorCompositeFactor

/-! Group the two mapped factors of an original comparison before
identifying its complete composite. -/

open _root_.CategoryTheory
universe u₁ v₁ u₂ v₂ u₃ v₃
variable {C : Type u₁} [Category.{v₁} C]
  {D : Type u₂} [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E]

theorem factor (T : C ⥤ D) (H : D ⥤ E) {A B P : C} {Q : E}
    (a : A ⟶ B) (b : B ⟶ P) (h : H.obj (T.obj P) ⟶ Q) :
    H.map (T.map a) ≫ H.map (T.map b) ≫ h = H.map (T.map (a ≫ b)) ≫ h := by
  rw [T.map_comp, H.map_comp, Category.assoc]

end OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.CompositeFactor.FunctorCompositeFactor
