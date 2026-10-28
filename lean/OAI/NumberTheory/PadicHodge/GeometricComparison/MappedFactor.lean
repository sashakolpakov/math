import OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.CompositeFactor

/-! # Mapped Factor -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.MappedFactor.MappedComparisonFactor

/-! Factor a named comparison using separately verified original factors. -/
open _root_.CategoryTheory
universe u₁ v₁ u₂ v₂ u₃ v₃
variable {C : Type u₁} [Category.{v₁} C]
  {D : Type u₂} [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E]

theorem equality (T : C ⥤ D) (H : D ⥤ E) {A B P : C} {Q : E}
    (a : A ⟶ B) (b : B ⟶ P) (h : H.obj (T.obj P) ⟶ Q)
    (c : H.obj (T.obj A) ⟶ H.obj (T.obj B))
    (i : H.obj (T.obj B) ⟶ Q) (f : H.obj (T.obj A) ⟶ Q)
    (hc : c = H.map (T.map a)) (hi : i = H.map (T.map b) ≫ h)
    (hf : f = c ≫ i) : f = H.map (T.map (a ≫ b)) ≫ h := by
  rw [hf, hc, hi]
  exact Functor.CompositeFactor.FunctorCompositeFactor.factor T H a b h

end OAI.NumberTheory.PadicHodge.GeometricComparison.MappedFactor.MappedComparisonFactor
