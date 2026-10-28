import OAI.NumberTheory.PadicHodge.GeometricComparison.PrimeTorsion
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Linear.LinearFunctor

/-! # Triangle Prime -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.TrianglePrime.TrianglePrimeTorsion

noncomputable section

/-! A reduction triangle and surjectivity in degree zero imply absence of prime torsion in degree one. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Pretriangulated

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

theorem shifted_injective (T : Triangle C) (hT : T ∈ distTriang C) (A : C)
    (hs : Function.Surjective (fun f : A ⟶ T.obj₂ => f ≫ T.mor₂)) :
    Function.Injective (fun f : A ⟶ T.obj₁⟦(1 : ℤ)⟧ => f ≫ T.mor₁⟦(1 : ℤ)⟧') := by
  intro x y hxy
  dsimp only at hxy
  have hz : (x - y) ≫ T.mor₁⟦(1 : ℤ)⟧' = 0 := by rw [Preadditive.sub_comp, hxy, sub_self]
  obtain ⟨z, hz⟩ := T.coyoneda_exact₁ hT (x - y) hz
  obtain ⟨w, rfl⟩ := hs z
  apply sub_eq_zero.mp
  rw [hz, Category.assoc, comp_distTriang_mor_zero₂₃ T hT, comp_zero]

theorem torsionFree (p : ℕ) [Fact p.Prime] [Linear ℤ_[p] C]
    [(shiftFunctor C (1 : ℤ)).Linear ℤ_[p]]
    (X Y A : C) (r : X ⟶ Y) (δ : Y ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk ((p : ℤ_[p]) • 𝟙 X) r δ ∈ distTriang C)
    (hs : Function.Surjective (fun f : A ⟶ X => f ≫ r)) :
    Module.IsTorsionFree ℤ_[p] (A ⟶ X⟦(1 : ℤ)⟧) := by
  apply PrimeTorsion.PrimeTorsionCriterion.torsionFree p
  intro x hx
  apply shifted_injective (Triangle.mk ((p : ℤ_[p]) • 𝟙 X) r δ) hT A hs
  change x ≫ (shiftFunctor C (1 : ℤ)).map ((p : ℤ_[p]) • 𝟙 X) =
    0 ≫ (shiftFunctor C (1 : ℤ)).map ((p : ℤ_[p]) • 𝟙 X)
  rw [Functor.map_smul, CategoryTheory.Functor.map_id, Linear.comp_smul,
    Category.comp_id, hx, zero_comp]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.TrianglePrime.TrianglePrimeTorsion
