import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Lax Pairing -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.LaxPairing

/-! Additive lax monoidal functors preserve bilinear Leibniz identities.
This applies to the actual sheafification and underlying-presheaf
functors, without an exactness assumption on tensor products. -/

open _root_.CategoryTheory MonoidalCategory Functor.LaxMonoidal

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [MonoidalCategory D]
  (F : C ⥤ D) [F.Additive] [F.LaxMonoidal]
  {M N P M' N' P' : C}
  (a : M ⟶ M') (b : N ⟶ N') (c : P ⟶ P')
  (m : M ⊗ N ⟶ P) (m₁ : M' ⊗ N ⟶ P') (m₂ : M ⊗ N' ⟶ P')
  (z : ℤ) (h : m ≫ c = (a ⊗ₘ 𝟙 N) ≫ m₁ + z • ((𝟙 M ⊗ₘ b) ≫ m₂))

include h in
theorem differential : (μ F M N ≫ F.map m) ≫ F.map c =
    (F.map a ⊗ₘ 𝟙 (F.obj N)) ≫ (μ F M' N ≫ F.map m₁) +
      z • ((𝟙 (F.obj M) ⊗ₘ F.map b) ≫ (μ F M N' ≫ F.map m₂)) := by
  rw [Category.assoc, ← F.map_comp, h, F.map_add, F.map_zsmul,
    Preadditive.comp_add, Preadditive.comp_zsmul, F.map_comp, F.map_comp]
  rw [← F.map_id N, ← F.map_id M, μ_natural_assoc, μ_natural_assoc]

end OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.LaxPairing
