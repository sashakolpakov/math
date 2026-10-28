import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-! # Injective Presentation Morphism -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.InjectivePresentationMorphism

noncomputable section

/-! A coefficient morphism extends to a morphism of short exact
presentations whenever the target middle object is injective. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
  {S T : ShortComplex C} (hS : S.ShortExact) [Injective T.X₂]

include hS in
theorem exists_morphism (α : S.X₁ ⟶ T.X₁) : ∃ φ : S ⟶ T, φ.τ₁ = α := by
  let : Mono S.f := hS.mono_f
  let : Epi S.g := hS.epi_g
  let β := Injective.factorThru (α ≫ T.f) S.f
  have hβ : S.f ≫ β = α ≫ T.f := Injective.comp_factorThru (α ≫ T.f) S.f
  have hzero : S.f ≫ (β ≫ T.g) = 0 := by
    rw [← Category.assoc, hβ, Category.assoc, T.zero, comp_zero]
  obtain ⟨γ, hγ⟩ := CokernelCofork.IsColimit.desc' hS.exact.gIsCokernel (β ≫ T.g) hzero
  exact ⟨{ τ₁ := α, τ₂ := β, τ₃ := γ, comm₁₂ := hβ.symm, comm₂₃ := hγ.symm }, rfl⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.InjectivePresentationMorphism
