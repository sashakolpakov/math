import Mathlib.Logic.Equiv.Defs

/-! # Multiplicative Descent -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicativeDescent.Comparison

/-! Multiplication descends through a genuinely bijective comparison
whose augmentation is already normalized on a cohomology model. -/

universe u v w
variable {A : Nat → Type u} {B : Nat → Type v} {H : Nat → Type w}
  (f : ∀ i, A i → B i) (c : ∀ i, B i → H i) (e : ∀ i, A i ≃ H i)
  (hc : ∀ i, Function.Bijective (c i)) (h : ∀ i x, c i (f i x) = e i x)

include hc h in
theorem surjective (i : Nat) : Function.Surjective (f i) := by
  intro y
  obtain ⟨x, hx⟩ := (e i).surjective (c i y)
  exact ⟨x, (hc i).injective ((h i x).trans hx)⟩

variable (μ : ∀ i j, A i → A j → A (i+j))
  (ν : ∀ i j, B i → B j → B (i+j))
  (κ : ∀ i j, H i → H j → H (i+j))
  (hf : ∀ i j x y, f (i+j) (μ i j x y) = ν i j (f i x) (f j y))
  (he : ∀ i j x y, κ i j (e i x) (e j y) = e (i+j) (μ i j x y))

include hc h hf he in
theorem multiplication (i j : Nat) (x : B i) (y : B j) :
    c (i+j) (ν i j x y) = κ i j (c i x) (c j y) := by
  obtain ⟨x, rfl⟩ := Comparison.surjective f c e hc h i x
  obtain ⟨y, rfl⟩ := Comparison.surjective f c e hc h j y
  rw [← hf, h, h, h, he]

end OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicativeDescent.Comparison
