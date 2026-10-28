import OAI.AlgebraicGeometry.FormalGeometry.Completion.IntegralQuadraticSpectrum
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ExactSequenceEigenvalues
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Stability

/-! # Quadratic Spectral Step -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion

noncomputable section

/-! One step of the quadratic filtration sends an eigenvalue to its
kernel or bounds it using the positive definite quotient. -/

open scoped TensorProduct

universe u
variable {G : Type u} [AddCommGroup G] [Module.Finite ℤ G]

theorem NonnegativeQuadraticMk.Construction.NonnegativeQuadratic.eigenvalue_kernel_or_norm (q : NonnegativeQuadraticMk.Construction.NonnegativeQuadratic G)
    (f : G →+ G) (c : ℚ) (hf : ∀ g, q.value (f g) = c * q.value g)
    (z : ℂ) (hz : Module.End.HasEigenvalue (f.toIntLinearMap.baseChange ℂ) z) :
    Module.End.HasEigenvalue ((q.kernelSimilitude f c hf).toIntLinearMap.baseChange ℂ) z ∨
      ‖z‖ = Real.sqrt (c : ℝ) := by
  let i := q.zeroKernel.subtype.toIntLinearMap
  let p := (QuotientAddGroup.mk' q.zeroKernel).toIntLinearMap
  have hp : Function.Surjective p := QuotientAddGroup.mk'_surjective q.zeroKernel
  have he : Function.Exact i p := by
    intro x
    change (QuotientAddGroup.mk x : G ⧸ q.zeroKernel) = 0 ↔ ∃ y : q.zeroKernel, (y : G) = x
    rw [QuotientAddGroup.eq_zero_iff]
    exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.property⟩
  have : Module.Finite ℤ (G ⧸ q.zeroKernel) := Module.Finite.of_surjective p hp
  have : Module.Flat ℤ ℚ := IsLocalization.flat ℚ (nonZeroDivisors ℤ)
  have : Module.Flat ℤ ℂ := Module.Flat.trans ℤ ℚ ℂ
  have h := ExactSequenceEigenvalues.Construction.baseChange_eigenvalue_or_of_exact i p Subtype.val_injective he hp
    (q.kernelSimilitude f c hf).toIntLinearMap f.toIntLinearMap
    (q.quotientSimilitude f c hf).toIntLinearMap (fun _ => rfl) (fun _ => rfl) z hz
  exact h.imp_right (q.quotientComplexEigenvalue_norm f c hf z)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion
