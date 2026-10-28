import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing

/-! # Rationalization Detection -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.RationalizationDetection.Construction

noncomputable section

/-! Clearing denominators and detecting torsion in rationalized abelian groups. -/

open scoped TensorProduct

universe u
variable {G : Type u} [AddCommGroup G]

theorem rationalization_one_tmul_eq_zero_iff (x : G) :
    ((1 : ℚ) ⊗ₜ[ℤ] x : TensorProduct ℤ ℚ G) = 0 ↔
      ∃ n : ℤ, n ≠ 0 ∧ n • x = 0 := by
  rw [show ((1 : ℚ) ⊗ₜ[ℤ] x : TensorProduct ℤ ℚ G) =
    (TensorProduct.mk ℤ ℚ G 1) x from rfl,
    IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ)]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n.val, mem_nonZeroDivisors_iff_ne_zero.mp n.property, hn⟩
  · rintro ⟨n, hn, he⟩
    exact ⟨⟨n, mem_nonZeroDivisors_iff_ne_zero.mpr hn⟩, he⟩

theorem rationalization_exists_integer_multiple (x : TensorProduct ℤ ℚ G) :
    ∃ (n : ℤ) (g : G), n ≠ 0 ∧ n • x = (1 : ℚ) ⊗ₜ[ℤ] g := by
  obtain ⟨⟨g, n⟩, hn⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ)
    (TensorProduct.mk ℤ ℚ G 1) x
  exact ⟨n.val, g, mem_nonZeroDivisors_iff_ne_zero.mp n.property, hn⟩

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.RationalizationDetection.Construction
