import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Positive.RationalKernelPoint
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Positive.RationalCommonDenominator

/-! # Natural Kernel Point -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Positive.NaturalKernelPoint

noncomputable section

/-! Positive real solutions of homogeneous rational linear equations
give positive natural solutions, with all equations preserved exactly. -/
open scoped Classical _root_.Matrix
universe u

theorem rationalMatrix_positive_natural_kernel_point {ι κ : Type u} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) (x : κ → ℝ)
    (hx : A.map (algebraMap ℚ ℝ) *ᵥ x = 0) (hxpos : ∀ i, 0 < x i) :
    ∃ a : κ → ℕ, (∀ i, 0 < a i) ∧ A *ᵥ (fun i => (a i : ℚ)) = 0 := by
  obtain ⟨q, hq, hqpos⟩ := RationalKernelPoint.rationalMatrix_positive_kernel_point A x hx hxpos
  obtain ⟨D, _, a, ha, hae⟩ := RationalCommonDenominator.positiveRationalVector_commonDenominator q hqpos
  refine ⟨a, ha, ?_⟩
  have he : (fun i => (a i : ℚ)) = (D : ℚ) • q := by
    funext i
    exact hae i
  rw [he, Matrix.mulVec_smul, hq, smul_zero]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Positive.NaturalKernelPoint
