import OAI.NumberTheory.PadicHodge.GeometricComparison.WeakAdmissibilityTransport

/-! # Split Determinant -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.SplitDeterminant.FiltrationTransport

noncomputable section

/-! Frobenius determinants and Newton numbers add over actual complementary invariant subspaces. -/

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem split_det (φ : Module.End K V) (S T : Submodule K V) (hc : IsCompl S T)
    (hS : S ≤ S.comap φ) (hT : T ≤ T.comap φ) :
    φ.det = (φ.restrict hS).det * (φ.restrict hT).det := by
  have h := WeakAdmissibilityTransport.FiltrationTransport.det_eq_of_intertwines (S.prodEquivOfIsCompl T hc)
    (LinearMap.prodMap (φ.restrict hS) (φ.restrict hT)) φ (by
      intro x
      change φ (x.1 : V) + φ (x.2 : V) = φ ((x.1 : V) + (x.2 : V))
      exact (φ.map_add _ _).symm)
  exact h.trans (LinearMap.det_prodMap _ _)

variable {q : ℕ} [Fact q.Prime]
  {D : Type*} [AddCommGroup D] [Module ℚ_[q] D] [FiniteDimensional ℚ_[q] D]

theorem split_newton (φ : D ≃ₗ[ℚ_[q]] D) (S T : Submodule ℚ_[q] D)
    (hc : IsCompl S T) (hS : S ≤ S.comap φ.toLinearMap)
    (hT : T ≤ T.comap φ.toLinearMap) :
    (Padic.valuation φ.toLinearMap.det : ℚ) =
      (Padic.valuation (φ.toLinearMap.restrict hS).det : ℚ) +
      (Padic.valuation (φ.toLinearMap.restrict hT).det : ℚ) := by
  have hd := split_det φ.toLinearMap S T hc hS hT
  have hn : (φ.toLinearMap.restrict hS).det * (φ.toLinearMap.restrict hT).det ≠ 0 := by
    rw [← hd]
    exact φ.isUnit_det'.ne_zero
  rw [hd, Padic.valuation_mul (mul_ne_zero_iff.mp hn).1 (mul_ne_zero_iff.mp hn).2,
    Int.cast_add]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.SplitDeterminant.FiltrationTransport
