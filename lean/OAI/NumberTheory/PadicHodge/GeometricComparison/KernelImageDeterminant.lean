import OAI.NumberTheory.PadicHodge.GeometricComparison.WeakAdmissibilityTransport

/-! # Kernel Image Determinant -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.KernelImageDeterminant.FiltrationTransport

noncomputable section

/-! Determinants and Newton numbers split along the actual kernel and image of an intertwining map. -/

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

theorem intertwining_kernel_stable (φ : Module.End K V) (ψ : Module.End K W) (f : V →ₗ[K] W)
    (h : ∀ x, f (φ x) = ψ (f x)) : f.ker ≤ f.ker.comap φ := by
  intro x hx
  change f (φ x) = 0
  exact (h x).trans ((congrArg ψ hx).trans ψ.map_zero)

theorem intertwining_range_stable (φ : Module.End K V) (ψ : Module.End K W) (f : V →ₗ[K] W)
    (h : ∀ x, f (φ x) = ψ (f x)) : f.range ≤ f.range.comap ψ := by
  rintro y ⟨x, rfl⟩
  exact ⟨φ x, h x⟩

theorem quotient_image_intertwines (φ : Module.End K V) (ψ : Module.End K W) (f : V →ₗ[K] W)
    (h : ∀ x, f (φ x) = ψ (f x)) (x : V ⧸ f.ker) :
    f.quotKerEquivRange
        (f.ker.mapQ f.ker φ (intertwining_kernel_stable φ ψ f h) x) =
      ψ.restrict (intertwining_range_stable φ ψ f h) (f.quotKerEquivRange x) := by
  induction x using Submodule.Quotient.induction_on with
  | H x => exact Subtype.ext (h x)

theorem kernel_image_det [FiniteDimensional K V]
    (φ : Module.End K V) (ψ : Module.End K W) (f : V →ₗ[K] W)
    (h : ∀ x, f (φ x) = ψ (f x)) :
    φ.det = (φ.restrict (intertwining_kernel_stable φ ψ f h)).det *
      (ψ.restrict (intertwining_range_stable φ ψ f h)).det := by
  rw [LinearMap.det_eq_det_mul_det f.ker φ (intertwining_kernel_stable φ ψ f h)]
  exact congrArg (fun a => (φ.restrict (intertwining_kernel_stable φ ψ f h)).det * a)
    (WeakAdmissibilityTransport.FiltrationTransport.det_eq_of_intertwines f.quotKerEquivRange _ _ (quotient_image_intertwines φ ψ f h)).symm

variable {q : ℕ} [Fact q.Prime]
  {D E : Type*} [AddCommGroup D] [Module ℚ_[q] D] [FiniteDimensional ℚ_[q] D]
  [AddCommGroup E] [Module ℚ_[q] E]

theorem kernel_image_newton (φ : D ≃ₗ[ℚ_[q]] D) (ψ : Module.End ℚ_[q] E) (f : D →ₗ[ℚ_[q]] E)
    (h : ∀ x, f (φ x) = ψ (f x)) :
    (Padic.valuation φ.toLinearMap.det : ℚ) =
      (Padic.valuation (φ.toLinearMap.restrict (intertwining_kernel_stable φ.toLinearMap ψ f h)).det : ℚ) +
      (Padic.valuation (ψ.restrict (intertwining_range_stable φ.toLinearMap ψ f h)).det : ℚ) := by
  have hd := kernel_image_det φ.toLinearMap ψ f h
  have hn : (φ.toLinearMap.restrict (intertwining_kernel_stable φ.toLinearMap ψ f h)).det *
      (ψ.restrict (intertwining_range_stable φ.toLinearMap ψ f h)).det ≠ 0 := by
    rw [← hd]
    exact φ.isUnit_det'.ne_zero
  rw [hd, Padic.valuation_mul (mul_ne_zero_iff.mp hn).1 (mul_ne_zero_iff.mp hn).2, Int.cast_add]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.KernelImageDeterminant.FiltrationTransport
