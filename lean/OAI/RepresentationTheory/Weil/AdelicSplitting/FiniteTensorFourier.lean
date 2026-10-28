import Mathlib.MeasureTheory.Integral.Pi

/-! # Finite Tensor Fourier -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteTensorFourier.Construction

noncomputable section

/-! Finite tensor integral transforms preserve pointwise linear relations.
This is the finite-product Fubini step used for actual local Fourier factors. -/

open _root_.MeasureTheory

variable {I J : Type*} [Fintype I] [Fintype J]
variable {V : I → Type*} [∀ i, MeasurableSpace (V i)]
variable (μ : ∀ i, Measure (V i)) [∀ i, SigmaFinite (μ i)]

theorem finite_tensor_integral_relation
    (f : ∀ i, V i → ℂ) (g : J → ∀ i, V i → ℂ) (a : J → ℂ)
    (K : ∀ i, V i → ℂ)
    (hg : ∀ j i, Integrable (fun x => g j i x * K i x) (μ i))
    (hrel : ∀ x : ∀ i, V i, (∏ i, f i (x i)) = ∑ j, a j * ∏ i, g j i (x i)) :
    (∏ i, ∫ x, f i x * K i x ∂μ i) =
      ∑ j, a j * ∏ i, ∫ x, g j i x * K i x ∂μ i := by
  rw [← integral_fintype_prod_eq_prod]
  have he (x : ∀ i, V i) : (∏ i, f i (x i) * K i (x i)) =
      ∑ j, a j * ∏ i, g j i (x i) * K i (x i) := by
    simp only [Finset.prod_mul_distrib, hrel, Finset.sum_mul, mul_assoc]
  simp_rw [he]
  rw [integral_finsetSum]
  · simp only [integral_const_mul]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    exact integral_fintype_prod_eq_prod (fun i x => g j i x * K i x)
  · intro j _
    exact (Integrable.fintype_prod_dep (hg j)).const_mul (a j)

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteTensorFourier.Construction
