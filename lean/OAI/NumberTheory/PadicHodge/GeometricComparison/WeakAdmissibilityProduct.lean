import OAI.NumberTheory.PadicHodge.GeometricComparison.FiltrationBounds
import OAI.NumberTheory.PadicHodge.GeometricComparison.FilteredImageDimension
import OAI.NumberTheory.PadicHodge.GeometricComparison.ProductKernel
import OAI.NumberTheory.PadicHodge.GeometricComparison.KernelImageDeterminant
import OAI.NumberTheory.PadicHodge.FilteredProjection
import OAI.NumberTheory.PadicHodge.GeometricComparison.SplitFiltration

/-! # Weak Admissibility Product -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.WeakAdmissibilityProduct

noncomputable section

/-! Weak admissibility in degrees zero and one is preserved by products, testing every stable subspace. -/

variable {q : ℕ} [Fact q.Prime]
  {V W : Type*} [AddCommGroup V] [Module ℚ_[q] V] [FiniteDimensional ℚ_[q] V]
  [AddCommGroup W] [Module ℚ_[q] W] [FiniteDimensional ℚ_[q] W]

theorem weaklyAdmissible_product_h1
    (F : Linear.FiniteFiltration ℚ_[q] V) (G : Linear.FiniteFiltration ℚ_[q] W)
    (φ : V ≃ₗ[ℚ_[q]] V) (ψ : W ≃ₗ[ℚ_[q]] W)
    (hF : Linear.WeaklyAdmissible q F φ) (hG : Linear.WeaklyAdmissible q G ψ)
    (hF0 : F.step 0 = ⊤) (hF2 : F.step 2 = ⊥)
    (hG0 : G.step 0 = ⊤) (hG2 : G.step 2 = ⊥) :
    Linear.WeaklyAdmissible q (ProductFiltration.FiltrationTransport.product F G) (φ.prodCongr ψ) := by
  constructor
  · rw [ProductFiltration.FiltrationTransport.product_tH, hF.1, hG.1]
    change _ = (Padic.valuation (LinearMap.prodMap φ.toLinearMap ψ.toLinearMap).det : ℚ)
    rw [LinearMap.det_prodMap, Padic.valuation_mul φ.isUnit_det'.ne_zero ψ.isUnit_det'.ne_zero, Int.cast_add]
  · intro U hU
    let φU := FilteredProjection.GeometricComparison.FiltrationTransport.invariantRestriction (φ.prodCongr ψ) U hU
    let f := ProductKernel.ProductSubspace.second U
    let A := ProductKernel.ProductSubspace.first U
    have hf : ∀ x, f (φU x) = ψ (f x) := fun _ => rfl
    have hA : A ≤ A.comap φ.toLinearMap := ProductKernel.ProductSubspace.first_stable φ.toLinearMap ψ.toLinearMap U hU
    have hB := KernelImageDeterminant.FiltrationTransport.intertwining_range_stable φU.toLinearMap ψ.toLinearMap f hf
    have hAineq := hF.2 A hA
    have hBineq := hG.2 f.range hB
    rw [FirstHodgeNumber.FiltrationTransport.tH_h1 _ (FiltrationBounds.FiltrationTransport.restrict_top F A 0 hF0) (FiltrationBounds.FiltrationTransport.restrict_bot F A 2 hF2), SplitFiltration.FiltrationTransport.restrict_step_finrank] at hAineq
    rw [FirstHodgeNumber.FiltrationTransport.tH_h1 _ (FiltrationBounds.FiltrationTransport.restrict_top G f.range 0 hG0) (FiltrationBounds.FiltrationTransport.restrict_bot G f.range 2 hG2), SplitFiltration.FiltrationTransport.restrict_step_finrank] at hBineq
    have hN := KernelImageDeterminant.FiltrationTransport.kernel_image_newton φU ψ.toLinearMap f hf
    let eK : f.ker ≃ₗ[ℚ_[q]] A := ProductKernel.ProductSubspace.kernelEquiv U
    let TK : Module.End ℚ_[q] f.ker :=
      φU.toLinearMap.restrict (KernelImageDeterminant.FiltrationTransport.intertwining_kernel_stable φU.toLinearMap ψ.toLinearMap f hf)
    have heK : ∀ x : f.ker, eK (TK x) = (φ.toLinearMap.restrict hA) (eK x) := by
      intro x
      apply Subtype.ext
      change φ x.1.1.1 = φ x.1.1.1
      rfl
    have hdet := (WeakAdmissibilityTransport.FiltrationTransport.det_eq_of_intertwines
      (R := ℚ_[q]) (D := f.ker) (E := A) eK TK (φ.toLinearMap.restrict hA) heK).symm
    rw [hdet] at hN
    let P := ((F.step 1).prod (G.step 1)).comap U.subtype
    have hdim := FilteredImageDimension.FiltrationTransport.filtered_image_dimension f P (G.step 1)
      (ProductKernel.ProductSubspace.second_filtered U (F.step 1) (G.step 1))
    rw [(ProductKernel.ProductSubspace.filteredKernelEquiv U (F.step 1) (G.step 1)).finrank_eq] at hdim
    have hdimQ : (Module.finrank ℚ_[q] P : ℚ) ≤
        (Module.finrank ℚ_[q] (A ⊓ F.step 1 : Submodule ℚ_[q] V) : ℚ) +
        (Module.finrank ℚ_[q] (f.range ⊓ G.step 1 : Submodule ℚ_[q] W) : ℚ) := by
      exact_mod_cast hdim
    rw [FirstHodgeNumber.FiltrationTransport.tH_h1 _ (FiltrationBounds.FiltrationTransport.restrict_top (ProductFiltration.FiltrationTransport.product F G) U 0 (FiltrationBounds.FiltrationTransport.product_top F G 0 hF0 hG0))
      (FiltrationBounds.FiltrationTransport.restrict_bot (ProductFiltration.FiltrationTransport.product F G) U 2 (FiltrationBounds.FiltrationTransport.product_bot F G 2 hF2 hG2))]
    change (Module.finrank ℚ_[q] P : ℚ) ≤ (Padic.valuation φU.toLinearMap.det : ℚ)
    linarith

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.WeakAdmissibilityProduct
