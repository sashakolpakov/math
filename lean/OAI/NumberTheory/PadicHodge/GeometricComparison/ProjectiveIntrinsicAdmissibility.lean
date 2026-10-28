import OAI.NumberTheory.PadicHodge.GeometricComparison.ProjectiveNumbers
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicConstructed.FrobeniusDivisibility
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicConstructed.IntegralFrobenius
import OAI.NumberTheory.PadicHodge.GeometricComparison.StableLattice
import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.PolynomialWeights
import OAI.NumberTheory.PadicHodge.GeometricComparison.WeilDeterminantNorm
import OAI.NumberTheory.PadicHodge.GeometricComparison.WeakAdmissibilityTransport

/-! # Projective Intrinsic Admissibility -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! Native weak admissibility using the proved projective comparison.
The integral lattice and its Frobenius divisibility are unchanged. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

theorem Geometry.AbelianH1Model.crystalline_finite_of_projective_comparison (j : K →+* ℂ)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom) :
    FiniteDimensional ℚ_[q] A.Crystalline := by
  let : FiniteDimensional ℚ_[q] A.DeRham := A.localDeRham_finite_of_projective_comparison j P
  exact A.constructedCrystallineDeRhamEquiv.symm.finiteDimensional

theorem Geometry.AbelianH1Model.projective_hodge_newton_equality
    [FiniteDimensional ℚ_[q] A.DeRham] [FiniteDimensional ℚ_[q] A.Crystalline]
    (hCompletion : Completion.GeometricWeightInput.{0})
    (j : K →+* ℂ)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q)
    (W : Polynomial ℤ) (hW : A.IsWeilPolynomial ℓ W)
    (hC : A.crystallineFrobenius.charpoly = W.map (Int.castRingHom ℚ_[q]))
    (cmp : A.Crystalline ≃ₗ[ℚ_[q]] A.DeRham)
    (φ : A.Crystalline ≃ₗ[ℚ_[q]] A.Crystalline)
    (hφ : φ.toLinearMap = A.crystallineFrobenius) :
    A.finiteFiltration.tH =
      (Padic.valuation (WeakAdmissibilityTransport.FiltrationTransport.conjugateEquiv cmp φ).toLinearMap.det : ℚ) := by
  have hH := A.projective_hodge_number_twice j P
  have hN := WeilDeterminantNorm.WeilDeterminant.determinant_valuation_twice q A.crystallineFrobenius W hC
    (A.native_polynomial_weights hCompletion ℓ hℓq W hW)
  have hdim := cmp.finrank_eq
  have hdet : (WeakAdmissibilityTransport.FiltrationTransport.conjugateEquiv cmp φ).toLinearMap.det =
      A.crystallineFrobenius.det := by
    rw [WeakAdmissibilityTransport.FiltrationTransport.conjugateEquiv_toLinearMap]
    exact (LinearMap.det_conj φ.toLinearMap cmp).trans (congrArg LinearMap.det hφ)
  rw [hdet]
  have hNq : (2 : ℚ) * (Padic.valuation A.crystallineFrobenius.det : ℚ) =
      (Module.finrank ℚ_[q] A.Crystalline : ℚ) := by exact_mod_cast hN
  rw [hdim] at hNq
  linarith

theorem Geometry.AbelianH1Model.projective_native_lattice_admissibility
    [FiniteDimensional ℚ_[q] A.DeRham] [FiniteDimensional ℚ_[q] A.Crystalline]
    (hCompletion : Completion.GeometricWeightInput.{0})
    (j : K →+* ℂ)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q)
    (W : Polynomial ℤ) (hW : A.IsWeilPolynomial ℓ W)
    (hCW : A.crystallineFrobenius.charpoly = W.map (Int.castRingHom ℚ_[q]))
    (cmp : A.Crystalline ≃ₗ[ℚ_[q]] A.DeRham)
    (φ : A.Crystalline ≃ₗ[ℚ_[q]] A.Crystalline)
    (hφ : φ.toLinearMap = A.crystallineFrobenius)
    {M : Type*} [AddCommGroup M] [Module ℤ_[q] M]
    [Module.Free ℤ_[q] M] [Module.Finite ℤ_[q] M]
    [Module ℤ_[q] A.DeRham] [IsScalarTower ℤ_[q] ℚ_[q] A.DeRham]
    (f : M →ₗ[ℤ_[q]] A.DeRham) [IsLocalizedModule ℤ_[q]⁰ f]
    (F : Module.End ℤ_[q] M)
    (hcomm : ∀ x, f (F x) =
      WeakAdmissibilityTransport.FiltrationTransport.conjugateEquiv cmp φ (f x))
    (hdiv : ∀ x, f x ∈ A.Fil 1 → ∃ y, F x = (q : ℤ_[q]) • y) :
    Linear.WeaklyAdmissible q A.finiteFiltration (WeakAdmissibilityTransport.FiltrationTransport.conjugateEquiv cmp φ) := by
  have htotal := A.projective_hodge_newton_equality hCompletion j P ℓ hℓq W hW hCW cmp φ hφ
  exact StableLattice.StableLatticeAdmissibility.weaklyAdmissible q f F
    (WeakAdmissibilityTransport.FiltrationTransport.conjugateEquiv cmp φ) hcomm A.finiteFiltration
    (A.Fil_eq_top 0 le_rfl) (A.Fil_eq_bot 2 (by decide)) htotal hdiv

theorem Geometry.AbelianH1Model.projective_constructedComparison_weaklyAdmissible
    [FiniteDimensional ℚ_[q] A.DeRham] [FiniteDimensional ℚ_[q] A.Crystalline]
    (hCompletion : Completion.GeometricWeightInput.{0})
    (j : K →+* ℂ)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q)
    (W : Polynomial ℤ) (hW : A.IsWeilPolynomial ℓ W)
    (hCW : A.crystallineFrobenius.charpoly = W.map (Int.castRingHom ℚ_[q]))
    (φ : A.Crystalline ≃ₗ[ℚ_[q]] A.Crystalline)
    (hφ : φ.toLinearMap = A.crystallineFrobenius) :
    Linear.WeaklyAdmissible q A.finiteFiltration
      (WeakAdmissibilityTransport.FiltrationTransport.conjugateEquiv A.constructedCrystallineDeRhamEquiv φ) := by
  let := A.integral_deRham_hone_free
  let := A.integral_deRham_hone_finite
  have heq : A.constructedDeRhamFrobenius =
      (WeakAdmissibilityTransport.FiltrationTransport.conjugateEquiv A.constructedCrystallineDeRhamEquiv φ).toLinearMap := by
    rw [WeakAdmissibilityTransport.FiltrationTransport.conjugateEquiv_toLinearMap, hφ]
    rfl
  apply A.projective_native_lattice_admissibility hCompletion j P ℓ hℓq W hW hCW
    A.constructedCrystallineDeRhamEquiv φ hφ
    A.integralDeRhamInclusion A.constructedIntegralFrobenius
  · intro x
    exact (LinearMap.congr_fun A.constructedIntegralFrobenius_inclusion x).trans
      (LinearMap.congr_fun heq (A.integralDeRhamInclusion x))
  · exact A.constructedIntegralFrobenius_hodge_divisible

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
