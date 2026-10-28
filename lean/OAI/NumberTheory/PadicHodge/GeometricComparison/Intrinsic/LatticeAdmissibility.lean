import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.Newton
import OAI.NumberTheory.PadicHodge.GeometricComparison.StableLattice

/-! # Lattice Admissibility -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The actual native Hodge filtration is admissible once a geometrically justified comparison identifies a full integral Frobenius lattice with prime-divisible first Hodge step. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

theorem Geometry.AbelianH1Model.native_lattice_admissibility
    (hCohomology : Cohomology.Good.GoodReductionInput.{0}) (hCompletion : Completion.GeometricWeightInput.{0})
    (hIntegralComparison : Integral.Shared.CharpolyInput.{0}) (hBettiComparison : Betti.ComparisonInput)
    (j : K →+* ℂ)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q)
    (cmp : A.Crystalline ≃ₗ[ℚ_[q]] A.DeRham)
    {M : Type*} [AddCommGroup M] [Module ℤ_[q] M]
    [Module.Free ℤ_[q] M] [Module.Finite ℤ_[q] M]
    [Module ℤ_[q] A.DeRham] [IsScalarTower ℤ_[q] ℚ_[q] A.DeRham]
    (f : M →ₗ[ℤ_[q]] A.DeRham) [IsLocalizedModule ℤ_[q]⁰ f]
    (F : Module.End ℤ_[q] M)
    (hcomm : ∀ x, f (F x) =
      WeakAdmissibilityTransport.FiltrationTransport.conjugateEquiv cmp (A.crystallineFrobeniusEquiv hCohomology) (f x))
    (hdiv : ∀ x, f x ∈ A.Fil 1 → ∃ y, F x = (q : ℤ_[q]) • y) :
    letI : FiniteDimensional ℚ_[q] A.DeRham := A.deRham_finite_of_Cohomology hCohomology
    Linear.WeaklyAdmissible q A.finiteFiltration
      (WeakAdmissibilityTransport.FiltrationTransport.conjugateEquiv cmp (A.crystallineFrobeniusEquiv hCohomology)) := by
  let : FiniteDimensional ℚ_[q] A.DeRham := A.deRham_finite_of_Cohomology hCohomology
  let φ := A.crystallineFrobeniusEquiv hCohomology
  have hd (e : A.Crystalline ≃ₗ[ℚ_[q]] A.DeRham) :
      (WeakAdmissibilityTransport.FiltrationTransport.conjugateEquiv e φ).toLinearMap.det = φ.toLinearMap.det := by
    rw [WeakAdmissibilityTransport.FiltrationTransport.conjugateEquiv_toLinearMap]
    exact LinearMap.det_conj φ.toLinearMap e
  have ht := A.native_geometric_hodge_newton_equality hCohomology hCompletion hIntegralComparison hBettiComparison j P ℓ hℓq
  change A.finiteFiltration.tH =
    (Padic.valuation (WeakAdmissibilityTransport.FiltrationTransport.conjugateEquiv (A.crystallineDeRhamEquiv hCohomology) φ).toLinearMap.det : ℚ) at ht
  have htotal : A.finiteFiltration.tH =
      (Padic.valuation (WeakAdmissibilityTransport.FiltrationTransport.conjugateEquiv cmp φ).toLinearMap.det : ℚ) := by
    rw [hd] at ht ⊢
    exact ht
  exact StableLattice.StableLatticeAdmissibility.weaklyAdmissible q f F
    (WeakAdmissibilityTransport.FiltrationTransport.conjugateEquiv cmp φ) hcomm A.finiteFiltration
    (A.Fil_eq_top 0 le_rfl) (A.Fil_eq_bot 2 (by decide)) htotal hdiv

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
