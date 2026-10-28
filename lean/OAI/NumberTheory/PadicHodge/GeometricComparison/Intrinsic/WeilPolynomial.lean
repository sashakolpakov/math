import OAI.NumberTheory.PadicHodge.GeometricComparison.SpecialFiberProjectivity
import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.Shared

/-! # Weil Polynomial -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! IntegralComparison gives an integral polynomial shared by the original crystalline and rational pro-étale Frobenius maps, with special-fiber projectivity supplied by its actual geometry. -/

theorem Geometry.AbelianH1Model.native_sharedPolynomial_of_IntegralComparison
    {K : Type} [Field K] [NumberField K]
    {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
    (hIntegralComparison : Integral.Shared.CharpolyInput.{0}) (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) :
    ∃ hC : FiniteDimensional ℚ_[q] A.Crystalline,
      letI := hC
      ∃ P : Polynomial ℤ, A.IsWeilPolynomial ℓ P ∧
        A.crystallineFrobenius.charpoly = P.map (Int.castRingHom ℚ_[q]) :=
  A.sharedPolynomial_of_IntegralComparison hIntegralComparison A.specialFiber_projective ℓ hℓq

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
