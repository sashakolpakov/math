import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicConstructed.FrobeniusDivisibility
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicConstructed.FrobeniusEquiv
import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.LatticeAdmissibility

/-! # Admissibility -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The constructed crystalline comparison gives weak admissibility of
the original native Hodge filtration through its actual integral lattice. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

theorem Geometry.AbelianH1Model.constructedComparison_weaklyAdmissible
    (hCohomology : Cohomology.Good.GoodReductionInput.{0}) (hCompletion : Completion.GeometricWeightInput.{0})
    (hIntegralComparison : Integral.Shared.CharpolyInput.{0}) (hBettiComparison : Betti.ComparisonInput)
    (j : K →+* ℂ)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) :
    letI : FiniteDimensional ℚ_[q] A.DeRham := A.deRham_finite_of_Cohomology hCohomology
    Linear.WeaklyAdmissible q A.finiteFiltration
      (WeakAdmissibilityTransport.FiltrationTransport.conjugateEquiv A.constructedCrystallineDeRhamEquiv
        (A.crystallineFrobeniusEquiv hCohomology)) := by
  let := A.integral_deRham_hone_free
  let := A.integral_deRham_hone_finite
  exact A.native_lattice_admissibility hCohomology hCompletion hIntegralComparison hBettiComparison j P ℓ hℓq
    A.constructedCrystallineDeRhamEquiv A.integralDeRhamInclusion A.constructedIntegralFrobenius
    (A.constructedIntegralFrobenius_inclusion_equiv hCohomology)
    A.constructedIntegralFrobenius_hodge_divisible

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
