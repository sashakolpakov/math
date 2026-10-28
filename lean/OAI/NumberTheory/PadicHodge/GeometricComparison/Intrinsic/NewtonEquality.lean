import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.HalfDimension
import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.PolynomialWeights
import OAI.NumberTheory.PadicHodge.GeometricComparison.WeilDeterminantNorm
import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.HeckeFrobenius

/-! # Newton Equality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! A shared native Weil polynomial gives equality of the total geometric Hodge number and the original crystalline Frobenius valuation. The stable-subspace inequalities remain a separate obligation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  [FiniteDimensional ℚ_[q] A.DeRham] [FiniteDimensional ℚ_[q] A.Crystalline]

theorem Geometry.AbelianH1Model.native_hodge_newton_equality
    (hCohomology : Cohomology.Good.GoodReductionInput.{0}) (hCompletion : Completion.GeometricWeightInput.{0})
    (hBettiComparison : Betti.ComparisonInput) (j : K →+* ℂ)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q)
    (W : Polynomial ℤ) (hW : A.IsWeilPolynomial ℓ W)
    (hC : A.crystallineFrobenius.charpoly = W.map (Int.castRingHom ℚ_[q])) :
    A.finiteFiltration.tH = (Padic.valuation (A.deRhamFrobeniusEquiv hCohomology).toLinearMap.det : ℚ) := by
  have hH := A.native_hodge_number_twice hBettiComparison j P
  have hN := WeilDeterminantNorm.WeilDeterminant.determinant_valuation_twice q A.crystallineFrobenius W hC
    (A.native_polynomial_weights hCompletion ℓ hℓq W hW)
  have hdim := (A.crystallineDeRhamEquiv hCohomology).finrank_eq
  have hdet : (A.deRhamFrobeniusEquiv hCohomology).toLinearMap.det = A.crystallineFrobenius.det := by
    rw [Geometry.AbelianH1Model.deRhamFrobeniusEquiv, WeakAdmissibilityTransport.FiltrationTransport.conjugateEquiv_toLinearMap]
    exact (LinearMap.det_conj (A.crystallineFrobeniusEquiv hCohomology).toLinearMap
      (A.crystallineDeRhamEquiv hCohomology)).trans
        (congrArg LinearMap.det (A.crystallineFrobeniusEquiv_toLinearMap hCohomology))
  rw [hdet]
  have hNq : (2 : ℚ) * (Padic.valuation A.crystallineFrobenius.det : ℚ) =
      (Module.finrank ℚ_[q] A.Crystalline : ℚ) := by exact_mod_cast hN
  rw [hdim] at hNq
  linarith

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
