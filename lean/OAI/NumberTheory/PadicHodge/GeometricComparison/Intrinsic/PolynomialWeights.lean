import OAI.NumberTheory.PadicHodge.GeometricComparison.Rational
import OAI.NumberTheory.PadicHodge.GeometricComparison.Completion
import OAI.NumberTheory.PadicHodge.GeometricComparison.CharpolyIntertwiningCore
import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-! # Polynomial Weights -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! Completion bounds every complex root of the original IntegralComparison characteristic polynomial, using the actual rationalization and Frobenius comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.IntegralComparison.Cohomology OAI.NumberTheory.PadicHodge.GeometricComparison.Rational.GeometricRationalComparison

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

theorem Geometry.AbelianH1Model.native_polynomial_weights (hCompletion : Completion.GeometricWeightInput.{0})
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (P : Polynomial ℤ)
    (hP : A.IsWeilPolynomial ℓ P) (z : ℂ) (hz : Polynomial.aeval z P = 0) :
    ‖z‖ = Real.sqrt (q : ℝ) := by
  obtain ⟨hfin, hchar⟩ := hP
  let : FiniteDimensional ℚ_[ℓ] (A.Etale ℓ) := hfin
  let X := AlgebraicGeometry.FormalGeometry.Completion.Cohomology.Construction.geometricFiber A.specialFiber.scheme
  let : FiniteDimensional ℚ_[ℓ] (IntegralComparison.Cohomology.RationalEllAdicCohomology ℓ X 1) := hfin
  let e := AlgebraicRational.RationalProEtaleCoefficients.algebraicH1Equiv ℓ X
  let : FiniteDimensional (AlgebraicClosure ℚ_[ℓ]) (AlgebraicRational.RationalProEtaleCoefficients.AlgebraicRationalH1 ℓ X) := by
    change FiniteDimensional (AlgebraicClosure ℚ_[ℓ])
      ((AlgebraicClosure ℚ_[ℓ]) ⊗[ℚ_[ℓ]] IntegralComparison.Cohomology.RationalEllAdicCohomology ℓ X 1)
    infer_instance
  let : FiniteDimensional (AlgebraicClosure ℚ_[ℓ]) (AlgebraicGeometry.FormalGeometry.Completion.Cohomology.Construction.GeometricH1 ℓ A.specialFiber.scheme) :=
    Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  let F := (A.etaleFrobenius ℓ).toLinearMap
  have he := Rational.GeometricRationalComparison.geometricFrobenius_compare q A.specialFiber.scheme ℓ
  have hc : (AlgebraicGeometry.FormalGeometry.Completion.CohomologyPullback.Construction.geometricH1Frobenius ℓ (ZMod q) A.specialFiber.scheme).charpoly =
      P.map (Int.castRingHom (AlgebraicClosure ℚ_[ℓ])) := by
    rw [CharpolyIntertwiningCore.CharpolyIntertwining.charpoly e _ (F.baseChange (AlgebraicClosure ℚ_[ℓ])) he]
    erw [LinearMap.charpoly_baseChange]
    change F.charpoly = P.map (Int.castRingHom ℚ_[ℓ]) at hchar
    rw [hchar, Polynomial.map_map]
    congr 1
  exact A.specialFiber_integral_polynomial_weights hCompletion ℓ hℓq P hc z hz

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
