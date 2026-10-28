import OAI.NumberTheory.PadicHodge.GeometricComparison.AbelianGlobalFilteredComparisons
import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.FiniteScalarExtension

/-! # Abelian De Rham Finite -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! Native algebraic and local de Rham finiteness follows from the actual fixed-complex comparison and genuine Betti finiteness. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  (hBettiComparison : Betti.ComparisonInput) (j : K →+* ℂ)
  (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)

include hBettiComparison j P in
theorem Geometry.AbelianH1Model.algebraicDeRham_finite_of_BettiComparison : FiniteDimensional K A.AlgebraicDeRham := by
  let : Algebra K ℂ := j.toAlgebra
  let : FiniteDimensional ℂ (A.ComplexBetti j) := A.complexBetti_finiteDimensional j P
  exact Finite.FiniteScalarExtension.ScalarExtension.finite_of_comparison K ℂ A.AlgebraicDeRham (A.algebraicBettiComparison hBettiComparison j)

include hBettiComparison j P in
theorem Geometry.AbelianH1Model.localDeRham_finite_of_BettiComparison : FiniteDimensional ℚ_[q] A.DeRham := by
  let : Algebra K ℚ_[q] := jq.toAlgebra
  let : FiniteDimensional K A.AlgebraicDeRham := A.algebraicDeRham_finite_of_BettiComparison hBettiComparison j P
  exact A.localAlgebraicComparison.finiteDimensional

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
