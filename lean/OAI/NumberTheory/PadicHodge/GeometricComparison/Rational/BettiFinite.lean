import OAI.NumberTheory.PadicHodge.GeometricComparison.BettiFinite
import OAI.NumberTheory.PadicHodge.GeometricComparison.SingularFiniteDescent

/-! # Betti Finite -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! Finite-dimensionality of the actual rational Betti group of the fixed projective complex fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

theorem Geometry.AbelianH1Model.rationalBetti_finiteDimensional (j : K →+* ℂ)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom) :
    FiniteDimensional ℚ (A.Betti j) := by
  let : FiniteDimensional ℂ (A.ComplexBetti j) := A.complexBetti_finiteDimensional j P
  exact SingularFiniteDescent.SingularFiniteness.cohomology_descends ℚ ℂ (AlgebraicGeometry.Betti.Scheme.schemePointSpace (A.complexFiber j).scheme) 1

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
