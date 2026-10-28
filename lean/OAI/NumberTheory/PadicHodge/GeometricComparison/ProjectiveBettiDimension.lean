import OAI.NumberTheory.PadicHodge.GeometricComparison.BettiGroupAction
import OAI.AlgebraicGeometry.AbelianVariety.BettiNumbers

/-! # Projective Betti Dimension -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The given complex projective fiber has the actual abelian Betti dimensions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  (j : K →+* ℂ)
  (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)

theorem Geometry.AbelianH1Model.projective_rationalBetti_finrank :
    Module.finrank ℚ (A.Betti j) = 2 * (A.complexAbelianVariety j P).variety.complexDimension :=
  AlgebraicGeometry.AbelianVariety.BettiNumbers.Constructions.ExteriorCohomology.abelian_h1_finrank (A.complexAbelianVariety j P)

theorem Geometry.AbelianH1Model.projective_complexBetti_finrank :
    Module.finrank ℂ (A.ComplexBetti j) = 2 * (A.complexAbelianVariety j P).variety.complexDimension := by
  exact (AlgebraicGeometry.AbelianVariety.BettiNumbers.Constructions.ExteriorCohomology.abelian_complex_betti_number (A.complexAbelianVariety j P) 1).trans
    (Nat.choose_one_right _)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
