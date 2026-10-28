import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.RelativeDimensionUnique
import OAI.NumberTheory.PadicHodge.GeometricComparison.ProjectiveBettiDimension
import OAI.NumberTheory.PadicHodge.CrystallineDimension

/-! # Dimension -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The genuine complex and crystalline H1 dimensions are twice
the relative dimension of the original abelian scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  (j : K →+* ℂ)
  (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)

theorem Geometry.AbelianH1Model.complexAbelianVariety_dimension :
    (A.complexAbelianVariety j P).variety.complexDimension = A.dimension := by
  let V := (A.complexAbelianVariety j P).variety
  let : IsIntegral V.toOver.left := V.property
  let : SmoothOfRelativeDimension V.complexDimension V.structureMap :=
    V.smoothOfRelativeDimension_complexDimension
  let : SmoothOfRelativeDimension A.dimension V.structureMap :=
    (A.complexFiber j).smoothDimension
  exact IntegralComparison.Smooth.RelativeDimensionUnique.eq V.structureMap V.complexDimension A.dimension

include j P

theorem Geometry.AbelianH1Model.native_betti_finrank : Module.finrank ℚ (A.Betti j) = 2 * A.dimension := by
  rw [A.projective_rationalBetti_finrank j P, A.complexAbelianVariety_dimension j P]

theorem Geometry.AbelianH1Model.native_complexBetti_finrank : Module.finrank ℂ (A.ComplexBetti j) = 2 * A.dimension := by
  rw [A.projective_complexBetti_finrank j P, A.complexAbelianVariety_dimension j P]

theorem Geometry.AbelianH1Model.native_crystalline_finrank : Module.finrank ℚ_[q] A.Crystalline = 2 * A.dimension := by
  rw [CrystallineDimension.FrobeniusSlope.crystalline_finrank_eq_betti A j P,
    A.native_complexBetti_finrank j P]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
