import OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineOpenDifferential

/-! # Open Chart Dimension -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Affine.OpenChartDimension

noncomputable section

/-! An actual affine open chart has precisely the native dimension of its smooth integral scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold

theorem affineOpen_genericDifferentialRank_eq
    (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    (A : CommAlgCat ℂ) [IsDomain A] [Algebra.Smooth ℂ A]
    (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) [IsOpenImmersion i.left] (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A = Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom := by
  let L := mfderiv (𝓘(ℂ, Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ))
    (𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ))
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i) x
  have hL : Function.Bijective L := ComplexPoints.Analytic.AffineOpenDifferential.mfderiv_affinePointMap_bijective A i x
  have hd := (LinearEquiv.ofBijective L.toLinearMap hL).finrank_eq
  change Module.finrank ℂ (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ) =
    Module.finrank ℂ (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) at hd
  simpa using hd

end

end OAI.AlgebraicGeometry.Comparison.Betti.Affine.OpenChartDimension
