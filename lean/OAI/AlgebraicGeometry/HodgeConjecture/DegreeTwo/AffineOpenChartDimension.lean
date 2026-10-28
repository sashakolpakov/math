import OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineOpenDifferential

/-! # Affine Open Chart Dimension -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AffineOpenChartDimension.Constructions

noncomputable section

/-!
# DegreeTwo: affine-open regular charts in the native scheme dimension

The already-proved bijective differential of the actual affine open
immersion identifies the two native model dimensions.
-/

open scoped ContDiff _root_.Manifold
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineOpenDifferential

variable {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  (A : CommAlgCat ℂ) [IsDomain A] [Algebra.Smooth ℂ A]
  (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) [IsOpenImmersion i.left]

include i

/-- The actual affine-open differential proves equality of its affine
generic rank and the native scheme model dimension. -/
theorem affineOpen_genericRank_eq_nativeDimension (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A = Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom := by
  let D := mfderiv 𝓘(ℂ, Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ)
    𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i) x
  let e := LinearEquiv.ofBijective D.toLinearMap (ComplexPoints.Analytic.AffineOpenDifferential.mfderiv_affinePointMap_bijective A i x)
  have hd := e.finrank_eq
  change Module.finrank ℂ (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ) =
    Module.finrank ℂ (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) at hd
  simpa using hd

/-- Any point of the chosen affine open admits an actual regular chart
of the fixed dimension of the native target scheme manifold. -/
theorem exists_affineOpen_regularChart_nativeDimension (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    ∃ e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A)
      (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ),
      e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) ∧ x ∈ e.source := by
  have h := ComplexPoints.Analytic.SmoothSchemeManifold.exists_smoothDomain_affineRegularChart x
  exact (congrArg (fun d => ∃ e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin d → ℂ),
    e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A d ∧ x ∈ e.source)
      (affineOpen_genericRank_eq_nativeDimension A i x)).mp h

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AffineOpenChartDimension.Constructions
