import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.PointValueTraceCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SmoothPointValue
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.ClosedPoint

/-! # Point Ordinary Value Formula -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.PointOrdinaryValueFormula.Ordinary

noncomputable section

/-! The original ordinary point value expressed by the local fraction
on any affine neighborhood of its whole identity section. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomologicalComplex
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : GeometricComparison.Geometry.AbelianH1Model K q jq) (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra
variable (U : (Projective.IntrinsicOverlap.Intrinsic.space (GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedTraceDimension n+1)).Opens)
  (hU : IsAffineOpen U)
  (D : ProjectivePoint.PointParameterData.Chart.Data (A.truncatedModel n).scheme (A.truncatedTraceMorphism n)
    (A.truncatedIdentitySection n) A.dimension U hU)
  (V : (A.truncatedModel n).scheme.left.affineOpens)
  (hVU : V.val ≤ (A.truncatedTraceMorphism n).left ⁻¹ᵁ U)
  (hcontains : ⊤ ≤ (A.truncatedIdentitySection n) ⁻¹ᵁ V.val)
  (r : WittVector q (ZMod q))
  (hr : Witt.quotient q (ZMod q) n r =
    Projective.FormFraction.rawValue q (ZMod q) n
      (A.truncatedModel n).scheme (A.truncatedTraceMorphism n)
      (A.truncatedIdentitySection n) (A.truncatedIdentitySection_over n)
      (A.truncatedTraceDimension n+2) le_rfl U hU D)

abbrev residue := TruncatedModel.SmoothPointValueData.residue q (ZMod q) n
  (A.truncatedModel n).scheme (A.truncatedTraceMorphism n) (A.truncatedIdentitySection n)
  U hU D A.specialFiber.scheme (A.truncatedReduction n) (A.truncatedReductionSquare n)
  (A.truncatedPointValueResolution n) V hVU hcontains

attribute [local irreducible] HomologicalComplex.homology Intrinsic.TopFormTrace.serreIso

include hr in
theorem comparison : A.truncatedOrdinaryPointValue n =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) D.codimension A.dimension •
      (ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) A.dimension A.dimension •
        ((⟨r⟩ : Crystalline.ExactRestriction.Coeff (B := WittVector q (ZMod q))) •
          residue A n U hU D V hVU hcontains)) := by
  have h := TruncatedModel.SmoothPointValue.global_fraction q (ZMod q) n
    (A.truncatedModel n).scheme (A.truncatedTraceMorphism n)
    (A.truncatedIdentitySection n) (A.truncatedIdentitySection_over n)
    (A.truncatedTraceDimension n+2) le_rfl U hU D A.specialFiber.scheme
    (A.truncatedReduction n) (A.truncatedReductionSquare n)
    (A.truncatedPointValueResolution n) V hVU hcontains r hr
  refine (PointValueTraceCoordinates.ordinary A n).symm.trans ?_
  dsimp only [PointValueTraceCoordinates.ordinaryValue,
    PointValueTraceCoordinates.ordinaryGlobalMap, residue]
  dsimp only [TruncatedModel.SmoothPointValueData.cover,
    TruncatedModel.SmoothPointValueData.coverFull] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.PointOrdinaryValueFormula.Ordinary
