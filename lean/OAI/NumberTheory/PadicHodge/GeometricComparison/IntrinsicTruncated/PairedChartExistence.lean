import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.PairedParameters
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ChartExistence

/-! # Paired Chart Existence -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The paired native point charts are obtained from the original
abelian model and finite shift, with all initial chart data derived. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ChartExistence.Parameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  (n m : ℕ) (hm : ¬q ∣ m)
attribute [local instance] MvPolynomial.gradedAlgebra

theorem Geometry.AbelianH1Model.exists_truncatedPairedPointChart :
    ∃ (U : (IntegralComparison.Projective.IntrinsicOverlap.Intrinsic.space (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedTraceDimension n+1)).Opens)
      (hU : IsAffineOpen U)
      (D : IntegralComparison.ProjectivePoint.PointParameterData.Chart.Data (A.truncatedModel n).scheme (A.truncatedTraceMorphism n)
        (A.truncatedIdentitySection n) A.dimension U hU),
      IntegralComparison.FiniteEtale.TraceBasis.Good (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
        (A.truncatedShiftModel n m hm) (A.truncatedModel n).scheme (A.truncatedShiftOver n m hm)
        ((A.truncatedTraceMorphism n).left ⁻¹ᵁ U) ∧
      Nonempty (A.TruncatedPairedPointParameters n m hm U hU D) := by
  let : IsFinite (A.truncatedShiftOver n m hm).left := A.truncatedShiftMap_finite n m hm
  let : AlgebraicGeometry.Etale (A.truncatedShiftOver n m hm).left := A.truncatedShiftMap_etale n m hm
  obtain ⟨U,hU,_,hgood,⟨D⟩⟩ := IntegralComparison.ProjectivePoint.ChartExistence.Parameter.exists_finite_chart
    (A.truncatedModel n).scheme (A.truncatedTraceMorphism n)
    (A.truncatedIdentitySection n) (A.truncatedIdentitySection_over n) A.dimension ⊤ (by simp)
    (A.truncatedShiftModel n m hm) (A.truncatedShiftOver n m hm)
  exact ⟨U,hU,D,hgood,A.exists_truncatedPairedPointParameters n m hm U hU D hgood⟩

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
