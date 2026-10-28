import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.PointDataTransport
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.SectionTransportScalar
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.ClosedPoint

/-! # Point Data Scalar -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The scalar in the finite-shift residue uses the exact same original
point class and chart data as the ordinary target residue. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  (n m : ℕ) (hm : ¬q ∣ m) {N : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

local instance Geometry.AbelianH1Model.finiteSection_closed :
    IsClosedImmersion (A.truncatedShiftIdentitySection n m hm ≫ A.truncatedShiftMap n m hm) := by
  rw [A.truncatedShiftIdentitySection_map]
  infer_instance

theorem Geometry.AbelianH1Model.truncatedShiftTargetSection_over :
    (A.truncatedShiftIdentitySection n m hm ≫ A.truncatedShiftMap n m hm) ≫
      (A.truncatedModel n).scheme.hom = 𝟙 _ := by
  rw [A.truncatedShiftIdentitySection_map, A.truncatedIdentitySection_over]

variable (i : (A.truncatedModel n).scheme ⟶ IntegralComparison.Projective.IntrinsicOverlap.Intrinsic.model (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (N+1))
  [IsClosedImmersion i.left] (g B : ℕ) (hB : N+2 ≤ B)
  (U : (IntegralComparison.Projective.IntrinsicOverlap.Intrinsic.space (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (N+1)).Opens) (hU : IsAffineOpen U)
  (D : IntegralComparison.ProjectivePoint.PointParameterData.Chart.Data (A.truncatedModel n).scheme i (A.truncatedIdentitySection n) g U hU)

theorem Geometry.AbelianH1Model.truncatedFinitePointData_rawValue :
    IntegralComparison.ProjectivePoint.DataScalar.rawValue (A.truncatedModel n).scheme i
      (A.truncatedShiftIdentitySection n m hm ≫ A.truncatedShiftMap n m hm)
      (A.truncatedShiftTargetSection_over n m hm) g B hB U hU (A.truncatedFinitePointData n m hm i g U hU D) =
    IntegralComparison.ProjectivePoint.DataScalar.rawValue (A.truncatedModel n).scheme i
      (A.truncatedIdentitySection n) (A.truncatedIdentitySection_over n) g B hB U hU D :=
  IntegralComparison.ProjectivePoint.SectionTransportScalar.Data.rawValue_changeSection (A.truncatedModel n).scheme i
    (A.truncatedIdentitySection_over n) (A.truncatedShiftTargetSection_over n m hm) g B hB U hU
    (A.truncatedShiftIdentitySection_map n m hm).symm D

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
