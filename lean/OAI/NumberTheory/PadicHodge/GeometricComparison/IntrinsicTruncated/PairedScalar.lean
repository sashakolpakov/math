import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.PairedParameters
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.PointDataScalar

/-! # Paired Scalar -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The finite residue and the transported ordinary residue have the
same scalar, using the original paired chart and actual section equality. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} {A : Geometry.AbelianH1Model K q jq}
  {n m : ℕ} {hm : ¬q ∣ m}
attribute [local instance] MvPolynomial.gradedAlgebra Geometry.AbelianH1Model.finiteSection_closed
variable
  {U : (IntegralComparison.Projective.IntrinsicOverlap.Intrinsic.space (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedTraceDimension n+1)).Opens}
  {hU : IsAffineOpen U}
  {D : IntegralComparison.ProjectivePoint.PointParameterData.Chart.Data (A.truncatedModel n).scheme (A.truncatedTraceMorphism n)
    (A.truncatedIdentitySection n) A.dimension U hU}
  (P : A.TruncatedPairedPointParameters n m hm U hU D)

def Geometry.AbelianH1Model.TruncatedPairedPointParameters.finiteOriginal := A.truncatedFinitePointData n m hm (A.truncatedTraceMorphism n) A.dimension
  P.paired.ambient P.paired.affine P.paired.original

theorem Geometry.AbelianH1Model.TruncatedPairedPointParameters.finite_original_scalar (B : ℕ) (hB : A.truncatedTraceDimension n+2 ≤ B) :
    IntegralComparison.ProjectivePoint.DataScalar.rawValue (A.truncatedModel n).scheme (A.truncatedTraceMorphism n)
      (A.truncatedShiftIdentitySection n m hm ≫ A.truncatedShiftMap n m hm)
      (A.truncatedShiftTargetSection_over n m hm) A.dimension B hB
      P.paired.ambient P.paired.affine (Geometry.AbelianH1Model.TruncatedPairedPointParameters.finiteOriginal P) =
    IntegralComparison.ProjectivePoint.DataScalar.rawValue (A.truncatedModel n).scheme (A.truncatedTraceMorphism n)
      (A.truncatedIdentitySection n) (A.truncatedIdentitySection_over n) A.dimension B hB
      P.paired.ambient P.paired.affine P.paired.transported :=
  (A.truncatedFinitePointData_rawValue n m hm (A.truncatedTraceMorphism n) A.dimension B hB
    P.paired.ambient P.paired.affine P.paired.original).trans
      (IntegralComparison.ProjectivePoint.DataScalar.raw_independent (A.truncatedModel n).scheme
        (A.truncatedTraceMorphism n) (A.truncatedIdentitySection n) (A.truncatedIdentitySection_over n)
        A.dimension B hB P.paired.ambient P.paired.affine P.paired.original P.paired.transported
        P.paired.same_codimension P.paired.same_coordinate)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
