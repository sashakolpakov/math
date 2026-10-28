import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.PairedScalar
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueScalarCompatibility

/-! # Paired Residue Scalar -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The actual scalar in both signed point residues has one common
Witt lift, without normalizing or cancelling that scalar. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
  (B : ℕ) (hB : A.truncatedTraceDimension n+2 ≤ B)

abbrev Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceResidueScalar : IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n :=
  IntegralComparison.ProjectivePoint.ResidueSingleCoordinates.rawValue (A.truncatedModel n).scheme
    (A.truncatedTraceMorphism n)
    (A.truncatedShiftIdentitySection n m hm ≫ A.truncatedShiftMap n m hm)
    (A.truncatedShiftTargetSection_over n m hm) B hB
    P.paired.ambient P.paired.affine P.finiteOriginal

abbrev Geometry.AbelianH1Model.TruncatedPairedPointParameters.targetResidueScalar : IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n :=
  IntegralComparison.ProjectivePoint.ResidueSingleCoordinates.rawValue (A.truncatedModel n).scheme
    (A.truncatedTraceMorphism n) (A.truncatedIdentitySection n) (A.truncatedIdentitySection_over n)
    B hB P.paired.ambient P.paired.affine P.paired.transported

theorem Geometry.AbelianH1Model.TruncatedPairedPointParameters.residueScalar_eq : Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceResidueScalar P B hB = Geometry.AbelianH1Model.TruncatedPairedPointParameters.targetResidueScalar P B hB :=
  (IntegralComparison.ProjectivePoint.ResidueScalarCompatibility.SingleCoordinates.rawValue_eq (A.truncatedModel n).scheme
    (A.truncatedTraceMorphism n)
    (A.truncatedShiftIdentitySection n m hm ≫ A.truncatedShiftMap n m hm)
    (A.truncatedShiftTargetSection_over n m hm) B hB
    P.paired.ambient P.paired.affine P.finiteOriginal).trans
      ((P.finite_original_scalar B hB).trans
        (IntegralComparison.ProjectivePoint.ResidueScalarCompatibility.SingleCoordinates.rawValue_eq (A.truncatedModel n).scheme
          (A.truncatedTraceMorphism n) (A.truncatedIdentitySection n) (A.truncatedIdentitySection_over n)
          B hB P.paired.ambient P.paired.affine P.paired.transported).symm)

theorem Geometry.AbelianH1Model.TruncatedPairedPointParameters.exists_commonResidueScalar : ∃ r : WittVector q (ZMod q),
    IntegralComparison.Truncated.Witt.quotient q (ZMod q) n r = Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceResidueScalar P B hB ∧
      IntegralComparison.Truncated.Witt.quotient q (ZMod q) n r = Geometry.AbelianH1Model.TruncatedPairedPointParameters.targetResidueScalar P B hB := by
  obtain ⟨r,hr⟩ := Ideal.Quotient.mk_surjective (Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceResidueScalar P B hB)
  exact ⟨r,hr,hr.trans (Geometry.AbelianH1Model.TruncatedPairedPointParameters.residueScalar_eq P B hB)⟩

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
