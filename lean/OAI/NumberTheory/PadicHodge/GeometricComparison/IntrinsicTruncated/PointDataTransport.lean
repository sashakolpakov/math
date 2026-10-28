import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.ClosedPoint
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.SectionTransport

/-! # Point Data Transport -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The finite-shift identity has exactly the original point data after
transport along its actual equality with the target identity section. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  (n m : ℕ) (hm : ¬q ∣ m) {N : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (i : (A.truncatedModel n).scheme ⟶ IntegralComparison.Projective.IntrinsicOverlap.Intrinsic.model (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) N)
  (g : ℕ)
  (U : (IntegralComparison.Projective.IntrinsicOverlap.Intrinsic.space (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) N).Opens) (hU : IsAffineOpen U)
  (D : IntegralComparison.ProjectivePoint.PointParameterData.Chart.Data (A.truncatedModel n).scheme i (A.truncatedIdentitySection n) g U hU)

def Geometry.AbelianH1Model.truncatedFinitePointData :
    IntegralComparison.ProjectivePoint.PointParameterData.Chart.Data (A.truncatedModel n).scheme i
      (A.truncatedShiftIdentitySection n m hm ≫ A.truncatedShiftMap n m hm) g U hU :=
  D.changeSection (A.truncatedModel n).scheme i g U hU
    (A.truncatedShiftIdentitySection_map n m hm).symm

@[simp] theorem Geometry.AbelianH1Model.truncatedFinitePointData_codimension :
    (A.truncatedFinitePointData n m hm i g U hU D).codimension = D.codimension := rfl

@[simp] theorem Geometry.AbelianH1Model.truncatedFinitePointData_coordinate :
    (A.truncatedFinitePointData n m hm i g U hU D).coordinate = D.coordinate := rfl

@[simp] theorem Geometry.AbelianH1Model.truncatedFinitePointData_equations :
    (A.truncatedFinitePointData n m hm i g U hU D).equations = D.equations := rfl

@[simp] theorem Geometry.AbelianH1Model.truncatedFinitePointData_parameters :
    (A.truncatedFinitePointData n m hm i g U hU D).parameters = D.parameters := rfl

@[simp] theorem Geometry.AbelianH1Model.truncatedFinitePointData_ambientBasis :
    (A.truncatedFinitePointData n m hm i g U hU D).ambientBasis = D.ambientBasis := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
