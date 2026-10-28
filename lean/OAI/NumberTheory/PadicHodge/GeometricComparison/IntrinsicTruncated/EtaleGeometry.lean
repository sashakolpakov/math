import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.EtaleLift
import OAI.NumberTheory.PadicHodge.IntegralComparison.NilpotentGeometricConnectedness

/-! # Etale Geometry -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The genuine lifted source has the original abelian relative
dimension and geometrically connected fibers over the truncated base. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  (n m : ℕ) (hm : ¬q ∣ m)

instance Geometry.AbelianH1Model.truncatedShiftModel_relativeDimension :
    SmoothOfRelativeDimension A.dimension (A.truncatedShiftModel n m hm).hom := by
  change SmoothOfRelativeDimension A.dimension
    (A.truncatedShiftMap n m hm ≫ (A.truncatedModel n).scheme.hom)
  simpa only [Nat.zero_add] using
    (inferInstance : SmoothOfRelativeDimension (0 + A.dimension)
      (A.truncatedShiftMap n m hm ≫ (A.truncatedModel n).scheme.hom))

instance Geometry.AbelianH1Model.truncatedShiftModel_geometricallyConnected :
    GeometricallyConnected (A.truncatedShiftModel n m hm).hom :=
  IntegralComparison.NilpotentGeometricConnectedness.connected (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.reduction q n)
    (IntegralComparison.Truncated.Witt.reduction_surjective q (ZMod q) n)
    (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.kernel_nilpotent q n) (A.truncatedShiftModel n m hm).hom
    A.specialFiber.scheme.hom (A.truncatedShiftReduction n m hm) (A.truncatedShiftModel_square n m hm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
