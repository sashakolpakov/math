import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.PointValueEdges
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.PointValueEquality
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.PointNormalization
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.ShiftPointClass

/-! # Normalized Points -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.NormalizedPoints.AbelianModel

noncomputable section

/-! Equality of the two original point values identifies the
trace-normalized point classes under the original crystalline edges. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

private theorem cancel_point_sign {M : Type u} [AddCommGroup M]
    (s : ℤˣ) {x y : M} (h : s • x = s • y) : x = y := by
  have hi := congrArg (fun z => s⁻¹ • z) h
  simpa only [inv_smul_smul] using hi

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.truncatedPointClass_edges (n m : ℕ) (hm : ¬q ∣ m)
    (hpos : 0 < A.dimension) :
    A.truncatedShiftCommonEdge n m hm (A.truncatedShiftPointClass n m hm hpos) =
      A.truncatedCrystallineTopEdge n (A.truncatedSmallPointClass n hpos) := by
  have h := A.truncatedPointValue_equality n m hm
  rw [A.truncatedFinitePointValue_eq n m hm hpos,
    A.truncatedOrdinaryPointValue_eq n hpos] at h
  exact cancel_point_sign _ h

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.truncatedNormalizedPointEquality (n m : ℕ) (hm : ¬q ∣ m)
    (hpos : 0 < A.dimension) :
    A.truncatedShiftCommonEdge n m hm
        ((A.truncatedShiftCommonTraceEquiv n m hm hpos).symm 1) =
      A.truncatedCrystallineTopEdge n
        ((A.truncatedSmallTopFormTraceEquiv n hpos).symm 1) := by
  simpa only [A.truncatedShiftPointClass_normalized n m hm hpos,
    A.truncatedSmallPointClass_normalized n hpos] using
      A.truncatedPointClass_edges n m hm hpos

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.NormalizedPoints.AbelianModel
