import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.ShiftTopEdge
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.TraceEquiv
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.TraceCyclic

/-! # Scalar Criterion -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! A common normalized point class and the actual top-form trace
degree formula determine the original bounded crystalline action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

theorem Geometry.AbelianH1Model.truncatedShiftBounded_scalar_of_normalized_point
    (n m : ℕ) (hm : ¬q ∣ m) (hpos : 0 < A.dimension) (d : ℕ)
    (t : A.TruncatedShiftCommonTopForms n m hm ≃+
      IntegralComparison.Projective.TopTracePairing.coefficientRing (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n))
    (hpoint : A.truncatedShiftCommonEdge n m hm (t.symm 1) =
      A.truncatedCrystallineTopEdge n ((A.truncatedSmallTopFormTraceEquiv n hpos).symm 1))
    (htrace : ∀ x : A.TruncatedSmallTopForms n,
      t (A.truncatedShiftCommonPullback n m hm x) =
        d • A.truncatedSmallTopFormTrace n hpos x)
    (x : A.NativeBoundedCrystallineCohomology n (A.dimension + A.dimension)) :
    A.truncatedShiftBoundedPullback n m (A.dimension + A.dimension) x = d • x := by
  exact IntegralComparison.NormalizedTopEdgeScalar.scalar_of_generator
    (A.truncatedShiftCommonEdge n m hm) (A.truncatedCrystallineTopEdge n)
    t (A.truncatedSmallTopFormTraceEquiv n hpos)
    (A.truncatedShiftBoundedPullback n m (A.dimension + A.dimension)).toAddMonoidHom
    (A.truncatedShiftCommonPullback n m hm).toAddMonoidHom d
    (A.truncatedCrystallineTopEdge_surjective n) 1
    (IntrinsicTruncated.TraceCyclic.IntrinsicTruncatedBase.traceCoefficient_generated_by_one q n) hpoint htrace
    (A.truncatedShiftCommonSquare n m hm) x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
