import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.PointClass
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.TraceEquiv

/-! # Point Normalization -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The actual scalar point class is the canonical trace-one element
of the original small-cover top-form cohomology. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

theorem Geometry.AbelianH1Model.truncatedSmallPointClass_normalized (n : ℕ) (hpos : 0 < A.dimension) :
    A.truncatedSmallPointClass n hpos = (A.truncatedSmallTopFormTraceEquiv n hpos).symm 1 := by
  apply (A.truncatedSmallTopFormTraceEquiv n hpos).injective
  exact (A.truncatedSmallPointClass_trace n hpos).trans
    ((A.truncatedSmallTopFormTraceEquiv n hpos).apply_symm_apply 1).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
