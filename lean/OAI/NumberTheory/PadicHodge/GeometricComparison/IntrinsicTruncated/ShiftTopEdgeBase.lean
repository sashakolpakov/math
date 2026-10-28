import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.ShiftCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTopEdgeBase

/-! # Shift Top Edge Base -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The original common-cover top-form groups and pullback for the
genuine finite étale lift of [m]+F. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  (n m : ℕ) (hm : ¬q ∣ m)

abbrev Geometry.AbelianH1Model.TruncatedShiftCommonTopForms :=
  IntegralComparison.TruncatedModel.MorphismTopEdgeBase.SourceTopForms q (ZMod q) n
    (A.truncatedShiftOver n m hm) A.dimension

def Geometry.AbelianH1Model.truncatedShiftCommonPullback : A.TruncatedSmallTopForms n →ₗ[IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n]
    A.TruncatedShiftCommonTopForms n m hm :=
  IntegralComparison.TruncatedModel.MorphismTopEdgeBase.pullback q (ZMod q) n
    (A.truncatedShiftOver n m hm) A.dimension

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
