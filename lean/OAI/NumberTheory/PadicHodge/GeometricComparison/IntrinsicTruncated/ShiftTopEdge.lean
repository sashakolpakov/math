import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.ShiftTopEdgeBase
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTopEdge

/-! # Shift Top Edge -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The genuine finite étale lift of [m]+F induces the original
bounded crystalline pullback through its common-cover top-form edge. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  (n m : ℕ) (hm : ¬q ∣ m)

def Geometry.AbelianH1Model.truncatedShiftSpecialOver : A.specialFiber.scheme ⟶ A.specialFiber.scheme :=
  ((m : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.specialFiber.scheme) +
    AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) A.specialFiber.scheme).toMul.hom.hom

def Geometry.AbelianH1Model.truncatedShiftCommonEdge : A.TruncatedShiftCommonTopForms n m hm →+
    A.NativeBoundedCrystallineCohomology n (A.dimension + A.dimension) :=
  IntegralComparison.TruncatedModel.MorphismTopEdge.sourceEdge q (ZMod q) n
    (A.truncatedShiftOver n m hm) (A.truncatedShiftReduction n m hm)
    (A.truncatedShiftModel_square n m hm) (injectiveResolution _) A.dimension

def Geometry.AbelianH1Model.truncatedShiftBoundedPullback (i : ℕ) :=
  IntegralComparison.BoundedCrystalline.CrystallinePullback.pullback (p := q)
    (J := Ideal.span {(q : WittVector q (ZMod q))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers q (ZMod q))
    (A.truncatedShiftSpecial m)
    (IntegralComparison.TruncatedModel.MorphismData.Frames.ambient_over q (ZMod q) (A.truncatedShiftSpecialOver m)) n i

abbrev Geometry.AbelianH1Model.truncatedShiftCommonSquare (x : A.TruncatedSmallTopForms n) :=
  IntegralComparison.TruncatedModel.MorphismTopEdge.square q (ZMod q) n
    (A.truncatedShiftOver n m hm) (A.truncatedShiftSpecialOver m)
    (A.truncatedShiftReduction n m hm) (A.truncatedReduction n)
    (A.truncatedShiftModel_square n m hm) (A.truncatedReductionSquare n)
    (A.truncatedShiftReduction_map n m hm)
    (injectiveResolution _) (injectiveResolution _) A.dimension x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
