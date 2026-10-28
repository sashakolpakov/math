import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.SmallTrace

/-! # Trace Equiv -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The original native small top-form trace as its canonical additive equivalence. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

def Geometry.AbelianH1Model.truncatedSmallTopFormTraceEquiv (n : ℕ) (hpos : 0 < A.dimension) :
    A.TruncatedSmallTopForms n ≃+
      IntegralComparison.Projective.TopTracePairing.coefficientRing (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) :=
  AddEquiv.ofBijective (A.truncatedSmallTopFormTrace n hpos)
    (A.truncatedSmallTopFormTrace_bijective n hpos)

@[simp] theorem Geometry.AbelianH1Model.truncatedSmallTopFormTraceEquiv_apply (n : ℕ) (hpos : 0 < A.dimension)
    (x : A.TruncatedSmallTopForms n) :
    A.truncatedSmallTopFormTraceEquiv n hpos x = A.truncatedSmallTopFormTrace n hpos x := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
