import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.PointedFrame
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.ClosedPoint
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PointedParameters

/-! # Pointed Parameters -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The actual pointed frame sends generators of the source identity ideal to generators of the target identity ideal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  (n m : ℕ) (hm : ¬q ∣ m)
  (U₁ : (A.truncatedShiftModel n m hm).left.affineOpens)
  (U₂ : (A.truncatedModel n).scheme.left.affineOpens)
  (h : A.truncatedShiftReduction n m hm ⁻¹ᵁ U₁.val = A.truncatedReduction n ⁻¹ᵁ U₂.val)
  (h₁ : ⊤ ≤ A.truncatedShiftIdentitySection n m hm ⁻¹ᵁ U₁.val)
  (h₂ : ⊤ ≤ A.truncatedIdentitySection n ⁻¹ᵁ U₂.val)

variable (g : ℕ) (b : Fin g → Γ((A.truncatedShiftModel n m hm).left, U₁.val))

def Geometry.AbelianH1Model.truncatedIdentityTransportedParameters : Fin g → Γ((A.truncatedModel n).scheme.left, U₂.val) :=
  fun i => (A.truncatedIdentityPointedFrameIso n m hm U₁ U₂ h h₁ h₂).hom.ambientMap (b i)

theorem Geometry.AbelianH1Model.truncatedIdentityTransportedParameters_span
    (hb : Ideal.span (Set.range b) = (A.truncatedShiftIdentitySection n m hm).ker.ideal U₁) :
    Ideal.span (Set.range (A.truncatedIdentityTransportedParameters n m hm U₁ U₂ h h₁ h₂ g b)) =
      (A.truncatedIdentitySection n).ker.ideal U₂ :=
  IntegralComparison.TruncatedModel.PointedParameters.span
    q (ZMod q) n (A.truncatedShiftModel n m hm) (A.truncatedModel n).scheme
    A.specialFiber.scheme (A.truncatedShiftReduction n m hm) (A.truncatedReduction n)
    (A.truncatedShiftModel_square n m hm) (A.truncatedReductionSquare n) U₁ U₂ h
    (A.truncatedShiftIdentitySection n m hm) (A.truncatedShiftIdentitySection_over n m hm)
    (A.truncatedIdentitySection n) (A.truncatedIdentitySection_over n)
    A.specialIdentitySection A.specialIdentitySection_over
    (A.truncatedShiftIdentitySection_reduction n m hm).symm
    (A.truncatedIdentitySection_reduction n) h₁ h₂ g b hb

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
