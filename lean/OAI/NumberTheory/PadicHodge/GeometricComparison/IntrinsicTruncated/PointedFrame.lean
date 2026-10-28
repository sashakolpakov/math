import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.CommonPointNeighborhood
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PointedLocalEquiv

/-! # Pointed Frame -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The actual finite étale source and fixed truncated model admit
a crystalline frame isomorphism preserving their identity sections. -/

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

def Geometry.AbelianH1Model.truncatedIdentityPointedFrameIso := IntegralComparison.TruncatedModel.PointedLocalEquiv.frameIso
  q (ZMod q) n (A.truncatedShiftModel n m hm) (A.truncatedModel n).scheme
  A.specialFiber.scheme (A.truncatedShiftReduction n m hm) (A.truncatedReduction n)
  (A.truncatedShiftModel_square n m hm) (A.truncatedReductionSquare n) U₁ U₂ h
  (A.truncatedShiftIdentitySection n m hm) (A.truncatedShiftIdentitySection_over n m hm)
  (A.truncatedIdentitySection n) (A.truncatedIdentitySection_over n)
  A.specialIdentitySection A.specialIdentitySection_over
  (A.truncatedShiftIdentitySection_reduction n m hm).symm
  (A.truncatedIdentitySection_reduction n) h₁ h₂

theorem Geometry.AbelianH1Model.truncatedIdentityPointedFrameIso_section
    (a : Γ((A.truncatedShiftModel n m hm).left, U₁.val)) :
    IntegralComparison.Intrinsic.SectionEvaluation.evaluation (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
      (A.truncatedModel n).scheme (A.truncatedIdentitySection n) (A.truncatedIdentitySection_over n)
      U₂.val h₂ ((A.truncatedIdentityPointedFrameIso n m hm U₁ U₂ h h₁ h₂).hom.ambientMap a) =
    IntegralComparison.Intrinsic.SectionEvaluation.evaluation (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
      (A.truncatedShiftModel n m hm) (A.truncatedShiftIdentitySection n m hm)
      (A.truncatedShiftIdentitySection_over n m hm) U₁.val h₁ a :=
  IntegralComparison.TruncatedModel.PointedLocalEquiv.frameIso_section
    q (ZMod q) n (A.truncatedShiftModel n m hm) (A.truncatedModel n).scheme
    A.specialFiber.scheme (A.truncatedShiftReduction n m hm) (A.truncatedReduction n)
    (A.truncatedShiftModel_square n m hm) (A.truncatedReductionSquare n) U₁ U₂ h
    (A.truncatedShiftIdentitySection n m hm) (A.truncatedShiftIdentitySection_over n m hm)
    (A.truncatedIdentitySection n) (A.truncatedIdentitySection_over n)
    A.specialIdentitySection A.specialIdentitySection_over
    (A.truncatedShiftIdentitySection_reduction n m hm).symm
    (A.truncatedIdentitySection_reduction n) h₁ h₂ a

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
