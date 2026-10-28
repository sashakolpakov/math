import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.ClosedPoint
import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SectionPuncture
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedSection

/-! # Point Support -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! Both actual identity sections define the same punctured open
of the original special fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

theorem Geometry.AbelianH1Model.truncatedIdentityPuncture (n : ℕ) :
    IntegralComparison.TruncatedModel.SupportedSection.punctured q (ZMod q) n (A.truncatedModel n).scheme
      A.specialFiber.scheme (A.truncatedReduction n) (A.truncatedIdentitySection n) =
        IntegralComparison.SectionIdealPuncturedCover.outside A.specialIdentitySection.ker :=
  IntegralComparison.Truncated.SectionPuncture.outside q (ZMod q) n (A.truncatedModel n).scheme
    A.specialFiber.scheme (A.truncatedReduction n) (A.truncatedReductionSquare n)
    (A.truncatedIdentitySection n) A.specialIdentitySection (A.truncatedIdentitySection_reduction n)

theorem Geometry.AbelianH1Model.truncatedShiftIdentityPuncture (n m : ℕ) (hm : ¬q ∣ m) :
    IntegralComparison.TruncatedModel.SupportedSection.punctured q (ZMod q) n (A.truncatedShiftModel n m hm)
      A.specialFiber.scheme (A.truncatedShiftReduction n m hm) (A.truncatedShiftIdentitySection n m hm) =
        IntegralComparison.SectionIdealPuncturedCover.outside A.specialIdentitySection.ker :=
  IntegralComparison.Truncated.SectionPuncture.outside q (ZMod q) n (A.truncatedShiftModel n m hm)
    A.specialFiber.scheme (A.truncatedShiftReduction n m hm) (A.truncatedShiftModel_square n m hm)
    (A.truncatedShiftIdentitySection n m hm) A.specialIdentitySection
    (A.truncatedShiftIdentitySection_reduction n m hm).symm

theorem Geometry.AbelianH1Model.truncatedIdentityPuncture_eq (n m : ℕ) (hm : ¬q ∣ m) :
    IntegralComparison.TruncatedModel.SupportedSection.punctured q (ZMod q) n (A.truncatedShiftModel n m hm)
      A.specialFiber.scheme (A.truncatedShiftReduction n m hm) (A.truncatedShiftIdentitySection n m hm) =
    IntegralComparison.TruncatedModel.SupportedSection.punctured q (ZMod q) n (A.truncatedModel n).scheme
      A.specialFiber.scheme (A.truncatedReduction n) (A.truncatedIdentitySection n) :=
  (A.truncatedShiftIdentityPuncture n m hm).trans (A.truncatedIdentityPuncture n).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
