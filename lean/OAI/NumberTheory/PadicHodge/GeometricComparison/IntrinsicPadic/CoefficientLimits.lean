import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient

/-! # Coefficient Limits -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CoefficientLimits.IntrinsicPadicCoefficientLimits

noncomputable section

/-! The actual crystalline coefficient transport preserves small limits,
including the countable inverse limit of finite-level cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable (p : ℕ) [Fact p.Prime]

instance preservesLimits : PreservesLimitsOfSize.{0, 0} (Coefficient.IntrinsicPadicSmallQuotientTotal.coefficients p) := by
  let : PreservesLimitsOfSize.{0, 0} (ModuleCat.uliftFunctor.{2, 1}
      (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p)))) :=
    preservesSmallestLimits_of_preservesLimits _
  dsimp only [Coefficient.IntrinsicPadicSmallQuotientTotal.coefficients, IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.coefficients]
  infer_instance

def iso {J : Type} [SmallCategory J] (F : J ⥤ ModuleCat.{0} ℤ_[p]) :
    (Coefficient.IntrinsicPadicSmallQuotientTotal.coefficients p).obj (limit F) ≅
      limit (F ⋙ Coefficient.IntrinsicPadicSmallQuotientTotal.coefficients p) :=
  preservesLimitIso (Coefficient.IntrinsicPadicSmallQuotientTotal.coefficients p) F

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CoefficientLimits.IntrinsicPadicCoefficientLimits
