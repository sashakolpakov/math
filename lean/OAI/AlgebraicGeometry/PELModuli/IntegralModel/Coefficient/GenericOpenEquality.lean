import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Models
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.GenericOpenEqualityLocalization

/-! # Generic Open Equality -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.GenericOpenEquality.Coefficients

noncomputable section

/-! Equal open inverse images under the actual generic comparison
give equal field-base-change opens, then equality after localization. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

theorem generic_open_equality_of_specialization {X : Over (Spec (.of K))}
    (M : Models.Coefficients.CoefficientModel R K X) (U V : M.model.left.Opens)
    (h : M.specialization ⁻¹ᵁ U = M.specialization ⁻¹ᵁ V) :
    pullback.fst M.model.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K M.coefficients) ⁻¹ᵁ U =
      pullback.fst M.model.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K M.coefficients) ⁻¹ᵁ V := by
  have he := congrArg (fun W => M.genericIso.hom.left ⁻¹ᵁ W) h
  simp only [Models.Coefficients.CoefficientModel.specialization, Scheme.Hom.comp_preimage] at he
  simpa only [← Scheme.Hom.comp_preimage, Over.hom_left_inv_left_assoc] using he

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.GenericOpenEquality.Coefficients
