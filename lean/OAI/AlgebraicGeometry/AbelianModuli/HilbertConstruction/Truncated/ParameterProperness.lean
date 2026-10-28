import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ProperProducts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.GradedParameters

/-! # Parameter Properness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.ParameterProperness

noncomputable section

/-! The constructed finite quotient and multiplication parameter schemes are proper over the base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable (σ : Type v) [Finite σ] (B : ℕ) (r : ℕ → ℕ) (S : Scheme.{max u v})

instance truncatedQuotientParameters_proper :
    IsProper (QuotientParameters.truncatedQuotientParameters.{u, v} σ B r S).hom := by
  apply HilbertConstruction.Finite.ProperProducts.overFinProduct_proper
  intro d
  exact Grassmann.ParameterScheme.grassmannParameterScheme_proper S

instance truncatedGradedParameters_proper :
    IsProper (GradedParameters.truncatedGradedParameters.{u, v} σ B r S).hom := by
  rw [← (GradedParameters.truncatedGradedInclusion σ B r S).w]
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.ParameterProperness
