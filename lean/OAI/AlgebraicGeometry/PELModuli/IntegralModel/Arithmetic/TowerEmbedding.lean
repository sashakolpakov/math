import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.Tower
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.Has

/-! # Tower Embedding -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! An arithmetic coefficient specialization preserves the exact
integral CM embedding after collapsing the finite number-field tower. -/

variable {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}

theorem Base.ArithmeticBaseExtension.compose_integralEmbedding (B : Base.ArithmeticBaseExtension K κ)
    (D : Base.ArithmeticBaseExtension B.extension.carrier B.embedding) (φ : B.R →+* D.R)
    (hφ : D.toField.comp φ = (algebraMap B.extension.carrier D.extension.carrier).comp B.toField)
    {E : Type} [Field E] (iota : E →+* K) :
    φ.comp (B.integralEmbedding iota) = (B.compose D).integralEmbedding iota := by
  ext a
  apply (B.compose D).toField_injective
  exact (RingHom.congr_fun hφ (B.integralEmbedding iota a)).trans
    ((congrArg (algebraMap B.extension.carrier D.extension.carrier)
      (B.integralEmbedding_toField iota a)).trans
        ((B.compose D).integralEmbedding_toField iota a).symm)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
