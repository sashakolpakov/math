import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.CoefficientEvaluation
import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteSchur

/-! # Coefficient Padic -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.CoefficientPadic.TestTransport

noncomputable section

/-! Continuous evaluation of the original finite PEL coefficient algebra
at a specified embedding of its number field into Q_q. -/

open scoped Classical TensorProduct

open OAI.RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization

variable (E : Type*) [Field E] [NumberField E]
  {q : ℕ} [Fact q.Prime] (σ : E →+* Padic q)

def finiteCoefficientPadic : AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E →ₐ[ℚ] Padic q :=
  TensorEvaluation.TestTransport.tensorEvaluation (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q) σ.toRatAlgHom

theorem finiteCoefficientPadic_tmul (a : AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles) (x : E) :
    finiteCoefficientPadic E σ (a ⊗ₜ[ℚ] x) = RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q a * σ x :=
  TensorEvaluation.TestTransport.tensorEvaluation_tmul (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q) σ.toRatAlgHom a x

theorem finiteCoefficientPadic_rational (x : E) :
    finiteCoefficientPadic E σ (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E x) = σ x := by
  exact (finiteCoefficientPadic_tmul E σ 1 x).trans (by rw [map_one, one_mul])

theorem finiteCoefficientPadic_smul (a : AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles) (x : AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) :
    finiteCoefficientPadic E σ (a • x) =
      RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q a * finiteCoefficientPadic E σ x :=
  TensorEvaluation.TestTransport.tensorEvaluation_smul (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q) σ.toRatAlgHom a x

theorem finiteCoefficientPadic_continuous : Continuous (finiteCoefficientPadic E σ) :=
  CoefficientEvaluation.TestTransport.finiteCoefficientEvaluation_continuous E (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q) σ.toRatAlgHom
    (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection_continuous q)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.CoefficientPadic.TestTransport
