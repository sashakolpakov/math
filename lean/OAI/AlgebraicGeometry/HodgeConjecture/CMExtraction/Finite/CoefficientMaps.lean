import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.CoefficientTopology

/-! # Coefficient Maps -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.CoefficientMaps.TestTransport

noncomputable section

/-! Continuous scalar extension of actual rational linear maps and
field homomorphisms to the PEL finite coefficient tensor algebras. -/

open scoped Classical TensorProduct

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]

def finiteCoefficientLinearMap (f : F →ₗ[ℚ] E) :
    AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients F →ₗ[AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles] AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E :=
  f.baseChange AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles

theorem finiteCoefficientLinearMap_continuous (f : F →ₗ[ℚ] E) :
    Continuous (finiteCoefficientLinearMap f) :=
  AbelianModuli.ReferenceFamily.AdelicCoefficientTopology.finiteCoefficientLinearMap_continuous (finiteCoefficientLinearMap f)

theorem finiteCoefficientLinearMap_rational (f : F →ₗ[ℚ] E) (x : F) :
    finiteCoefficientLinearMap f (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding F x) =
      AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E (f x) := rfl

def finiteCoefficientAlgMap (f : F →ₐ[ℚ] E) :
    AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients F →ₐ[AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles] AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E :=
  Algebra.TensorProduct.map (AlgHom.id AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles) f

theorem finiteCoefficientAlgMap_continuous (f : F →ₐ[ℚ] E) :
    Continuous (finiteCoefficientAlgMap f) :=
  AbelianModuli.ReferenceFamily.AdelicCoefficientTopology.finiteCoefficientLinearMap_continuous (finiteCoefficientAlgMap f).toLinearMap

theorem finiteCoefficientAlgMap_rational (f : F →ₐ[ℚ] E) (x : F) :
    finiteCoefficientAlgMap f (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding F x) =
      AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E (f x) := rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.CoefficientMaps.TestTransport
