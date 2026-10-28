import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.CoefficientMaps
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AdelicTensorDensity

/-! # Coefficient Conjugation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.CoefficientConjugation.TestTransport

noncomputable section

/-! The PEL tensor algebra carries its actual CM conjugation, extended
continuously from the original field factor. -/

open scoped Classical TensorProduct

open _root_.NumberField

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

def finiteConjugationAlgHom : AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E →ₐ[AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles] AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E :=
  CoefficientMaps.TestTransport.finiteCoefficientAlgMap (IsCMField.complexConj E).toRingHom.toRatAlgHom

theorem finiteConjugationAlgHom_eq (x : AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) :
    finiteConjugationAlgHom E x = AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientConjugation E x := by
  induction x using TensorProduct.inductionOn with
  | tmul r x => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem finiteCoefficientConjugation_continuous : Continuous (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientConjugation E) :=
  (CoefficientMaps.TestTransport.finiteCoefficientAlgMap_continuous (IsCMField.complexConj E).toRingHom.toRatAlgHom).congr
    (finiteConjugationAlgHom_eq E)

theorem finiteCoefficientConjugation_rational (x : E) :
    AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientConjugation E (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E x) =
      AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E (IsCMField.complexConj E x) := rfl

theorem finiteCoefficientConjugation_involutive :
    Function.Involutive (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientConjugation E) := by
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
      change r ⊗ₜ[ℚ] (IsCMField.complexConj E (IsCMField.complexConj E x)) = r ⊗ₜ[ℚ] x
      rw [IsCMField.complexConj_apply_apply]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

instance finiteCoefficientStarRing : StarRing (AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) where
  star := AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientConjugation E
  star_involutive := finiteCoefficientConjugation_involutive E
  star_mul x y := (map_mul (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientConjugation E) x y).trans (mul_comm _ _)
  star_add := map_add (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientConjugation E)

instance finiteCoefficientContinuousStar : ContinuousStar (AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) :=
  ⟨finiteCoefficientConjugation_continuous E⟩

theorem finiteCoefficientEmbedding_star (x : E) :
    star (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E x) =
      AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E (IsCMField.complexConj E x) :=
  finiteCoefficientConjugation_rational E x

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.CoefficientConjugation.TestTransport
