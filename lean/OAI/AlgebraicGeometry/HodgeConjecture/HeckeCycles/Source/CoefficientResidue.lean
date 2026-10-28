import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RestrictedPlace
import OAI.RepresentationTheory.Hecke.CoefficientResidueSquare

/-! # Coefficient Residue -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.CoefficientResidue.CM

noncomputable section

/-! The coefficient residue square for the actual source is the
reduction of its original integral completion map. Restriction to the
original number field preserves that same completion map. -/

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  (M : PELModuli.CMPoints.Models.RankThreePELModel E K) (hM : M.HasPrescribedBallPeriods)
  {q : ℕ} [Fact q.Prime] (j : M.QadicChoice q)
  (hsplit : j.HasSplitCoordinates M.extendedEmbedding)
  (R : M.GoodIntegralReduction q j)
  (labels : (Fin M.s × Bool) ≃ Gal(E/ℚ))
  (hlabels : ∀ (v : Fin M.s) (b : Bool),
    labels (v, !b) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, b))
  (a : M.Family) (hden : Nat.Coprime q M.arithmetic.denominator)

local notation "D" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a
local notation "J" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RestrictedPlace.CM.choice M j

include hden in
theorem coefficient_square : RepresentationTheory.Hecke.ModelBlockCharacters.OrdinaryCharacterIntrinsic.CoefficientResidueSquare D J :=
  RepresentationTheory.Hecke.CoefficientResidueSquare.OrdinaryCharacterIntrinsic.coefficientResidueSquare_of_completion D J
    (QadicModelMap.CM.integralMap j M.arithmetic.denominator hden)
    (QadicModelMap.CM.localFieldEmbedding j)
    (QadicModelMap.CM.integralMap_generic j M.arithmetic.denominator M.arithmetic.denominator_ne_zero hden)
    (PELModuli.CMPoints.LocalPadic.embeddingCompletionEquiv_comp
      (RestrictedPlace.CM.fieldEmbedding (algebraMap K M.arithmetic.extension.carrier) j)).symm
    (QadicModelMap.CM.integralMap_residue j M.arithmetic.denominator hden R.residue R.residue_compatibility).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.CoefficientResidue.CM
