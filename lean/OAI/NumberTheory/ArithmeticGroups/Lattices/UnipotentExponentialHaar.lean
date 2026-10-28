import OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.TranslationDerivative
import OAI.NumberTheory.ArithmeticGroups.Lattices.UnitJacobianPreservesMeasure
import OAI.NumberTheory.ArithmeticGroups.Lattices.HaarFromHomeomorphicCoordinates

/-! # Unipotent Exponential Haar -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! Exponential coordinates carry additive Haar measure on the positive
derivations to Haar measure on the full unipotent bracket subgroup. -/

open _root_.MeasureTheory _root_.MeasureTheory.Measure

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L}

local instance UnipotentExponentialHaar.Construction.exponentialHaarEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance UnipotentExponentialHaar.Construction.exponentialHaarEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance UnipotentExponentialHaar.Construction.exponentialHaarEnd_finite : FiniteDimensional ℝ (L →L[ℝ] L) := inferInstance

variable (d : KillingSplit.Construction.KillingSplitWeightData B)
  [MeasurableSpace (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val)]
  [BorelSpace (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val)]

theorem KillingSplit.Construction.KillingSplitWeightData.positiveLeftTranslation_measurePreserving
    (μ : Measure (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val)) [IsAddHaarMeasure μ]
    (g : UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement)) :
    MeasurePreserving (d.positiveLeftTranslation g) μ μ :=
  UnitJacobianPreservesMeasure.Construction.measurePreserving_homeomorph_of_det_one (d.positiveLeftTranslation g) μ
    (d.positiveTranslationDifferential g) (d.positiveLeftTranslation_hasFDerivAt g)
    (d.positiveTranslationDifferential_det g)

variable [MeasurableSpace (UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement))]
  [BorelSpace (UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement))]

theorem KillingSplit.Construction.KillingSplitWeightData.positiveUnipotentExp_isHaarMeasure
    (μ : Measure (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val)) [IsAddHaarMeasure μ] :
    IsHaarMeasure (μ.map d.positiveUnipotentExpHomeomorph) :=
  HaarFromHomeomorphicCoordinates.Construction.isHaarMeasure_of_homeomorphic_coordinates d.positiveUnipotentExpHomeomorph μ
    (fun g => d.positiveLeftTranslation g) (d.positiveLeftTranslation_measurePreserving μ)
    d.positiveLeftTranslation_exp

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
