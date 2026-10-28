import OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.TranslationCoordinates
import OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.DerivativeFactorization
import OAI.NumberTheory.ArithmeticGroups.Lattices.TranslatedChartDerivative

/-! # Translation Derivative -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! In exponential coordinates, every left translation of the
unipotent subgroup has derivative with determinant one. -/

open NormedSpace

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L}

local instance Positive.TranslationDerivative.Construction.translationDerivative_complete : CompleteSpace L := FiniteDimensional.complete ℝ L
local instance Positive.TranslationDerivative.Construction.translationDerivativeEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance Positive.TranslationDerivative.Construction.translationDerivativeEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance Positive.TranslationDerivative.Construction.translationDerivativeEnd_finite : FiniteDimensional ℝ (L →L[ℝ] L) := inferInstance

def KillingSplit.Construction.KillingSplitWeightData.positiveTranslationDifferential (d : KillingSplit.Construction.KillingSplitWeightData B)
    (g : UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement))
    (X : DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val) :
    DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val →L[ℝ]
      DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val :=
  (d.positiveLeftDifferentialEquiv (d.positiveLeftTranslation g X)).symm.toContinuousLinearMap.comp
    (d.positiveLeftDifferentialEquiv X).toContinuousLinearMap

theorem KillingSplit.Construction.KillingSplitWeightData.positiveLeftTranslation_hasFDerivAt (d : KillingSplit.Construction.KillingSplitWeightData B)
    (g : UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement))
    (X : DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val) :
    HasFDerivAt (d.positiveLeftTranslation g) (d.positiveTranslationDifferential g X) X := by
  apply TranslatedChartDerivative.Construction.translated_chart_hasFDerivAt
    (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val).subtypeL Subtype.val_injective
    (fun Y => exp Y.val) d.positiveLeftDifferentialEquiv
  · intro Y
    rw [← d.positiveExpDifferential_factor]
    exact (d.positive_exp_hasStrictFDerivAt Y).hasFDerivAt
  · intro Y
    exact (OperatorExponentialUnits.Construction.operatorExpUnit Y.val).isUnit
  · exact d.positiveLeftTranslation_exp_val g

theorem KillingSplit.Construction.KillingSplitWeightData.positiveTranslationDifferential_det (d : KillingSplit.Construction.KillingSplitWeightData B)
    (g : UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement))
    (X : DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val) :
    (d.positiveTranslationDifferential g X).toLinearMap.det = 1 := by
  change LinearMap.det
    ((d.positiveLeftDifferentialEquiv (d.positiveLeftTranslation g X)).toLinearEquiv.symm.toLinearMap.comp
      (d.positiveLeftDifferentialEquiv X).toLinearEquiv.toLinearMap) = 1
  rw [LinearMap.det_comp, LinearEquiv.det_coe_symm,
    d.positiveLeftDifferentialEquiv_det, d.positiveLeftDifferentialEquiv_det, inv_one, one_mul]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
