import OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.SplitConjugation
import OAI.NumberTheory.ArithmeticGroups.Lattices.MeasureScalingConjugacy
import OAI.NumberTheory.ArithmeticGroups.Lattices.UnipotentExponentialHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Unipotent Conjugation Haar Scaling -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! Split conjugation rescales unipotent Haar measure by the inverse
exponential of the positive-weight trace. -/

open _root_.MeasureTheory _root_.MeasureTheory.Measure

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L}

local instance UnipotentConjugationHaarScaling.Construction.conjugationHaarEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance UnipotentConjugationHaarScaling.Construction.conjugationHaarEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance UnipotentConjugationHaarScaling.Construction.conjugationHaarEnd_finite : FiniteDimensional ℝ (L →L[ℝ] L) := inferInstance

variable (d : KillingSplit.Construction.KillingSplitWeightData B)
  [MeasurableSpace (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val)]
  [BorelSpace (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val)]

theorem KillingSplit.Construction.KillingSplitWeightData.positiveConjugation_map_addHaar
    (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B) (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (μ : Measure (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val)) [IsAddHaarMeasure μ]
    (A : d.subspace) :
    μ.map (d.positiveConjugation A) = ENNReal.ofReal (Real.exp (-d.positiveTrace A)) • μ := by
  have hdet : (d.positiveConjugation A).toLinearEquiv.toLinearMap.det ≠ 0 := by
    rw [d.positiveConjugation_det hB hK]
    exact Real.exp_ne_zero _
  have hm := map_linearMap_addHaar_eq_smul_addHaar μ hdet
  rw [d.positiveConjugation_det hB hK, abs_of_pos (inv_pos.mpr (Real.exp_pos _)),
    ← Real.exp_neg] at hm
  exact hm

variable [MeasurableSpace (UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement))]
  [BorelSpace (UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement))]

theorem KillingSplit.Construction.KillingSplitWeightData.unipotentConjugation_map_expHaar
    (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B) (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (μ : Measure (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val)) [IsAddHaarMeasure μ]
    (A : d.subspace) :
    (μ.map d.positiveUnipotentExpHomeomorph).map (d.unipotentConjugation A) =
      ENNReal.ofReal (Real.exp (-d.positiveTrace A)) • μ.map d.positiveUnipotentExpHomeomorph :=
  MeasureScalingConjugacy.Construction.measure_scaling_of_semiconjugacy μ d.positiveUnipotentExpHomeomorph
    d.positiveUnipotentExpHomeomorph.continuous.measurable (d.positiveConjugation A)
    (d.positiveConjugation A).continuous.measurable (d.unipotentConjugation A)
    (d.unipotentConjugation A).continuous.measurable (d.unipotentConjugation_exp A) _
    (d.positiveConjugation_map_addHaar hB hK μ A)

theorem KillingSplit.Construction.KillingSplitWeightData.unipotentNegativeConjugation_map_expHaar
    (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B) (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (μ : Measure (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val)) [IsAddHaarMeasure μ]
    (A : d.subspace) :
    (μ.map d.positiveUnipotentExpHomeomorph).map (d.unipotentConjugation (-A)) =
      ENNReal.ofReal (Real.exp (d.positiveTrace A)) • μ.map d.positiveUnipotentExpHomeomorph := by
  simpa only [map_neg, neg_neg] using d.unipotentConjugation_map_expHaar hB hK μ (-A)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
