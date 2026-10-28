import OAI.NumberTheory.ArithmeticGroups.Lattices.Split.ChamberFiniteMeasure
import OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.ContinuousDensity
import OAI.NumberTheory.ArithmeticGroups.Lattices.HomeomorphMeasureFiniteness

/-! # Exponential Haar -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! The explicit split exponential measure is finite on compact sets
and positive on open sets; its inverse is a Haar measure. -/

open _root_.MeasureTheory _root_.MeasureTheory.Measure

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L}

local instance Split.ExponentialHaar.Construction.splitHaarEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance Split.ExponentialHaar.Construction.splitHaarEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance Split.ExponentialHaar.Construction.splitHaarEnd_finite : FiniteDimensional ℝ (L →L[ℝ] L) := inferInstance

variable (d : KillingSplit.Construction.KillingSplitWeightData B)
  [MeasurableSpace d.subspace] [BorelSpace d.subspace]
  [MeasurableSpace (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val)]
  [BorelSpace (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val)]
  [MeasurableSpace (UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement))]
  [BorelSpace (UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement))]
  [MeasurableSpace (Split.FilteredBracketGroup.Construction.splitFilteredBracketUnitGroup B d.basis.toBasis (fun i => d.weight i d.regularElement)
    d.subspace d.commute)]
  [BorelSpace (Split.FilteredBracketGroup.Construction.splitFilteredBracketUnitGroup B d.basis.toBasis (fun i => d.weight i d.regularElement)
    d.subspace d.commute)]

theorem KillingSplit.Construction.KillingSplitWeightData.splitExponentialMeasure_inv_isHaarMeasure
    (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B) (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (μ : Measure d.subspace) [IsAddHaarMeasure μ]
    (ν : Measure (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val)) [IsAddHaarMeasure ν] :
    IsHaarMeasure (d.splitExponentialMeasure μ ν).inv := by
  let μa : Measure (Multiplicative d.subspace) := μ
  let ρa := μa.withDensity (ExponentialLinearCharacter.Construction.exponentialLinearCharacter d.positiveTrace)
  let ρn := ν.map d.positiveUnipotentExpHomeomorph
  let : IsLocallyFiniteMeasure μa := (inferInstance : IsLocallyFiniteMeasure μ)
  let : IsOpenPosMeasure μa := (inferInstance : IsOpenPosMeasure μ)
  have hc : Continuous (fun A : Multiplicative d.subspace => Real.exp (d.positiveTrace A.toAdd)) :=
    Real.continuous_exp.comp d.positiveTrace.continuous_of_finiteDimensional
  let : IsFiniteMeasureOnCompacts ρa := Positive.ContinuousDensity.Construction.continuous_positive_density_finite_on_compacts μa _ hc
  let : IsOpenPosMeasure ρa := Positive.ContinuousDensity.Construction.isOpenPosMeasure_withDensity_positive μa _
    (ExponentialLinearCharacter.Construction.exponentialLinearCharacter_continuous d.positiveTrace).measurable
    (fun A => (ENNReal.ofReal_pos.mpr (Real.exp_pos (d.positiveTrace A.toAdd))).ne')
  let : IsHaarMeasure ρn := d.positiveUnipotentExp_isHaarMeasure ν
  let : IsFiniteMeasureOnCompacts (d.splitExponentialMeasure μ ν) :=
    HomeomorphMeasureFiniteness.Construction.isFiniteMeasureOnCompacts_map_homeomorph d.additiveSplitProductHomeomorph (ρa.prod ρn)
  let : IsOpenPosMeasure (d.splitExponentialMeasure μ ν) :=
    d.additiveSplitProductHomeomorph.continuous.isOpenPosMeasure_map d.additiveSplitProductHomeomorph.surjective
  let := d.splitExponentialMeasure_isMulRightInvariant hB hK μ ν
  exact
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsMulLeftInvariant := inferInstance
      toIsOpenPosMeasure := inferInstance }

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
