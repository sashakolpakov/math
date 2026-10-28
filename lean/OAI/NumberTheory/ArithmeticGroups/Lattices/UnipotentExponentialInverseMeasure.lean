import OAI.NumberTheory.ArithmeticGroups.Lattices.UnipotentExponentialHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Unipotent Exponential Inverse Measure -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! Negation in exponential coordinates corresponds to group
inversion, so the constructed unipotent Haar measure is also right invariant. -/

open _root_.MeasureTheory _root_.MeasureTheory.Measure

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L}

local instance UnipotentExponentialInverseMeasure.Construction.inverseMeasure_complete : CompleteSpace L := FiniteDimensional.complete ℝ L
local instance UnipotentExponentialInverseMeasure.Construction.inverseMeasureEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance UnipotentExponentialInverseMeasure.Construction.inverseMeasureEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance UnipotentExponentialInverseMeasure.Construction.inverseMeasureEnd_finite : FiniteDimensional ℝ (L →L[ℝ] L) := inferInstance

variable (d : KillingSplit.Construction.KillingSplitWeightData B)
  [MeasurableSpace (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val)]
  [BorelSpace (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val)]
  [MeasurableSpace (UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement))]
  [BorelSpace (UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement))]

theorem KillingSplit.Construction.KillingSplitWeightData.positiveUnipotentExp_inv_measure
    (μ : Measure (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val)) [IsAddHaarMeasure μ] :
    (μ.map d.positiveUnipotentExpHomeomorph).inv = μ.map d.positiveUnipotentExpHomeomorph := by
  have he : Inv.inv ∘ d.positiveUnipotentExpHomeomorph =
      d.positiveUnipotentExpHomeomorph ∘ Neg.neg := by
    funext X
    apply Subtype.ext
    change (OperatorExponentialUnits.Construction.operatorExpUnit X.val)⁻¹ = OperatorExponentialUnits.Construction.operatorExpUnit (-X.val)
    exact (OperatorExponentialUnits.Construction.operatorExpUnit_neg X.val).symm
  rw [Measure.inv_def, Measure.map_map measurable_inv d.positiveUnipotentExpHomeomorph.continuous.measurable,
    he, ← Measure.map_map d.positiveUnipotentExpHomeomorph.continuous.measurable measurable_neg,
    map_neg_eq_self]

theorem KillingSplit.Construction.KillingSplitWeightData.positiveUnipotentExp_isMulRightInvariant
    (μ : Measure (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val)) [IsAddHaarMeasure μ] :
    IsMulRightInvariant (μ.map d.positiveUnipotentExpHomeomorph) := by
  let := d.positiveUnipotentExp_isHaarMeasure μ
  rw [← d.positiveUnipotentExp_inv_measure μ]
  infer_instance

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
