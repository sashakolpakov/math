import OAI.NumberTheory.ArithmeticGroups.Lattices.Split.UnipotentProductCoordinates
import OAI.NumberTheory.ArithmeticGroups.Lattices.CommutingExponentialHomeomorph
import OAI.NumberTheory.ArithmeticGroups.Lattices.UnipotentExponentialHomeomorph

/-! # Filtered Exponential Coordinates -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! The split filtered group has global coordinates in the product
of its symmetric split subspace and positive derivation space. -/

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L}

def KillingSplit.Construction.KillingSplitWeightData.splitExponentialHomeomorph (d : KillingSplit.Construction.KillingSplitWeightData B) :
    d.subspace × (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val) ≃ₜ
      Split.FilteredBracketGroup.Construction.splitFilteredBracketUnitGroup B d.basis.toBasis (fun i => d.weight i d.regularElement) d.subspace d.commute :=
  ((CommutingExponentialHomeomorph.Construction.commutingExponentialHomeomorph d.subspace (fun _ hX => (d.le_symmetric hX).1) d.commute).prodCongr
    d.positiveUnipotentExpHomeomorph).trans d.splitUnipotentHomeomorph

theorem KillingSplit.Construction.KillingSplitWeightData.splitExponentialHomeomorph_val
    (d : KillingSplit.Construction.KillingSplitWeightData B)
    (x : d.subspace × (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val)) :
    (d.splitExponentialHomeomorph x).val = OperatorExponentialUnits.Construction.operatorExpUnit x.1.val * OperatorExponentialUnits.Construction.operatorExpUnit x.2.val := rfl

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
