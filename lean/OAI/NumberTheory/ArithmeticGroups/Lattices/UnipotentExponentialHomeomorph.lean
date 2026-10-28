import OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.UnipotentSplitFlow
import OAI.NumberTheory.ArithmeticGroups.Lattices.ContractingInverseContinuity

/-! # Unipotent Exponential Homeomorph -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! Exponential coordinates identify the entire unipotent bracket
group homeomorphically with its positive derivation space. -/

open scoped _root_.Topology
open Filter

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L}

theorem KillingSplit.Construction.KillingSplitWeightData.positiveUnipotentLog_continuous
    (d : KillingSplit.Construction.KillingSplitWeightData B) : Continuous d.positiveUnipotentExpEquiv.symm :=
  ContractingInverseContinuity.Construction.continuous_inverse_of_contracting_equivariance d.positiveUnipotentExpEquiv
    (fun t : ℝ => d.positiveSplitFlow t) (fun t : ℝ => d.positiveSplitFlow (-t))
    d.unipotentSplitFlow (fun t => (d.positiveSplitFlow (-t)).continuous)
    d.unipotentSplitFlow_continuous d.positiveSplitFlow_inverse
    d.positiveUnipotentExp_splitFlow atTop 1 d.unipotentSplitFlow_contracts
    d.positiveLog_eventually_continuousAt

def KillingSplit.Construction.KillingSplitWeightData.positiveUnipotentExpHomeomorph (d : KillingSplit.Construction.KillingSplitWeightData B) :
    DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val ≃ₜ
      UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement) where
  toEquiv := d.positiveUnipotentExpEquiv
  continuous_toFun := d.positiveUnipotentExp_continuous
  continuous_invFun := d.positiveUnipotentLog_continuous

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
