import OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.EigenbasisSpan
import OAI.NumberTheory.ArithmeticGroups.Lattices.Split.ChamberIntegrability

/-! # Inner Derivation Basis -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! The positive derivations of a Killing bracket have a basis of
inner derivations indexed by its positive restricted weights. -/

open scoped Classical

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L}

theorem KillingSplit.Construction.KillingSplitWeightData.positive_derivation_span
    (d : KillingSplit.Construction.KillingSplitWeightData B) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate) :
    DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val =
      Submodule.span ℝ (Set.range (fun i : d.PositiveIndex => B (d.basis i.val))) := by
  have hD : DerivationSpectralDecomposition.Construction.bracketDerivationSubmodule B = B.toLinearMap.range :=
    ContinuousInnerDerivations.Construction.continuousKillingBracket_derivation_kernel B hB hK
  rw [DerivationSpectralDecomposition.Construction.positiveBracketDerivations, hD,
    InvolutionSpectralDecomposition.Construction.positiveSpectralSubmodule_range _ d.regularElement.val.toLinearMap B.toLinearMap
      (ContinuousInnerDerivations.Construction.continuousKillingBracket_injective B hK)
      (fun x => FaithfulDerivationCommutator.Construction.derivation_commutator_inner_operator B d.regularElement.val
        (d.le_symmetric d.regularElement.property).2 x),
    Positive.EigenbasisSpan.Construction.positiveSpectralSubmodule_eq_eigenbasis_span d.basis d.regularElement.val
      (d.le_symmetric d.regularElement.property).1 (fun i => d.weight i d.regularElement)
      (fun i => d.eigenvector i d.regularElement), Submodule.map_span, ← Set.range_comp]
  rfl

def KillingSplit.Construction.KillingSplitWeightData.positiveDerivationBasis
    (d : KillingSplit.Construction.KillingSplitWeightData B) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate) :
    Module.Basis d.PositiveIndex ℝ (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val) :=
  (Module.Basis.span
    ((d.basis.toBasis.linearIndependent.comp (fun i : d.PositiveIndex => i.val) Subtype.val_injective).map'
      B.toLinearMap (LinearMap.ker_eq_bot.mpr (ContinuousInnerDerivations.Construction.continuousKillingBracket_injective B hK)))).map
    (LinearEquiv.ofEq _ _ (d.positive_derivation_span hB hK).symm)

theorem KillingSplit.Construction.KillingSplitWeightData.positiveDerivationBasis_val
    (d : KillingSplit.Construction.KillingSplitWeightData B) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate) (i : d.PositiveIndex) :
    (d.positiveDerivationBasis hB hK i).val = B (d.basis i.val) := by
  unfold KillingSplit.Construction.KillingSplitWeightData.positiveDerivationBasis
  rw [Module.Basis.map_apply]
  change ((Module.Basis.span _) i).val = B (d.basis i.val)
  exact Module.Basis.coe_span_apply _ i

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
