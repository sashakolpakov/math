import OAI.NumberTheory.ArithmeticGroups.Lattices.KillingSplit

/-! # Regular Split Centralizer -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! Every regular element of the fixed split subspace has that
subspace as its symmetric derivation centralizer. -/

theorem KillingSplit.Construction.KillingSplitWeightData.regular_symmetric_centralizer
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {B : L →L[ℝ] L →L[ℝ] L} (d : KillingSplit.Construction.KillingSplitWeightData B) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (A : d.subspace) (hA : ∀ i, d.weight i A = 0 ↔ d.weight i = 0) :
    ∀ X ∈ RegularSymmetricDerivation.Construction.symmetricDerivationSubmodule B, Commute A.val X ↔ X ∈ d.subspace := by
  apply RegularWeightsCentralizer.Construction.killing_regular_weights_centralizer B hB hK d.subspace d.le_symmetric d.commute
    _ d.basis d.weight d.eigenvector A hA
  intro X hX hc
  exact (d.centralizer X hX).mp (hc d.regularElement.val d.regularElement.property).symm

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
