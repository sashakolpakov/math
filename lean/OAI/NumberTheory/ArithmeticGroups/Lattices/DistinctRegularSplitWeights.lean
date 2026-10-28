import OAI.NumberTheory.ArithmeticGroups.Lattices.KillingSplit

/-! # Distinct Regular Split Weights -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.DistinctRegularSplitWeights.Construction

noncomputable section

/-! The regular split element may also separate every pair of distinct
weights, allowing one ordering of the ambient basis compatible with the roots. -/

open scoped Classical

theorem exists_distinct_regular_linear_forms
    {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Finite ι]
    (w : ι → Module.Dual ℝ E) :
    ∃ H : E, (∀ i, w i H = 0 ↔ w i = 0) ∧
      ∀ i j, w i H = w j H ↔ w i = w j := by
  let f : ι ⊕ (ι × ι) → Module.Dual ℝ E := Sum.elim w (fun p => w p.1 - w p.2)
  obtain ⟨H, hH⟩ := RegularLinearForms.Construction.exists_regular_linear_forms f
  refine ⟨H, fun i => hH (Sum.inl i), fun i j => ?_⟩
  have he := hH (Sum.inr (i, j))
  simpa only [f, Sum.elim_inr, LinearMap.sub_apply, sub_eq_zero] using he

theorem exists_killing_split_weight_data_distinct
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    (B : L →L[ℝ] L →L[ℝ] L) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate) :
    ∃ d : KillingSplit.Construction.KillingSplitWeightData B, ∀ i j,
      d.weight i d.regularElement = d.weight j d.regularElement ↔ d.weight i = d.weight j := by
  obtain ⟨a, ha, hc, hmax⟩ := MaximalCommutingSubspace.Construction.exists_maximal_commuting_subspace (RegularSymmetricDerivation.Construction.symmetricDerivationSubmodule B)
  obtain ⟨b, w, heig⟩ := CommutingSymmetricWeights.Construction.exists_commuting_symmetric_weights a (fun A hA => (ha hA).1) hc
  obtain ⟨H, hH, hdistinct⟩ := exists_distinct_regular_linear_forms w
  have hopp := InvariantFormWeightPairing.Construction.invariant_form_weights_opposite a b w heig (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B) hK
    (fun A x y => FaithfulDerivationCommutator.Construction.continuousBracketKillingForm_derivation B A.val (ha A.property).2 x y)
  exact ⟨⟨a, b, w, H, ha, hc, heig, hH, hopp,
    RegularWeightsCentralizer.Construction.killing_regular_weights_centralizer B hB hK a ha hc hmax b w heig H hH⟩, hdistinct⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.DistinctRegularSplitWeights.Construction
