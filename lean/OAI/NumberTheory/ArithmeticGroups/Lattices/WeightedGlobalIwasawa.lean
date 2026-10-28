import OAI.NumberTheory.ArithmeticGroups.Lattices.KillingSplit
import OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.GlobalIwasawa

/-! # Weighted Global Iwasawa -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! Global Iwasawa factorization using the regular split weights
whose positive part separates the split subspace. -/

open _root_.ContinuousLinearMap

theorem KillingSplit.Construction.KillingSplitWeightData.global_iwasawa
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {B : L →L[ℝ] L →L[ℝ] L} (d : KillingSplit.Construction.KillingSplitWeightData B)
    (hadj : ∀ g : L ≃L[ℝ] L, ContinuousBracketChange.Construction.continuousBracketChange g B = B →
      ∀ x y, adjoint g.toContinuousLinearMap (B x y) =
        B (adjoint g.toContinuousLinearMap x) (adjoint g.toContinuousLinearMap y))
    (hDadj : ∀ X, Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B X = 0 →
      Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B (adjoint X) = 0)
    (g : (L →L[ℝ] L)ˣ) (hg : g ∈ UnipotentBracketGroup.Construction.continuousBracketUnitGroup B) :
    ∃ k ∈ OrthogonalBracketUnitCompactness.Construction.orthogonalBracketUnitGroup B, ∃ A : d.subspace,
      ∃ n ∈ UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement),
        g = k * OperatorExponentialUnits.Construction.operatorExpUnit A.val * n := by
  obtain ⟨k, hk, A, hA, n, hn, he⟩ := Bracket.GlobalIwasawa.Construction.bracket_global_iwasawa_product B hadj
    d.subspace d.regularElement.val d.le_symmetric d.commute d.regularElement.property
    (d.linear_iwasawa hDadj) d.basis (fun i => d.weight i d.regularElement)
    (fun i => d.eigenvector i d.regularElement) g hg
  exact ⟨k, hk, ⟨A, hA⟩, n, hn, he⟩

theorem WeightedGlobalIwasawa.Construction.exists_normed_killing_split_weight_realization
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (B : V →L[ℝ] V →L[ℝ] V) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate) :
    ∃ (m : ℕ) (Ψ : V ≃L[ℝ] EuclideanSpace ℝ (Fin m)),
      Nonempty (KillingSplit.Construction.KillingSplitWeightData (Positive.Killing.Construction.continuousBracketTransport Ψ B)) ∧
      (∀ g : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m),
        ContinuousBracketChange.Construction.continuousBracketChange g (Positive.Killing.Construction.continuousBracketTransport Ψ B) = Positive.Killing.Construction.continuousBracketTransport Ψ B →
          ∀ x y, adjoint g.toContinuousLinearMap (Positive.Killing.Construction.continuousBracketTransport Ψ B x y) =
            Positive.Killing.Construction.continuousBracketTransport Ψ B (adjoint g.toContinuousLinearMap x)
              (adjoint g.toContinuousLinearMap y)) ∧
      (∀ X, Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect (Positive.Killing.Construction.continuousBracketTransport Ψ B) X = 0 →
        Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect (Positive.Killing.Construction.continuousBracketTransport Ψ B) (adjoint X) = 0) := by
  obtain ⟨m, Ψ, hadj, hDadj⟩ := AutomorphismAdjointDerivations.Construction.exists_normed_killing_adjoint_stable_realization B hB hK
  exact ⟨m, Ψ, KillingSplit.Construction.exists_killing_split_weight_data _ (Positive.Killing.Construction.continuousBracketTransport_isLie Ψ B hB)
    (Positive.Killing.Construction.continuousBracketTransport_killing_nondegenerate Ψ B hK), hadj, hDadj⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
