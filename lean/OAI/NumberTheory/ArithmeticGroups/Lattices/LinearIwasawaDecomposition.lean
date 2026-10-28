import OAI.NumberTheory.ArithmeticGroups.Lattices.DerivationSpectralDecomposition
import OAI.NumberTheory.ArithmeticGroups.Lattices.AutomorphismAdjointDerivations

/-! # Linear Iwasawa Decomposition -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.LinearIwasawaDecomposition.Construction

noncomputable section

/-! A regular symmetric derivation identifies the zero-weight symmetric
part with a maximal commuting subspace, giving the linear Iwasawa decomposition. -/

open _root_.ContinuousLinearMap

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

theorem regular_symmetric_centralizer_submodule [CompleteSpace L]
    (B : L →L[ℝ] L →L[ℝ] L) (a : Submodule ℝ (L →L[ℝ] L))
    (ha : a ≤ RegularSymmetricDerivation.Construction.symmetricDerivationSubmodule B) (H : L →L[ℝ] L)
    (hreg : ∀ X ∈ RegularSymmetricDerivation.Construction.symmetricDerivationSubmodule B, Commute H X ↔ X ∈ a) :
    DerivationSpectralDecomposition.Construction.bracketDerivationSubmodule B ⊓ (EndomorphismHilbertSchmidt.Construction.continuousCommutatorRepresentation H).toLinearMap.ker ⊓
      (DerivationSpectralDecomposition.Construction.continuousEndAdjointLinearMap (L := L) - LinearMap.id).ker = a := by
  apply le_antisymm
  · intro X hX
    have hder : Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B X = 0 := hX.1.1
    have hc : Commute H X := sub_eq_zero.mp hX.1.2
    have hs : adjoint X = X := sub_eq_zero.mp hX.2
    have hsym : X.toLinearMap.IsSymmetric := (eq_adjoint_iff X X).mp hs.symm
    exact (hreg X ⟨hsym, hder⟩).mp hc
  · intro X hX
    have hsym := ha hX
    refine ⟨⟨hsym.2, ?_⟩, ?_⟩
    · exact sub_eq_zero.mpr ((hreg X hsym).mpr hX).eq
    · change adjoint X - X = 0
      rw [hsym.1.clm_adjoint_eq, sub_self]

theorem exists_bracket_linear_iwasawa_decomposition
    (B : L →L[ℝ] L →L[ℝ] L)
    (hadj : ∀ X, Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B X = 0 →
      Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B (adjoint X) = 0) :
    ∃ (a : Submodule ℝ (L →L[ℝ] L)) (H : L →L[ℝ] L),
      a ≤ RegularSymmetricDerivation.Construction.symmetricDerivationSubmodule B ∧ (∀ X ∈ a, ∀ Y ∈ a, Commute X Y) ∧ H ∈ a ∧
      DerivationSpectralDecomposition.Construction.bracketDerivationSubmodule B = DerivationSpectralDecomposition.Construction.skewBracketDerivations B ⊔ a ⊔ DerivationSpectralDecomposition.Construction.positiveBracketDerivations B H := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  obtain ⟨a, ha, hc, H, hH, hreg⟩ := RegularSymmetricDerivation.Construction.exists_regular_symmetric_derivation B
  refine ⟨a, H, ha, hc, hH, ?_⟩
  rw [DerivationSpectralDecomposition.Construction.bracket_derivation_spectral_decomposition B hadj H (ha hH),
    regular_symmetric_centralizer_submodule B a ha H hreg]

theorem exists_killing_bracket_linear_iwasawa_realization
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (B : V →L[ℝ] V →L[ℝ] V) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate) :
    ∃ (m : ℕ) (Ψ : V ≃L[ℝ] EuclideanSpace ℝ (Fin m))
      (a : Submodule ℝ (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)))
      (H : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)),
      a ≤ RegularSymmetricDerivation.Construction.symmetricDerivationSubmodule (Positive.Killing.Construction.continuousBracketTransport Ψ B) ∧
      (∀ X ∈ a, ∀ Y ∈ a, Commute X Y) ∧ H ∈ a ∧
      DerivationSpectralDecomposition.Construction.bracketDerivationSubmodule (Positive.Killing.Construction.continuousBracketTransport Ψ B) =
        DerivationSpectralDecomposition.Construction.skewBracketDerivations (Positive.Killing.Construction.continuousBracketTransport Ψ B) ⊔ a ⊔
          DerivationSpectralDecomposition.Construction.positiveBracketDerivations (Positive.Killing.Construction.continuousBracketTransport Ψ B) H := by
  obtain ⟨m, Ψ, _, hadj⟩ := AutomorphismAdjointDerivations.Construction.exists_normed_killing_adjoint_stable_realization B hB hK
  obtain ⟨a, H, ha, hc, hH, he⟩ := exists_bracket_linear_iwasawa_decomposition (Positive.Killing.Construction.continuousBracketTransport Ψ B) hadj
  exact ⟨m, Ψ, a, H, ha, hc, hH, he⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.LinearIwasawaDecomposition.Construction
