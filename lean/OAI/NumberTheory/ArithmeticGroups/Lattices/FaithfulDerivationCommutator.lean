import OAI.NumberTheory.ArithmeticGroups.Lattices.DerivationSpectralDecomposition
import OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.KillingDeterminant

/-! # Faithful Derivation Commutator -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.FaithfulDerivationCommutator.Construction

noncomputable section

section

/-! The commutator action of the derivation algebra of a Killing
bracket on itself is faithful. -/

open _root_.ContinuousLinearMap

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

theorem derivation_commutator_inner_operator
    (B : L →L[ℝ] L →L[ℝ] L) (A : L →L[ℝ] L)
    (hA : Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B A = 0) (x : L) : A * B x - B x * A = B (A x) := by
  apply ContinuousLinearMap.ext
  intro y
  have he := (OrthogonalBracketAlgebra.Construction.continuousBilinearDerivationDefect_eq_zero_iff B A).mp hA x y
  change A (B x y) - B x (A y) = B (A x) y
  rw [he]
  abel

theorem derivation_commuting_with_derivations_eq_zero
    (B : L →L[ℝ] L →L[ℝ] L) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (A : L →L[ℝ] L) (hA : Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B A = 0)
    (hcomm : ∀ D, Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B D = 0 → Commute A D) : A = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  have hxD : Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B (B x) = 0 := by
    change B x ∈ (Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B).toLinearMap.ker
    rw [ContinuousInnerDerivations.Construction.continuousKillingBracket_derivation_kernel B hB hK]
    exact ⟨x, rfl⟩
  apply ContinuousInnerDerivations.Construction.continuousKillingBracket_injective B hK
  change B (A x) = B (0 : L)
  rw [map_zero]
  rw [← derivation_commutator_inner_operator B A hA x, sub_eq_zero.mpr (hcomm (B x) hxD).eq]

end

/-! Derivations preserve the Killing form infinitesimally. -/

open _root_.ContinuousLinearMap

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

theorem continuousBracketKillingForm_derivation
    (B : L →L[ℝ] L →L[ℝ] L) (A : L →L[ℝ] L)
    (hA : Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B A = 0) (x y : L) :
    ContinuousInnerDerivations.Construction.continuousBracketKillingForm B (A x) y + ContinuousInnerDerivations.Construction.continuousBracketKillingForm B x (A y) = 0 := by
  change Bracket.KillingDeterminant.Construction.continuousEndTrace (B (A x) * B y) + Bracket.KillingDeterminant.Construction.continuousEndTrace (B x * B (A y)) = 0
  rw [← map_add, ← derivation_commutator_inner_operator B A hA x,
    ← derivation_commutator_inner_operator B A hA y]
  have he : (A * B x - B x * A) * B y + B x * (A * B y - B y * A) =
      A * (B x * B y) - (B x * B y) * A := by noncomm_ring
  rw [he, map_sub]
  exact sub_eq_zero.mpr (LinearMap.trace_mul_comm ℝ A.toLinearMap (B x * B y).toLinearMap)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.FaithfulDerivationCommutator.Construction
