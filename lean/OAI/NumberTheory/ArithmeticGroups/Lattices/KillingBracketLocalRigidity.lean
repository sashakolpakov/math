import OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousInnerDerivations
import OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.ExponentialEquiv
import OAI.NumberTheory.ArithmeticGroups.Lattices.ZeroSetLocalOrbit

/-! # Killing Bracket Local Rigidity -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.KillingBracketLocalRigidity.Construction

noncomputable section

/-! A real finite-dimensional Lie bracket with nondegenerate Killing
form is locally rigid: every sufficiently close Lie bracket is
obtained by a continuous change of basis. -/

open scoped _root_.Topology
open Filter Set NormedSpace

variable {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]

local instance rigidEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance rigidEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance rigidEnd_finite : FiniteDimensional ℝ (L →L[ℝ] L) := inferInstance
local instance rigidBilinear_normed : NormedAddCommGroup (L →L[ℝ] L →L[ℝ] L) := inferInstance
local instance rigidBilinear_space : NormedSpace ℝ (L →L[ℝ] L →L[ℝ] L) := inferInstance
local instance rigidBilinear_finite : FiniteDimensional ℝ (L →L[ℝ] L →L[ℝ] L) := inferInstance
local instance rigidTrilinear_normed : NormedAddCommGroup (L →L[ℝ] L →L[ℝ] L →L[ℝ] L) := inferInstance
local instance rigidTrilinear_space : NormedSpace ℝ (L →L[ℝ] L →L[ℝ] L →L[ℝ] L) := inferInstance
local instance rigidJacobiOperator_normed : NormedAddCommGroup
    ((L →L[ℝ] L →L[ℝ] L) →L[ℝ] (L →L[ℝ] L →L[ℝ] L →L[ℝ] L)) := inferInstance
local instance rigidJacobiOperator_space : NormedSpace ℝ
    ((L →L[ℝ] L →L[ℝ] L) →L[ℝ] (L →L[ℝ] L →L[ℝ] L →L[ℝ] L)) := inferInstance
local instance rigidJacobiPair_normed : NormedAddCommGroup
    ((L →L[ℝ] L →L[ℝ] L) →L[ℝ]
      (L →L[ℝ] L →L[ℝ] L) →L[ℝ] (L →L[ℝ] L →L[ℝ] L →L[ℝ] L)) := inferInstance

theorem killing_bracket_local_exponential_orbit
    (B : L →L[ℝ] L →L[ℝ] L) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate) :
    ∀ᶠ C in 𝓝 (0 : L →L[ℝ] L →L[ℝ] L), ContinuousBracketConstraints.Construction.IsContinuousLieBracket (B + C) →
      ∃ A : L →L[ℝ] L, Bracket.ChangeDerivative.Construction.continuousBracketExponentialPerturbation B (A, 0) = C := by
  exact ZeroSetLocalOrbit.Construction.quadratic_zero_set_local_orbit_of_range
    (E := L →L[ℝ] L) (V := L →L[ℝ] L →L[ℝ] L)
    (F := (L →L[ℝ] L →L[ℝ] L) × (L →L[ℝ] L →L[ℝ] L →L[ℝ] L))
    (fun C => ContinuousBracketConstraints.Construction.IsContinuousLieBracket (B + C)) (ContinuousBracketConstraints.Construction.continuousBracketLinearization B)
    (Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B) (ContinuousInnerDerivations.Construction.continuousBracketLinearization_kernel B hB hK).symm
    ‖ContinuousJacobi.Construction.continuousJacobiPair (L := L)‖ (norm_nonneg (ContinuousJacobi.Construction.continuousJacobiPair (L := L)))
    (fun C hC => ContinuousBracketConstraints.Construction.continuousBracketLinearization_norm_bound B C hB hC)
    (Bracket.ChangeDerivative.Construction.continuousBracketExponentialPerturbation B)
    (Bracket.ChangeDerivative.Construction.continuousBracketExponentialPerturbation_zero B)
    (Bracket.ChangeDerivative.Construction.continuousBracketExponentialPerturbation_hasStrictFDerivAt B)
    (fun A C => (Bracket.ExponentialEquiv.Construction.continuousBracketExponentialPerturbation_preserves B C A).mp)

theorem killing_bracket_local_rigidity
    (B : L →L[ℝ] L →L[ℝ] L) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate) :
    ∀ᶠ C in 𝓝 B, ContinuousBracketConstraints.Construction.IsContinuousLieBracket C →
      ∃ e : L ≃L[ℝ] L, C = ContinuousBracketChange.Construction.continuousBracketChange e B := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  have ht : Tendsto (fun C : L →L[ℝ] L →L[ℝ] L => C - B) (𝓝 B) (𝓝 0) := by
    have hc : Continuous (fun C : L →L[ℝ] L →L[ℝ] L => C - B) :=
      continuous_id.sub continuous_const
    simpa only [sub_self] using hc.tendsto B
  filter_upwards [ht.eventually (killing_bracket_local_exponential_orbit B hB hK)] with C hC
  intro hLie
  obtain ⟨A, hA⟩ := hC (by simpa only [add_sub_cancel] using hLie)
  refine ⟨Bracket.ExponentialEquiv.Construction.continuousLinearMapExpEquiv A, ?_⟩
  have he := Bracket.ExponentialEquiv.Construction.continuousBracketExponentialPerturbation_add B 0 A
  rw [hA, add_sub_cancel, add_zero] at he
  exact he

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.KillingBracketLocalRigidity.Construction
