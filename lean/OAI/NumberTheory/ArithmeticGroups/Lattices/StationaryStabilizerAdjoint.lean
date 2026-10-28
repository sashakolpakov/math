import OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.MinimumStationary
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Stationary Stabilizer Adjoint -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.StationaryStabilizerAdjoint.Construction

noncomputable section

/-! A stationary vector for a representation compatible with adjoints
has a stabilizer closed under taking adjoints. -/

open _root_.ContinuousLinearMap

theorem commutator_adjoint_inner
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (T : V →L[ℝ] V) (v : V) :
    inner ℝ ((T * adjoint T - adjoint T * T) v) v =
      ‖adjoint T v‖ ^ 2 - ‖T v‖ ^ 2 := by
  simp only [sub_apply, mul_apply_eq_comp, inner_sub_left]
  have hleft : inner ℝ (T (adjoint T v)) v = ‖adjoint T v‖ ^ 2 :=
    (adjoint_inner_right T (adjoint T v) v).symm.trans (real_inner_self_eq_norm_sq _)
  have hright : inner ℝ (adjoint T (T v)) v = ‖T v‖ ^ 2 :=
    (adjoint_inner_left T v (T v)).trans (real_inner_self_eq_norm_sq _)
  rw [hleft, hright]

theorem adjoint_kills_of_stationary_commutator
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (T : V →L[ℝ] V) (v : V) (hT : T v = 0)
    (hstat : inner ℝ ((T * adjoint T - adjoint T * T) v) v = 0) : adjoint T v = 0 := by
  rw [commutator_adjoint_inner, hT, norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero] at hstat
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hstat)

theorem stationary_stabilizer_adjoint
    {L V : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [CompleteSpace L]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (ρ : (L →L[ℝ] L) →ₗ[ℝ] (V →L[ℝ] V))
    (hcomm : ∀ A B, ρ (A * B - B * A) = ρ A * ρ B - ρ B * ρ A)
    (hadj : ∀ A, ρ (adjoint A) = adjoint (ρ A))
    (v : V)
    (hstat : ∀ A, LinearMap.trace ℝ L A.toLinearMap = 0 → inner ℝ (ρ A v) v = 0)
    (A : L →L[ℝ] L) (hA : ρ A v = 0) : ρ (adjoint A) v = 0 := by
  rw [hadj]
  apply adjoint_kills_of_stationary_commutator (ρ A) v hA
  rw [← hadj, ← hcomm]
  apply hstat
  change LinearMap.trace ℝ L (A.toLinearMap * (adjoint A).toLinearMap -
    (adjoint A).toLinearMap * A.toLinearMap) = 0
  rw [map_sub, LinearMap.trace_mul_comm, sub_self]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.StationaryStabilizerAdjoint.Construction
