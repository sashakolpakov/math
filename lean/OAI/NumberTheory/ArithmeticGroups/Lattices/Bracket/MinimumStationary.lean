import OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.OrbitMinimum
import OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousOperatorExponentialDeterminant
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! # Minimum Stationary -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.MinimumStationary.Construction

noncomputable section

/-! A minimum-norm bracket is orthogonal to every infinitesimal
volume-preserving change of basis. -/

open scoped _root_.Topology
open Filter

theorem min_norm_curve_inner_derivative_zero
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (f : ℝ → V) (v w : V) (hf : HasDerivAt f w 0) (h0 : f 0 = v)
    (hmin : ∀ t, ‖v‖ ≤ ‖f t‖) : inner ℝ w v = 0 := by
  have hm : IsLocalMin (fun t => inner ℝ (f t) (f t)) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    change inner ℝ (f 0) (f 0) ≤ inner ℝ (f t) (f t)
    rw [h0, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg v) (hmin t) 2
  have hd := hm.hasDerivAt_eq_zero (hf.inner ℝ hf)
  rw [h0, real_inner_comm v w] at hd
  rw [real_inner_comm v w]
  linarith

variable {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]

local instance stationaryEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance stationaryEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance stationaryBilinear_normed : NormedAddCommGroup (L →L[ℝ] L →L[ℝ] L) := inferInstance
local instance stationaryBilinear_space : NormedSpace ℝ (L →L[ℝ] L →L[ℝ] L) := inferInstance

theorem exponential_bracket_curve_hasDerivAt
    (B : L →L[ℝ] L →L[ℝ] L) (A : L →L[ℝ] L) :
    HasDerivAt (fun t : ℝ => B + ChangeDerivative.Construction.continuousBracketExponentialPerturbation B (t • A, 0))
      (Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B A) 0 := by
  let p : ℝ → (L →L[ℝ] L) × (L →L[ℝ] L →L[ℝ] L) := fun t => (t • A, 0)
  have hp : HasDerivAt p (A, 0) 0 := by
    simpa only [p, id_eq, one_smul] using
      ((hasDerivAt_id (0 : ℝ)).smul_const A).prodMk
        (hasDerivAt_const (0 : ℝ) (0 : L →L[ℝ] L →L[ℝ] L))
  have hP : HasFDerivAt (ChangeDerivative.Construction.continuousBracketExponentialPerturbation B)
      ((Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B).coprod
        (ContinuousLinearMap.id ℝ (L →L[ℝ] L →L[ℝ] L))) (p 0) := by
    simpa only [p, zero_smul, Prod.zero_eq_mk] using
      (ChangeDerivative.Construction.continuousBracketExponentialPerturbation_hasStrictFDerivAt B).hasFDerivAt
  have hd := (hP.comp_hasDerivAt 0 hp).const_add B
  simpa only [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.id_apply, add_zero] using! hd

theorem minimum_bracket_orthogonal_to_traceless_change
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (Φ : (L →L[ℝ] L →L[ℝ] L) →L[ℝ] V)
    (B : L →L[ℝ] L →L[ℝ] L)
    (hmin : ∀ e : L ≃L[ℝ] L, |LinearMap.det e.toLinearMap| = 1 →
      ‖Φ B‖ ≤ ‖Φ (ContinuousBracketChange.Construction.continuousBracketChange e B)‖)
    (A : L →L[ℝ] L) (hA : LinearMap.trace ℝ L A.toLinearMap = 0) :
    inner ℝ (Φ (Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B A)) (Φ B) = 0 := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  let f : ℝ → V := fun t => Φ (B + ChangeDerivative.Construction.continuousBracketExponentialPerturbation B (t • A, 0))
  have hf : HasDerivAt f (Φ (Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B A)) 0 :=
    Φ.hasFDerivAt.comp_hasDerivAt 0 (exponential_bracket_curve_hasDerivAt B A)
  have h0 : f 0 = Φ B := by
    simp only [f, zero_smul, ← Prod.zero_eq_mk, ChangeDerivative.Construction.continuousBracketExponentialPerturbation_zero, add_zero]
  apply min_norm_curve_inner_derivative_zero f (Φ B) _ hf h0
  intro t
  have ht : LinearMap.trace ℝ L (t • A).toLinearMap = 0 := by
    change LinearMap.trace ℝ L (t • A.toLinearMap) = 0
    rw [map_smul, hA, smul_zero]
  have hdet : |LinearMap.det (ExponentialEquiv.Construction.continuousLinearMapExpEquiv (t • A)).toLinearMap| = 1 := by
    change |LinearMap.det (NormedSpace.exp (t • A)).toLinearMap| = 1
    rw [ContinuousOperatorExponentialDeterminant.Construction.continuousOperator_exp_det_one_of_trace_zero _ ht, abs_one]
  have he := hmin (ExponentialEquiv.Construction.continuousLinearMapExpEquiv (t • A)) hdet
  simpa only [f, ExponentialEquiv.Construction.continuousBracketExponentialPerturbation_add, add_zero] using he

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.MinimumStationary.Construction
