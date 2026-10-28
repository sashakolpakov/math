import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.ContinuousMap.Algebra

/-! # Coefficient Topology -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientTopology.Construction

noncomputable section

/-!
# Completion: continuous finite quotients of integral ℓ-adic coefficients

Reduction modulo ℓⁿ is continuous and has a continuous set-theoretic
section. Its kernel on continuous functions consists exactly of multiples
of ℓⁿ, with a continuous quotient function.
-/

variable (ℓ n : ℕ) [Fact ℓ.Prime]

/-- Reduction of integral ℓ-adic coefficients modulo ℓⁿ is continuous. -/
theorem continuous_padicInt_toZModPow : Continuous (PadicInt.toZModPow (p := ℓ) n) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rw [ContinuousAt, nhds_discrete (ZMod (ℓ ^ n)), Filter.tendsto_pure]
  have hp : 0 < (ℓ : ℝ) := by exact_mod_cast (Fact.out : ℓ.Prime).pos
  filter_upwards [Metric.ball_mem_nhds x (zpow_pos hp (-n : ℤ))] with y hy
  apply sub_eq_zero.mp
  rw [← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    ← PadicInt.norm_le_pow_iff_mem_span_pow]
  exact le_of_lt (by simpa only [Metric.mem_ball, dist_eq_norm] using hy)

/-- The canonical finite representatives give a section of reduction. -/
theorem padicInt_toZModPow_section :
    Function.RightInverse (fun a : ZMod (ℓ ^ n) => (a.val : ℤ_[ℓ]))
      (PadicInt.toZModPow n) := by
  intro a
  simp

/-- Continuous functions with zero reduction have continuous quotients by ℓⁿ. -/
theorem continuousMap_padicInt_divisible {T : Type*} [TopologicalSpace T]
    (f : C(T, ℤ_[ℓ])) (hf : ∀ t, PadicInt.toZModPow n (f t) = 0) :
    ∃ g : C(T, ℤ_[ℓ]), ∀ t, (ℓ : ℤ_[ℓ]) ^ n * g t = f t := by
  have ha : (ℓ : ℤ_[ℓ]) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero)
  have hm : Topology.IsEmbedding (fun b : ℤ_[ℓ] => (ℓ : ℤ_[ℓ]) ^ n * b) :=
    ((continuous_const.mul continuous_id).isClosedEmbedding
      (mul_right_injective₀ ha)).isEmbedding
  have he (t : T) : ∃ b : ℤ_[ℓ], (ℓ : ℤ_[ℓ]) ^ n * b = f t := by
    have h := hf t
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h
    obtain ⟨b, hb⟩ := h
    exact ⟨b, hb.symm⟩
  choose g hg using he
  refine ⟨⟨g, hm.isInducing.continuous_iff.mpr ?_⟩, hg⟩
  simpa only [Function.comp_def, hg] using f.continuous

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientTopology.Construction
