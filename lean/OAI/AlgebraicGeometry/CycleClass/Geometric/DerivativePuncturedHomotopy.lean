import OAI.AlgebraicGeometry.CycleClass.Geometric.NormalSphere
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-! # Derivative Punctured Homotopy -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.DerivativePuncturedHomotopy.Cycles

noncomputable section

/-!
# A differentiable germ and its invertible derivative on a punctured ball

An invertible derivative controls the error relative to the derivative's own
norm. On a sufficiently small punctured ball, the straight line between the
translated map and its derivative consequently avoids zero. This constructs
the local topological homotopy needed for comparing nonlinear coordinate
changes with their linear derivatives. No local orientation class or excision
theorem is assumed.
-/

open Filter Set
open scoped _root_.Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative error is eventually at most half the derivative norm. -/
theorem eventually_derivative_remainder_small {f : E → F} (L : E ≃L[ℝ] F)
    (hf : HasFDerivAt f (L : E →L[ℝ] F) 0) :
    ∀ᶠ x in 𝓝 (0 : E), ‖f x - f 0 - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖ := by
  have h := (hf.isEquivalent_sub L.toHomeomorph.isInducing).isLittleO
  simpa only [Pi.sub_apply, sub_zero, ContinuousLinearEquiv.coe_coe] using
    h.bound (by norm_num : (0 : ℝ) < 1 / 2)

/-- A perturbation by at most half the norm stays away from zero throughout
the straight-line interpolation. -/
theorem straightLine_ne_zero_of_half_norm {u v : F} (hu : u ≠ 0)
    (herror : ‖v - u‖ ≤ (1 / 2 : ℝ) * ‖u‖) (t : unitInterval) :
    u + (t : ℝ) • (v - u) ≠ 0 := by
  intro hzero
  have hnorm : ‖u‖ = ‖(t : ℝ) • (v - u)‖ := by
    calc
      ‖u‖ = ‖-((t : ℝ) • (v - u))‖ := congrArg norm (eq_neg_of_add_eq_zero_left hzero)
      _ = ‖(t : ℝ) • (v - u)‖ := norm_neg _
  have hbound : ‖(t : ℝ) • (v - u)‖ ≤ (1 / 2 : ℝ) * ‖u‖ := by
    calc
      ‖(t : ℝ) • (v - u)‖ = (t : ℝ) * ‖v - u‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1]
      _ ≤ ‖v - u‖ := mul_le_of_le_one_left (norm_nonneg _) t.property.2
      _ ≤ (1 / 2 : ℝ) * ‖u‖ := herror
  have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  linarith

/-- The actual punctured ball in a normed model space. -/
abbrev PuncturedBall (E : Type*) [NormedAddCommGroup E] (r : ℝ) :=
  {x : E // x ≠ 0 ∧ ‖x‖ < r}

/-- Restriction of an invertible linear derivative to a punctured ball. -/
def puncturedBallLinearMap (L : E ≃L[ℝ] F) (r : ℝ) :
    C(PuncturedBall E r, NormalSphere.Cycles.PuncturedNormal F) where
  toFun x := ⟨L x.1, by
    change L x.1 ≠ 0
    intro hx
    exact x.property.1 (L.injective (by simpa only [map_zero] using hx))⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact L.continuous.comp continuous_subtype_val

/-- Restriction of the translated nonlinear map; the quantitative error
estimate proves its values avoid zero. -/
def puncturedBallTranslatedMap {f : E → F} (L : E ≃L[ℝ] F) (r : ℝ)
    (hc : ContinuousOn f (Metric.ball 0 r))
    (he : ∀ x, ‖x‖ < r → ‖f x - f 0 - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖) :
    C(PuncturedBall E r, NormalSphere.Cycles.PuncturedNormal F) where
  toFun x := ⟨f x.1 - f 0, by
    change f x.1 - f 0 ≠ 0
    have hL : L x.1 ≠ 0 := by
      intro hx
      exact x.property.1 (L.injective (by simpa only [map_zero] using hx))
    simpa using straightLine_ne_zero_of_half_norm hL (he x.1 x.property.2)
      (1 : unitInterval)⟩
  continuous_toFun := by
    have hfc : Continuous (fun x : PuncturedBall E r => f x.1) := by
      apply hc.comp_continuous continuous_subtype_val
      intro x
      simpa only [Metric.mem_ball, dist_zero_right] using x.property.2
    exact (hfc.sub continuous_const).subtype_mk _

/-- The actual zero-avoiding homotopy between the derivative and the
translated nonlinear map on the chosen punctured ball. -/
def derivativePuncturedBallHomotopy {f : E → F} (L : E ≃L[ℝ] F) (r : ℝ)
    (hc : ContinuousOn f (Metric.ball 0 r))
    (he : ∀ x, ‖x‖ < r → ‖f x - f 0 - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖) :
    ContinuousMap.Homotopy (puncturedBallLinearMap L r)
      (puncturedBallTranslatedMap L r hc he) where
  toFun z := ⟨L z.2.1 + (z.1 : ℝ) • (f z.2.1 - f 0 - L z.2.1), by
    change L z.2.1 + (z.1 : ℝ) • ((f z.2.1 - f 0) - L z.2.1) ≠ 0
    apply straightLine_ne_zero_of_half_norm
    · intro hx
      exact z.2.property.1 (L.injective (by simpa only [map_zero] using hx))
    · exact he z.2.1 z.2.property.2⟩
  continuous_toFun := by
    have hfc : Continuous (fun x : PuncturedBall E r => f x.1) := by
      apply hc.comp_continuous continuous_subtype_val
      intro x
      simpa only [Metric.mem_ball, dist_zero_right] using x.property.2
    exact ((L.continuous.comp (continuous_subtype_val.comp continuous_snd)).add
      ((continuous_subtype_val.comp continuous_fst).smul
        (((hfc.comp continuous_snd).sub continuous_const).sub
          (L.continuous.comp (continuous_subtype_val.comp continuous_snd))))).subtype_mk _
  map_zero_left x := by
    apply Subtype.ext
    simp [puncturedBallLinearMap]
  map_one_left x := by
    apply Subtype.ext
    simp [puncturedBallTranslatedMap]

/-- Differentiability with an invertible derivative supplies a positive
radius on which the nonlinear germ has the explicit punctured homotopy. -/
theorem exists_derivativePuncturedBallHomotopy {f : E → F}
    (L : E ≃L[ℝ] F) (hf : HasFDerivAt f (L : E →L[ℝ] F) 0)
    {U : Set E} (hU : U ∈ 𝓝 (0 : E)) (hc : ContinuousOn f U) :
    ∃ r : ℝ, 0 < r ∧ ∃ (hc' : ContinuousOn f (Metric.ball 0 r))
      (he : ∀ x, ‖x‖ < r → ‖f x - f 0 - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖),
      Nonempty (ContinuousMap.Homotopy (puncturedBallLinearMap L r)
        (puncturedBallTranslatedMap L r hc' he)) := by
  have hmem : U ∩ {x | ‖f x - f 0 - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖} ∈
      𝓝 (0 : E) := inter_mem hU (eventually_derivative_remainder_small L hf)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hmem
  have hc' : ContinuousOn f (Metric.ball 0 r) := hc.mono fun x hx => (hball hx).1
  have he : ∀ x, ‖x‖ < r → ‖f x - f 0 - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖ := by
    intro x hx
    exact (hball (by simpa only [Metric.mem_ball, dist_zero_right] using hx)).2
  exact ⟨r, hr, hc', he, ⟨derivativePuncturedBallHomotopy L r hc' he⟩⟩

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.DerivativePuncturedHomotopy.Cycles
