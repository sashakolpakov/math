import OAI.Analysis.Calculus.Current.Physical.Parameters

/-! Uniform first-derivative bounds for the genuine physical fiber parametrization. -/

noncomputable section
namespace OAI.Analysis.Calculus.Current

def physicalInverseFamily {d : ℕ} (p : ℝ × (ℂ × (Option (Fin d) → ℂ))) :
    Option (Fin d) → ℂ := physicalFiberInverse p.1 p.2.1 p.2.2

theorem contDiffAt_physicalInverseFamily {d : ℕ} (a : ℝ) (τ : ℂ)
    (u : Option (Fin d) → ℂ) (hD : fiberDenominator (fun i => u (some i)) ≠ 0) :
    ContDiffAt ℝ ⊤ (physicalInverseFamily (d := d)) (a, τ, u) := by
  have hN : ContDiffAt ℝ ⊤
      (fun p : ℝ × (ℂ × (Option (Fin d) → ℂ)) =>
        Real.sqrt 2 • p.2.1 + p.1 • p.2.2 none) (a, τ, u) := by fun_prop
  have hDen : ContDiffAt ℝ ⊤
      (fun p : ℝ × (ℂ × (Option (Fin d) → ℂ)) =>
        fiberDenominator (fun i => p.2.2 (some i))) (a, τ, u) := by
    unfold fiberDenominator fiberQuadratic
    fun_prop
  have hH : ContDiffAt ℝ ⊤
      (fun p : ℝ × (ℂ × (Option (Fin d) → ℂ)) => inverseHeight p.1 p.2.1 p.2.2)
      (a, τ, u) := by
    simpa only [inverseHeight, div_eq_mul_inv, Pi.inv_apply] using! hN.mul (hDen.inv hD)
  apply contDiffAt_pi.mpr
  intro i
  cases i with
  | none =>
    change ContDiffAt ℝ ⊤
      (fun p : ℝ × (ℂ × (Option (Fin d) → ℂ)) =>
        Real.sqrt 2 • inverseHeight p.1 p.2.1 p.2.2 - p.2.1) (a, τ, u)
    exact (hH.const_smul (Real.sqrt 2)).sub (by fun_prop)
  | some i =>
    change ContDiffAt ℝ ⊤
      (fun p : ℝ × (ℂ × (Option (Fin d) → ℂ)) =>
        p.2.2 (some i) * inverseHeight p.1 p.2.1 p.2.2) (a, τ, u)
    exact (by fun_prop : ContDiffAt ℝ ⊤
      (fun p : ℝ × (ℂ × (Option (Fin d) → ℂ)) => p.2.2 (some i)) (a, τ, u)).mul hH

def boundedInverseParameters (d : ℕ) : Set (ℝ × (ℂ × (Option (Fin d) → ℂ))) :=
  Set.Icc 0 4 ×ˢ (Metric.closedBall (0 : ℂ) 4 ×ˢ fiberParameterBall d)

theorem isCompact_boundedInverseParameters (d : ℕ) :
    IsCompact (boundedInverseParameters d) :=
  isCompact_Icc.prod ((isCompact_closedBall (0 : ℂ) 4).prod (isCompact_fiberParameterBall d))

/-- The bound includes differentiation in the scale, time, and ellipsoid coordinates.
It remains valid at scale zero, although the parametrization is then not invertible. -/
theorem physicalInverseFamily_fderiv_uniform_bound (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ) (τ : ℂ) (u : Option (Fin d) → ℂ),
      0 ≤ a → a ≤ 4 → ‖τ‖ ≤ 4 → u ∈ fiberParameterBall d →
      ‖fderiv ℝ (physicalInverseFamily (d := d)) (a, τ, u)‖ ≤ C := by
  have hc : ContinuousOn
      (fun p => ‖fderiv ℝ (physicalInverseFamily (d := d)) p‖)
      (boundedInverseParameters d) := by
    intro p hp
    exact ((contDiffAt_physicalInverseFamily p.1 p.2.1 p.2.2
      (fiberParameterBall_denominator hp.2.2)).continuousAt_fderiv (by norm_num)).norm.continuousWithinAt
  obtain ⟨B, hB⟩ := (isCompact_boundedInverseParameters d).exists_bound_of_continuousOn hc
  refine ⟨|B| + 1, by positivity, ?_⟩
  intro a τ u ha ha' ht hu
  have hp : (a, τ, u) ∈ boundedInverseParameters d :=
    ⟨⟨ha, ha'⟩, by simpa only [Metric.mem_closedBall, dist_zero_right] using ht, hu⟩
  have hb := hB _ hp
  simpa only [Real.norm_eq_abs, abs_norm] using
    hb.trans (show B ≤ |B| + 1 by linarith [le_abs_self B])

theorem convex_fiberParameterBall (d : ℕ) : Convex ℝ (fiberParameterBall d) := by
  intro u hu v hv a b ha hb hab
  have hcoord (i : Option (Fin d)) :
      ‖a • u i + b • v i‖ ^ 2 ≤ a * ‖u i‖ ^ 2 + b * ‖v i‖ ^ 2 := by
    have hn : ‖a • u i + b • v i‖ ≤ a * ‖u i‖ + b * ‖v i‖ := by
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
        using norm_add_le (a • u i) (b • v i)
    have hid : a * ‖u i‖ ^ 2 + b * ‖v i‖ ^ 2 -
        (a * ‖u i‖ + b * ‖v i‖) ^ 2 = a * b * (‖u i‖ - ‖v i‖) ^ 2 := by
      have hb' : b = 1 - a := by linarith
      rw [hb']
      ring
    have hpos := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (‖u i‖ - ‖v i‖))
    nlinarith [norm_nonneg (a • u i + b • v i),
      mul_nonneg ha (norm_nonneg (u i)), mul_nonneg hb (norm_nonneg (v i))]
  change (∑ i, ‖a • u i + b • v i‖ ^ 2) ≤ (1 / 100 : ℝ)
  calc
    _ ≤ ∑ i, (a * ‖u i‖ ^ 2 + b * ‖v i‖ ^ 2) := Finset.sum_le_sum (fun i _ => hcoord i)
    _ = a * (∑ i, ‖u i‖ ^ 2) + b * (∑ i, ‖v i‖ ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ a * (1 / 100) + b * (1 / 100) :=
      add_le_add (mul_le_mul_of_nonneg_left hu ha) (mul_le_mul_of_nonneg_left hv hb)
    _ = 1 / 100 := by linarith

theorem convex_boundedInverseParameters (d : ℕ) : Convex ℝ (boundedInverseParameters d) :=
  (convex_Icc (0 : ℝ) 4).prod ((convex_closedBall (0 : ℂ) 4).prod (convex_fiberParameterBall d))

theorem physicalInverseFamily_lipschitz (d : ℕ) :
    ∃ C : NNReal, 0 < C ∧ LipschitzOnWith C (physicalInverseFamily (d := d))
      (boundedInverseParameters d) := by
  obtain ⟨C, hC, hbound⟩ := physicalInverseFamily_fderiv_uniform_bound d
  refine ⟨⟨C, hC.le⟩, hC, ?_⟩
  apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ) ?_ ?_
    (convex_boundedInverseParameters d)
  · intro p hp
    exact (contDiffAt_physicalInverseFamily p.1 p.2.1 p.2.2
      (fiberParameterBall_denominator hp.2.2)).differentiableAt (by norm_num)
  · intro p hp
    change ‖fderiv ℝ (physicalInverseFamily (d := d)) p‖ ≤ C
    apply hbound p.1 p.2.1 p.2.2 hp.1.1 hp.1.2 _ hp.2.2
    simpa only [Metric.mem_closedBall, dist_zero_right] using hp.2.1

end OAI.Analysis.Calculus.Current
