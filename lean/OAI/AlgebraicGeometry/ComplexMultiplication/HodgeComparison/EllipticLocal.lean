import Mathlib.Analysis.Distribution.Sobolev

/-! # Elliptic Local -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EllipticLocal.CM.Construction

noncomputable section

/-! Constant-coefficient elliptic inversion for the analytic existence step in HodgeComparison. -/

open FourierTransform TemperedDistribution _root_.MeasureTheory ENNReal
open scoped SchwartzMap Laplacian

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Fourier multipliers add when their symbols have temperate growth. -/
theorem fourierMultiplier_add {g h : E → ℂ}
    (hg : g.HasTemperateGrowth) (hh : h.HasTemperateGrowth) (u : 𝓢'(E, F)) :
    fourierMultiplierCLM F (g + h) u =
      fourierMultiplierCLM F g u + fourierMultiplierCLM F h u := by
  simp only [fourierMultiplierCLM_apply, smulLeftCLM_add hg hh,
    add_apply, fourierInv_add]

/-- The order-two Bessel operator is the normalized shifted Euclidean Laplacian. -/
theorem besselPotential_two_eq_shiftedLaplacian (u : 𝓢'(E, F)) :
    besselPotential E F 2 u = u - (((2 * Real.pi) ^ 2)⁻¹ : ℝ) • Δ u := by
  have hs : (fun x : E => (((1 + ‖x‖ ^ 2) ^ ((2 : ℝ) / 2) : ℝ) : ℂ)) =
      (fun _ : E => (1 : ℂ)) + (fun x : E => ((‖x‖ ^ 2 : ℝ) : ℂ)) := by
    ext x
    simp
  rw [besselPotential, hs, fourierMultiplier_add (by fun_prop) (by fun_prop),
    fourierMultiplierCLM_const, one_smul, ContinuousLinearMap.id_apply,
    TemperedDistribution.laplacian_eq_fourierMultiplierCLM, smul_smul]
  have hn : (2 * Real.pi) ^ 2 ≠ 0 := pow_ne_zero _ (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  rw [mul_neg, inv_mul_cancel₀ hn, neg_one_smul, sub_neg_eq_add]

/-- The inverse Fourier multiplier solves the shifted Euclidean Poisson equation. -/
theorem besselPotential_neg_two_solves (f : 𝓢'(E, F)) :
    besselPotential E F (-2) f - (((2 * Real.pi) ^ 2)⁻¹ : ℝ) •
      Δ (besselPotential E F (-2) f) = f := by
  rw [← besselPotential_two_eq_shiftedLaplacian, besselPotential_besselPotential_apply]
  norm_num

/-- This shifted equation has a unique tempered-distribution solution. -/
theorem shiftedLaplacian_existsUnique (f : 𝓢'(E, F)) :
    ∃! u : 𝓢'(E, F), u - (((2 * Real.pi) ^ 2)⁻¹ : ℝ) • Δ u = f := by
  refine ⟨besselPotential E F (-2) f, besselPotential_neg_two_solves f, ?_⟩
  intro u hu
  rw [← besselPotential_two_eq_shiftedLaplacian] at hu
  have h := congrArg (besselPotential E F (-2)) hu
  simpa only [besselPotential_besselPotential_apply, add_neg_cancel,
    besselPotential_zero, ContinuousLinearMap.id_apply] using h

variable [CompleteSpace F]

/-- The inverse gains two Sobolev derivatives. -/
theorem besselPotential_neg_two_regularity {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {f : 𝓢'(E, F)} (hf : MemSobolev s p f) :
    MemSobolev (s + 2) p (besselPotential E F (-2) f) := by
  rw [memSobolev_besselPotential_iff]
  convert hf using 1
  ring

/-- Euclidean elliptic regularity: controlling a distribution and its Laplacian
in the same Sobolev space gives two additional derivatives. -/
theorem laplacian_sobolev_regularity {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {u : 𝓢'(E, F)} (hu : MemSobolev s p u) (hΔ : MemSobolev s p (Δ u)) :
    MemSobolev (s + 2) p u := by
  have hscalar : MemSobolev s p ((((2 * Real.pi) ^ 2)⁻¹ : ℝ) • Δ u) := by
    simpa only [Complex.coe_smul] using
      hΔ.smul ((((2 * Real.pi) ^ 2)⁻¹ : ℝ) : ℂ)
  have h := besselPotential_neg_two_regularity (hu.sub hscalar)
  rw [← besselPotential_two_eq_shiftedLaplacian, besselPotential_besselPotential_apply] at h
  norm_num at h
  exact h

/-- The embedding of smooth rapidly decreasing functions into distributions is faithful. -/
theorem schwartz_toTemperedDistribution_injective :
    Function.Injective (fun f : 𝓢(E, F) => (f : 𝓢'(E, F))) := by
  intro f g h
  apply SchwartzMap.injective_toLp 2 (volume : Measure E)
  have hi : Function.Injective (Lp.toTemperedDistributionCLM F (volume : Measure E) 2) :=
    LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := F)
      (μ := (volume : Measure E)) (p := 2))
  apply hi
  simpa only [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_toLp_eq] using h

/-- A smooth rapidly decreasing inverse for the shifted Euclidean Laplacian. -/
def schwartzLaplacianResolvent (f : 𝓢(E, F)) : 𝓢(E, F) :=
  SchwartzMap.fourierMultiplierCLM F
    (fun x : E => (((1 + ‖x‖ ^ 2) ^ (-1 : ℝ) : ℝ) : ℂ)) f

/-- The smooth inverse agrees with the inverse on genuine distributions. -/
theorem schwartzLaplacianResolvent_distribution (f : 𝓢(E, F)) :
    (schwartzLaplacianResolvent f : 𝓢'(E, F)) =
      besselPotential E F (-2) (f : 𝓢'(E, F)) := by
  unfold schwartzLaplacianResolvent besselPotential
  norm_num only [show (-2 : ℝ) / 2 = -1 by norm_num]
  exact (fourierMultiplierCLM_toTemperedDistributionCLM_eq (by fun_prop) f).symm

/-- The Schwartz inverse solves the ordinary differential equation on smooth functions. -/
theorem schwartzLaplacianResolvent_solves (f : 𝓢(E, F)) :
    schwartzLaplacianResolvent f - (((2 * Real.pi) ^ 2)⁻¹ : ℝ) •
      Δ (schwartzLaplacianResolvent f) = f := by
  apply schwartz_toTemperedDistribution_injective
  change SchwartzMap.toTemperedDistributionCLM E F (volume : Measure E)
    (schwartzLaplacianResolvent f - (((2 * Real.pi) ^ 2)⁻¹ : ℝ) •
      Δ (schwartzLaplacianResolvent f)) = (f : 𝓢'(E, F))
  rw [map_sub, ContinuousLinearMap.map_smul_of_tower,
    ← TemperedDistribution.laplacian_toTemperedDistributionCLM_eq,
    schwartzLaplacianResolvent_distribution]
  exact besselPotential_neg_two_solves _

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EllipticLocal.CM.Construction
