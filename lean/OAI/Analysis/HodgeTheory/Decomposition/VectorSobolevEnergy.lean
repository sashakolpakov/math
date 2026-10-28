import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.FourierEnergy

/-! # Vector Sobolev Energy -/

namespace OAI.Analysis.HodgeTheory.Decomposition.VectorSobolevEnergy.Constructions

noncomputable section

/-! Fourier energy identities for vector-valued Sobolev coordinates. -/

open _root_.MeasureTheory FourierTransform
open scoped SchwartzMap

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.FourierEnergy.CM.Construction

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- A pointwise square partition of Fourier symbols preserves the Hilbert inner product. -/
theorem vectorL2FourierPartition_inner {ι : Type*} [Fintype ι]
    (g : ι → E → ℂ) (hg : ∀ i, (g i).HasTemperateGrowth)
    (C : ι → ℝ) (hC : ∀ i x, ‖g i x‖ ≤ C i)
    (hpartition : ∀ x, ∑ i, star (g i x) * g i x = 1)
    (f h : Lp F 2 (volume : Measure E)) :
    ∑ i, inner ℂ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.l2FourierMultiplier (hg i) (hC i) f)
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.l2FourierMultiplier (hg i) (hC i) h) = inner ℂ f h := by
  let T := fun i => AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.l2FourierMultiplier (hg i) (hC i) (F := F)
  have hfae : ∀ᵐ x ∂(volume : Measure E), ∀ i,
      (𝓕 (T i f) : Lp F 2 (volume : Measure E)) x = g i x • (𝓕 f) x :=
    ae_all_iff.mpr (fun i => AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpLocalization.CM.Construction.fourierMultiplier_l2_fourier_coeFn (hg i) (hC i) f (T i f)
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.l2FourierMultiplier_distribution (hg i) (hC i) f))
  have hhae : ∀ᵐ x ∂(volume : Measure E), ∀ i,
      (𝓕 (T i h) : Lp F 2 (volume : Measure E)) x = g i x • (𝓕 h) x :=
    ae_all_iff.mpr (fun i => AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpLocalization.CM.Construction.fourierMultiplier_l2_fourier_coeFn (hg i) (hC i) h (T i h)
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.l2FourierMultiplier_distribution (hg i) (hC i) h))
  calc
    _ = ∑ i, ∫ x, inner ℂ ((𝓕 (T i f) : Lp F 2 (volume : Measure E)) x)
        ((𝓕 (T i h) : Lp F 2 (volume : Measure E)) x) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Lp.inner_fourier_eq, L2.inner_def]
    _ = ∫ x, ∑ i, inner ℂ ((𝓕 (T i f) : Lp F 2 (volume : Measure E)) x)
        ((𝓕 (T i h) : Lp F 2 (volume : Measure E)) x) :=
      (integral_finsetSum Finset.univ (fun i _ => L2.integrable_inner (𝕜 := ℂ) (𝓕 (T i f))
        (𝓕 (T i h)))).symm
    _ = ∫ x, inner ℂ ((𝓕 f : Lp F 2 (volume : Measure E)) x)
        ((𝓕 h : Lp F 2 (volume : Measure E)) x) := by
      apply integral_congr_ae
      filter_upwards [hfae, hhae] with x hx hy
      simp only [hx, hy, inner_smul_left, inner_smul_right]
      calc
        _ = (∑ i, star (g i x) * g i x) *
            inner ℂ ((𝓕 f : Lp F 2 (volume : Measure E)) x)
              ((𝓕 h : Lp F 2 (volume : Measure E)) x) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          change g i x * (star (g i x) * _) = _
          ring
        _ = _ := by rw [hpartition, one_mul]
    _ = inner ℂ f h := by rw [← L2.inner_def, Lp.inner_fourier_eq]

/-- The normalized gradient, with its actual directional components in a Hilbert direct sum. -/
def vectorSobolevNormalizedGradient {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) :
    Lp F 2 (volume : Measure E) →L[ℂ] PiLp 2 (fun _ : ι => Lp F 2 (volume : Measure E)) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => Lp F 2 (volume : Measure E))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.l2FourierMultiplier
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.FourierEnergy.CM.Construction.sobolevEnergySymbol_temperate b (some i)) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.FourierEnergy.CM.Construction.sobolevEnergySymbol_bound b (some i))))

theorem vectorSobolevNormalizedGradient_apply {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (f : Lp F 2 (volume : Measure E)) (i : ι) :
    vectorSobolevNormalizedGradient b f i = AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.l2FourierMultiplier
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.FourierEnergy.CM.Construction.sobolevEnergySymbol_temperate b (some i)) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.FourierEnergy.CM.Construction.sobolevEnergySymbol_bound b (some i)) f := rfl

/-- Each normalized gradient component is exactly the native weak derivative divided by 2πi. -/
theorem vectorSobolevNormalizedGradient_derivative {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (f : Lp F 2 (volume : Measure E)) (i : ι) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDifferential.CM.Construction.sobolevL2Derivative (b i) f = (2 * Real.pi * Complex.I : ℂ) • vectorSobolevNormalizedGradient b f i := by
  rw [vectorSobolevNormalizedGradient_apply]
  change (2 * Real.pi * Complex.I : ℂ) •
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.l2FourierMultiplier (g := fun x : E =>
      Complex.ofReal (inner ℝ x (b i) * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ)))
      (by fun_prop) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Bounds.CM.Construction.normalizedDerivativeSymbol_bound (b i)) f = _
  apply congrArg (fun v : Lp F 2 (volume : Measure E) => (2 * Real.pi * Complex.I : ℂ) • v)
  apply (LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
    (F := F) (μ := (volume : Measure E)) (p := 2)))
  change (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.l2FourierMultiplier (g := fun x : E =>
      Complex.ofReal (inner ℝ x (b i) * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ)))
      (by fun_prop) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Bounds.CM.Construction.normalizedDerivativeSymbol_bound (b i)) f : TemperedDistribution E F) =
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.l2FourierMultiplier (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.FourierEnergy.CM.Construction.sobolevEnergySymbol_temperate b (some i))
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.FourierEnergy.CM.Construction.sobolevEnergySymbol_bound b (some i)) f : TemperedDistribution E F)
  rw [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.l2FourierMultiplier_distribution, AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.l2FourierMultiplier_distribution]
  rfl

theorem vectorSobolev_derivative_energy {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (f h : Lp F 2 (volume : Measure E)) :
    ∑ i, inner ℂ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDifferential.CM.Construction.sobolevL2Derivative (b i) f) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDifferential.CM.Construction.sobolevL2Derivative (b i) h) =
      (((2 * Real.pi) ^ 2 : ℝ) : ℂ) *
        inner ℂ (vectorSobolevNormalizedGradient b f) (vectorSobolevNormalizedGradient b h) := by
  let c : ℂ := 2 * Real.pi * Complex.I
  have hc : c * star c = (((2 * Real.pi) ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hn : ‖c‖ = 2 * Real.pi := by
      dsimp [c]
      simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [hn]
  rw [PiLp.inner_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [vectorSobolevNormalizedGradient_derivative, vectorSobolevNormalizedGradient_derivative,
    inner_smul_left, inner_smul_right]
  change star c * (c * _) = _
  rw [← mul_assoc, mul_comm (star c) c, hc]

/-- The usual H¹ graph inner product agrees exactly with the Bessel-coordinate Hilbert product. -/
theorem vectorSobolev_graph_inner {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (f h : Lp F 2 (volume : Measure E)) :
    inner ℂ f h = inner ℂ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) f)
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) h) +
      inner ℂ (vectorSobolevNormalizedGradient b f) (vectorSobolevNormalizedGradient b h) := by
  have henergy := vectorL2FourierPartition_inner (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.FourierEnergy.CM.Construction.sobolevEnergySymbol b)
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.FourierEnergy.CM.Construction.sobolevEnergySymbol_temperate b) (fun _ => 1) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.FourierEnergy.CM.Construction.sobolevEnergySymbol_bound b)
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.FourierEnergy.CM.Construction.sobolevEnergySymbol_partition b) f h
  rw [Fintype.sum_option] at henergy
  rw [PiLp.inner_apply]
  exact henergy.symm

end

end OAI.Analysis.HodgeTheory.Decomposition.VectorSobolevEnergy.Constructions
