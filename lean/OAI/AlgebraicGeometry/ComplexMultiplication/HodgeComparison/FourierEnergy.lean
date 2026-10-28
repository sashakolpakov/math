import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDifferential
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Fourier Energy -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.FourierEnergy.CM.Construction

noncomputable section

/-! The Fourier energy identity for the actual Sobolev embedding and weak derivatives. -/

open _root_.MeasureTheory FourierTransform
open scoped SchwartzMap ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A pointwise square partition of Fourier symbols preserves the Hilbert inner product. -/
theorem l2FourierPartition_inner {ι : Type*} [Fintype ι]
    (g : ι → E → ℂ) (hg : ∀ i, (g i).HasTemperateGrowth)
    (C : ι → ℝ) (hC : ∀ i x, ‖g i x‖ ≤ C i)
    (hpartition : ∀ x, ∑ i, star (g i x) * g i x = 1)
    (f h : Lp ℂ 2 (volume : Measure E)) :
    ∑ i, inner ℂ (SobolevIs.CM.Construction.l2FourierMultiplier (hg i) (hC i) f)
      (SobolevIs.CM.Construction.l2FourierMultiplier (hg i) (hC i) h) = inner ℂ f h := by
  let T := fun i => SobolevIs.CM.Construction.l2FourierMultiplier (hg i) (hC i) (F := ℂ)
  have hfae : ∀ᵐ x ∂(volume : Measure E), ∀ i,
      (𝓕 (T i f) : Lp ℂ 2 (volume : Measure E)) x = g i x • (𝓕 f) x :=
    ae_all_iff.mpr (fun i => LpLocalization.CM.Construction.fourierMultiplier_l2_fourier_coeFn (hg i) (hC i) f (T i f)
      (SobolevIs.CM.Construction.l2FourierMultiplier_distribution (hg i) (hC i) f))
  have hhae : ∀ᵐ x ∂(volume : Measure E), ∀ i,
      (𝓕 (T i h) : Lp ℂ 2 (volume : Measure E)) x = g i x • (𝓕 h) x :=
    ae_all_iff.mpr (fun i => LpLocalization.CM.Construction.fourierMultiplier_l2_fourier_coeFn (hg i) (hC i) h (T i h)
      (SobolevIs.CM.Construction.l2FourierMultiplier_distribution (hg i) (hC i) h))
  calc
    _ = ∑ i, ∫ x, inner ℂ ((𝓕 (T i f) : Lp ℂ 2 (volume : Measure E)) x)
        ((𝓕 (T i h) : Lp ℂ 2 (volume : Measure E)) x) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Lp.inner_fourier_eq, L2.inner_def]
    _ = ∫ x, ∑ i, inner ℂ ((𝓕 (T i f) : Lp ℂ 2 (volume : Measure E)) x)
        ((𝓕 (T i h) : Lp ℂ 2 (volume : Measure E)) x) :=
      (integral_finsetSum Finset.univ (fun i _ => L2.integrable_inner (𝕜 := ℂ) (𝓕 (T i f))
        (𝓕 (T i h)))).symm
    _ = ∫ x, inner ℂ ((𝓕 f : Lp ℂ 2 (volume : Measure E)) x)
        ((𝓕 h : Lp ℂ 2 (volume : Measure E)) x) := by
      apply integral_congr_ae
      filter_upwards [hfae, hhae] with x hx hy
      simp only [hx, hy, inner_smul_left, inner_smul_right]
      calc
        _ = (∑ i, star (g i x) * g i x) *
            inner ℂ ((𝓕 f : Lp ℂ 2 (volume : Measure E)) x)
              ((𝓕 h : Lp ℂ 2 (volume : Measure E)) x) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          change g i x * (star (g i x) * _) = _
          ring
        _ = _ := by rw [hpartition, one_mul]
    _ = inner ℂ f h := by rw [← L2.inner_def, Lp.inner_fourier_eq]

/-- The scalar Bessel coordinate and the normalized directional derivative coordinates. -/
def sobolevEnergySymbol {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) :
    Option ι → E → ℂ
  | none, x => (((1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ) : ℝ) : ℂ)
  | some i, x => Complex.ofReal (inner ℝ x (b i) * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem sobolevEnergySymbol_temperate {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (i : Option ι) : (sobolevEnergySymbol b i).HasTemperateGrowth := by
  cases i with
  | none =>
    change (fun x : E => (((1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ) : ℝ) : ℂ)).HasTemperateGrowth
    fun_prop
  | some i =>
    change (fun x : E => Complex.ofReal
      (inner ℝ x (b i) * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ))).HasTemperateGrowth
    fun_prop

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem sobolevEnergySymbol_bound {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (i : Option ι) (x : E) : ‖sobolevEnergySymbol b i x‖ ≤ 1 := by
  cases i with
  | none => exact SobolevIs.CM.Construction.negative_besselSymbol_bound (by norm_num : (0 : ℝ) ≤ 1) x
  | some i => simpa only [sobolevEnergySymbol, b.norm_eq_one] using Bounds.CM.Construction.normalizedDerivativeSymbol_bound (b i) x

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem sobolevEnergySymbol_partition {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (x : E) : ∑ i, star (sobolevEnergySymbol b i x) * sobolevEnergySymbol b i x = 1 := by
  let q : ℝ := (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ)
  have hq : q ^ 2 = (1 + ‖x‖ ^ 2)⁻¹ := by
    dsimp [q]
    rw [← Real.rpow_two, ← Real.rpow_mul (by positivity)]
    norm_num
    exact Real.rpow_neg_one _
  have hreal : q ^ 2 + ∑ i, (inner ℝ x (b i) * q) ^ 2 = 1 := by
    simp_rw [mul_pow]
    rw [← Finset.sum_mul, b.sum_sq_inner_left, hq]
    field_simp
  rw [Fintype.sum_option]
  change star (q : ℂ) * (q : ℂ) +
    ∑ i, star (Complex.ofReal (inner ℝ x (b i) * q)) *
      Complex.ofReal (inner ℝ x (b i) * q) = 1
  simpa only [Complex.star_def, Complex.conj_ofReal, ← pow_two,
    ← Complex.ofReal_pow, ← Complex.ofReal_sum, ← Complex.ofReal_add,
    ← Complex.ofReal_one] using congrArg Complex.ofReal hreal

/-- The normalized gradient, with its actual directional components in a Hilbert direct sum. -/
def sobolevNormalizedGradient {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) :
    Lp ℂ 2 (volume : Measure E) →L[ℂ] PiLp 2 (fun _ : ι => Lp ℂ 2 (volume : Measure E)) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => Lp ℂ 2 (volume : Measure E))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => SobolevIs.CM.Construction.l2FourierMultiplier
      (sobolevEnergySymbol_temperate b (some i)) (sobolevEnergySymbol_bound b (some i))))

theorem sobolevNormalizedGradient_apply {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (f : Lp ℂ 2 (volume : Measure E)) (i : ι) :
    sobolevNormalizedGradient b f i = SobolevIs.CM.Construction.l2FourierMultiplier
      (sobolevEnergySymbol_temperate b (some i)) (sobolevEnergySymbol_bound b (some i)) f := rfl

/-- Each normalized gradient component is exactly the native weak derivative divided by 2πi. -/
theorem sobolevNormalizedGradient_derivative {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (f : Lp ℂ 2 (volume : Measure E)) (i : ι) :
    SobolevDifferential.CM.Construction.sobolevL2Derivative (b i) f = (2 * Real.pi * Complex.I : ℂ) • sobolevNormalizedGradient b f i := by
  rw [sobolevNormalizedGradient_apply]
  change (2 * Real.pi * Complex.I : ℂ) •
    SobolevIs.CM.Construction.l2FourierMultiplier (g := fun x : E =>
      Complex.ofReal (inner ℝ x (b i) * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ)))
      (by fun_prop) (Bounds.CM.Construction.normalizedDerivativeSymbol_bound (b i)) f = _
  apply congrArg (fun v : Lp ℂ 2 (volume : Measure E) => (2 * Real.pi * Complex.I : ℂ) • v)
  apply (LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
    (F := ℂ) (μ := (volume : Measure E)) (p := 2)))
  change (SobolevIs.CM.Construction.l2FourierMultiplier (g := fun x : E =>
      Complex.ofReal (inner ℝ x (b i) * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ)))
      (by fun_prop) (Bounds.CM.Construction.normalizedDerivativeSymbol_bound (b i)) f : TemperedDistribution E ℂ) =
    (SobolevIs.CM.Construction.l2FourierMultiplier (sobolevEnergySymbol_temperate b (some i))
      (sobolevEnergySymbol_bound b (some i)) f : TemperedDistribution E ℂ)
  rw [SobolevIs.CM.Construction.l2FourierMultiplier_distribution, SobolevIs.CM.Construction.l2FourierMultiplier_distribution]
  rfl

theorem sobolev_derivative_energy {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (f h : Lp ℂ 2 (volume : Measure E)) :
    ∑ i, inner ℂ (SobolevDifferential.CM.Construction.sobolevL2Derivative (b i) f) (SobolevDifferential.CM.Construction.sobolevL2Derivative (b i) h) =
      (((2 * Real.pi) ^ 2 : ℝ) : ℂ) *
        inner ℂ (sobolevNormalizedGradient b f) (sobolevNormalizedGradient b h) := by
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
  rw [sobolevNormalizedGradient_derivative, sobolevNormalizedGradient_derivative,
    inner_smul_left, inner_smul_right]
  change star c * (c * _) = _
  rw [← mul_assoc, mul_comm (star c) c, hc]

/-- The usual H¹ graph inner product agrees exactly with the Bessel-coordinate Hilbert product. -/
theorem sobolev_graph_inner {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (f h : Lp ℂ 2 (volume : Measure E)) :
    inner ℂ f h = inner ℂ (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) f)
      (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) h) +
      inner ℂ (sobolevNormalizedGradient b f) (sobolevNormalizedGradient b h) := by
  have henergy := l2FourierPartition_inner (sobolevEnergySymbol b)
    (sobolevEnergySymbol_temperate b) (fun _ => 1) (sobolevEnergySymbol_bound b)
    (sobolevEnergySymbol_partition b) f h
  rw [Fintype.sum_option] at henergy
  rw [PiLp.inner_apply]
  exact henergy.symm

/-- No nonzero Euclidean L² function has all its first derivatives zero. -/
theorem sobolevNormalizedGradient_injective [Nontrivial E] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) : Function.Injective (sobolevNormalizedGradient b) := by
  have hzero : ∀ f : Lp ℂ 2 (volume : Measure E), sobolevNormalizedGradient b f = 0 → f = 0 := by
    intro f hf
    have hzF : (𝓕 (0 : Lp ℂ 2 (volume : Measure E)) : Lp ℂ 2 (volume : Measure E)) = 0 :=
      (Lp.fourierTransformₗᵢ E ℂ).map_zero
    have hcomponent (i : ι) : SobolevIs.CM.Construction.l2FourierMultiplier (sobolevEnergySymbol_temperate b (some i))
        (sobolevEnergySymbol_bound b (some i)) f = 0 := by
      change sobolevNormalizedGradient b f i = 0
      rw [hf]
      rfl
    have hcoefs : ∀ᵐ x ∂(volume : Measure E), ∀ i : ι,
        sobolevEnergySymbol b (some i) x * (𝓕 f : Lp ℂ 2 (volume : Measure E)) x = 0 := by
      apply ae_all_iff.mpr
      intro i
      have h := LpLocalization.CM.Construction.fourierMultiplier_l2_fourier_coeFn
        (sobolevEnergySymbol_temperate b (some i)) (sobolevEnergySymbol_bound b (some i)) f
        (SobolevIs.CM.Construction.l2FourierMultiplier (sobolevEnergySymbol_temperate b (some i))
          (sobolevEnergySymbol_bound b (some i)) f)
        (SobolevIs.CM.Construction.l2FourierMultiplier_distribution _ _ f)
      rw [hcomponent i, hzF] at h
      filter_upwards [h, Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure E))] with x hx hz
      rw [hz] at hx
      exact hx.symm
    have hfour : (𝓕 f : Lp ℂ 2 (volume : Measure E)) = 0 := by
      apply Lp.ext
      filter_upwards [hcoefs, (Set.countable_singleton (0 : E)).ae_notMem (volume : Measure E),
        Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure E))] with x hx hx0 hz
      rw [hz]
      have hex : ∃ i : ι, inner ℝ x (b i) ≠ 0 := by
        by_contra! hn
        have heq := b.sum_sq_inner_left x
        simp only [hn, zero_pow (by norm_num : 2 ≠ 0), Finset.sum_const_zero] at heq
        have hxzero : x = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp heq.symm)
        exact hx0 (by simpa only [Set.mem_singleton_iff] using hxzero)
      obtain ⟨i, hi⟩ := hex
      have hsymbol : sobolevEnergySymbol b (some i) x ≠ 0 := by
        change Complex.ofReal (inner ℝ x (b i) * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ)) ≠ 0
        exact_mod_cast mul_ne_zero hi (Real.rpow_pos_of_pos (by positivity) _).ne'
      exact (mul_eq_zero.mp (hx i)).resolve_left hsymbol
    apply (Lp.fourierTransformₗᵢ E ℂ).injective
    change (𝓕 f : Lp ℂ 2 (volume : Measure E)) = 𝓕 (0 : Lp ℂ 2 (volume : Measure E))
    rw [hzF]
    exact hfour
  intro f h heq
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub, heq, sub_self]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.FourierEnergy.CM.Construction
