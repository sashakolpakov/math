import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EllipticLocal

/-! # Bounds -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Bounds.CM.Construction

noncomputable section

section

/-! Faithful L² coordinates for the genuine Sobolev spaces used in HodgeComparison's analytic step. -/

open TemperedDistribution _root_.MeasureTheory ENNReal
open scoped SchwartzMap Laplacian

variable (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Sobolev regularity as a subspace of actual tempered distributions. -/
def sobolevDistributionSubmodule (s : ℝ) : Submodule ℂ 𝓢'(E, F) where
  carrier := {u | MemSobolev s 2 u}
  zero_mem' := memSobolev_fun_zero E F s 2
  add_mem' hu hv := hu.add hv
  smul_mem' c _ hu := hu.smul c

/-- Inverse Bessel potential sends an L² function to an actual Sobolev distribution. -/
def sobolevCoordinateMap (s : ℝ) :
    Lp F 2 (volume : Measure E) →ₗ[ℂ] sobolevDistributionSubmodule E F s :=
  (((besselPotential E F (-s)).toLinearMap).comp
    (Lp.toTemperedDistributionCLM F (volume : Measure E) 2).toLinearMap).codRestrict _ (by
      intro f
      change MemSobolev s 2 (besselPotential E F (-s) (f : 𝓢'(E, F)))
      rw [memSobolev_besselPotential_iff, neg_add_cancel, memSobolev_zero_iff]
      exact ⟨f, rfl⟩)

theorem sobolevCoordinateMap_apply (s : ℝ) (f : Lp F 2 (volume : Measure E)) :
    (sobolevCoordinateMap E F s f).val = besselPotential E F (-s) (f : 𝓢'(E, F)) := rfl

/-- No two distinct L² functions describe the same Sobolev distribution. -/
theorem sobolevCoordinateMap_injective (s : ℝ) :
    Function.Injective (sobolevCoordinateMap E F s) := by
  intro f g h
  have hd := congrArg (fun u : sobolevDistributionSubmodule E F s =>
    besselPotential E F s u.val) h
  simp only [sobolevCoordinateMap_apply, besselPotential_besselPotential_apply,
    neg_add_cancel, besselPotential_zero, ContinuousLinearMap.id_apply] at hd
  exact (LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
    (F := F) (μ := (volume : Measure E)) (p := 2))) hd

/-- Every Sobolev distribution has an L² coordinate, by the genuine defining regularity. -/
theorem sobolevCoordinateMap_surjective (s : ℝ) :
    Function.Surjective (sobolevCoordinateMap E F s) := by
  intro u
  obtain ⟨f, hf⟩ := u.property
  refine ⟨f, Subtype.ext ?_⟩
  rw [sobolevCoordinateMap_apply, ← hf, besselPotential_besselPotential_apply,
    add_neg_cancel, besselPotential_zero, ContinuousLinearMap.id_apply]

/-- The actual Sobolev subspace is canonically identified with L² by the Bessel operator. -/
def sobolevCoordinateEquiv (s : ℝ) :
    Lp F 2 (volume : Measure E) ≃ₗ[ℂ] sobolevDistributionSubmodule E F s :=
  LinearEquiv.ofBijective (sobolevCoordinateMap E F s)
    ⟨sobolevCoordinateMap_injective E F s, sobolevCoordinateMap_surjective E F s⟩

/-- Applying the order-s Bessel operator recovers the actual L² representative. -/
theorem sobolevCoordinateEquiv_symm_distribution (s : ℝ)
    (u : sobolevDistributionSubmodule E F s) :
    ((sobolevCoordinateEquiv E F s).symm u : 𝓢'(E, F)) = besselPotential E F s u.val := by
  obtain ⟨f, rfl⟩ := (sobolevCoordinateEquiv E F s).surjective u
  simp only [LinearEquiv.symm_apply_apply]
  change (f : 𝓢'(E, F)) = besselPotential E F s (besselPotential E F (-s) (f : 𝓢'(E, F)))
  simp

/-- The Sobolev norm is the L² norm of the genuine Bessel representative. -/
def sobolevNorm (s : ℝ) (u : sobolevDistributionSubmodule E F s) : ℝ :=
  ‖(sobolevCoordinateEquiv E F s).symm u‖

theorem sobolevNorm_eq_zero_iff (s : ℝ) (u : sobolevDistributionSubmodule E F s) :
    sobolevNorm E F s u = 0 ↔ u = 0 := by
  rw [sobolevNorm, norm_eq_zero, LinearEquiv.map_eq_zero_iff]

theorem sobolevNorm_add_le (s : ℝ) (u v : sobolevDistributionSubmodule E F s) :
    sobolevNorm E F s (u + v) ≤ sobolevNorm E F s u + sobolevNorm E F s v := by
  unfold sobolevNorm
  rw [map_add]
  exact norm_add_le _ _

theorem sobolevNorm_sub_le (s : ℝ) (u v : sobolevDistributionSubmodule E F s) :
    sobolevNorm E F s (u - v) ≤ sobolevNorm E F s u + sobolevNorm E F s v := by
  unfold sobolevNorm
  rw [map_sub]
  exact norm_sub_le _ _

theorem sobolevNorm_smul (s : ℝ) (c : ℂ) (u : sobolevDistributionSubmodule E F s) :
    sobolevNorm E F s (c • u) = ‖c‖ * sobolevNorm E F s u := by
  unfold sobolevNorm
  rw [map_smul, norm_smul]

/-- Bessel potential changes Sobolev order without changing the L² coordinate. -/
def sobolevBesselEquiv (s t : ℝ) :
    sobolevDistributionSubmodule E F s ≃ₗ[ℂ] sobolevDistributionSubmodule E F t :=
  (sobolevCoordinateEquiv E F s).symm.trans (sobolevCoordinateEquiv E F t)

/-- The order-changing equivalence is the genuine Fourier multiplier of order s-t. -/
theorem sobolevBesselEquiv_distribution (s t : ℝ)
    (u : sobolevDistributionSubmodule E F s) :
    (sobolevBesselEquiv E F s t u).val = besselPotential E F (s - t) u.val := by
  obtain ⟨f, rfl⟩ := (sobolevCoordinateEquiv E F s).surjective u
  simp only [sobolevBesselEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  change besselPotential E F (-t) (f : 𝓢'(E, F)) =
    besselPotential E F (s - t) (besselPotential E F (-s) (f : 𝓢'(E, F)))
  rw [besselPotential_besselPotential_apply, show -s + (s - t) = -t by ring]

/-- The Bessel coordinate equivalence preserves the stated Sobolev norms. -/
theorem sobolevBesselEquiv_norm (s t : ℝ) (u : sobolevDistributionSubmodule E F s) :
    sobolevNorm E F t (sobolevBesselEquiv E F s t u) = sobolevNorm E F s u := by
  simp only [sobolevNorm, sobolevBesselEquiv, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]

/-- The basic Euclidean elliptic estimate, with the Fourier normalization explicit. -/
theorem laplacian_sobolev_estimate {s : ℝ} {u : 𝓢'(E, F)}
    (hu : MemSobolev s 2 u) (hΔ : MemSobolev s 2 (Δ u)) :
    sobolevNorm E F (s + 2) ⟨u, EllipticLocal.CM.Construction.laplacian_sobolev_regularity hu hΔ⟩ ≤
      sobolevNorm E F s ⟨u, hu⟩ +
        ‖((((2 * Real.pi) ^ 2)⁻¹ : ℝ) : ℂ)‖ * sobolevNorm E F s ⟨Δ u, hΔ⟩ := by
  let higher : sobolevDistributionSubmodule E F (s + 2) :=
    ⟨u, EllipticLocal.CM.Construction.laplacian_sobolev_regularity hu hΔ⟩
  let lower : sobolevDistributionSubmodule E F s := ⟨u, hu⟩
  let derivative : sobolevDistributionSubmodule E F s := ⟨Δ u, hΔ⟩
  let c : ℂ := (((2 * Real.pi) ^ 2)⁻¹ : ℝ)
  have heq : sobolevBesselEquiv E F (s + 2) s higher = lower - c • derivative := by
    apply Subtype.ext
    rw [sobolevBesselEquiv_distribution, show s + 2 - s = 2 by ring,
      EllipticLocal.CM.Construction.besselPotential_two_eq_shiftedLaplacian]
    change u - (((2 * Real.pi) ^ 2)⁻¹ : ℝ) • Δ u = u - c • Δ u
    rw [Complex.coe_smul]
  have hn := sobolevBesselEquiv_norm E F (s + 2) s higher
  rw [heq] at hn
  change sobolevNorm E F (s + 2) higher ≤ _
  rw [← hn]
  have h := sobolevNorm_sub_le E F s lower (c • derivative)
  rwa [sobolevNorm_smul] at h

end

section

/-! Quantitative Fourier multiplier bounds for the scalar elliptic existence argument. -/

open Filter FourierTransform TemperedDistribution _root_.MeasureTheory ENNReal
open scoped SchwartzMap BoundedContinuousFunction

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- A bounded temperate Fourier symbol acts on L² with its pointwise norm bound. -/
theorem fourierMultiplier_l2_bound {g : E → ℂ}
    (hg : g.HasTemperateGrowth) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C)
    (f : Lp F 2 (volume : Measure E)) :
    ∃ v : Lp F 2 (volume : Measure E),
      (v : 𝓢'(E, F)) = fourierMultiplierCLM F g (f : 𝓢'(E, F)) ∧ ‖v‖ ≤ C * ‖f‖ := by
  let G : E →ᵇ ℂ := BoundedContinuousFunction.ofNormedAddCommGroup g hg.1.continuous C hC
  let m : Lp ℂ ⊤ (volume : Measure E) := G.memLp_top.toLp _
  let product : Lp F 2 (volume : Measure E) := m • 𝓕 f
  refine ⟨𝓕⁻ product, ?_, ?_⟩
  · rw [← Lp.fourierInv_toTemperedDistribution_eq, fourierMultiplierCLM_apply,
      Lp.fourier_toTemperedDistribution_eq]
    congr 1
    exact Lp.toTemperedDistribution_smul_eq hg G.memLp_top (𝓕 f)
  · have hprod : ‖product‖ ≤ C * ‖𝓕 f‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) m (𝓕 f),
        G.memLp_top.coeFn_toLp] with x hx hm
      rw [hx]
      change ‖m x • (𝓕 f) x‖ ≤ _
      rw [norm_smul]
      rw [hm]
      exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)
    change ‖(Lp.fourierTransformₗᵢ E F).symm product‖ ≤ C * ‖f‖
    rw [(Lp.fourierTransformₗᵢ E F).symm.norm_map]
    simpa only [Lp.norm_fourier_eq] using hprod

omit [CompleteSpace F] in
/-- Bessel regularity operators commute with scalar Fourier multipliers. -/
theorem besselPotential_fourierMultiplier_comm (s : ℝ) {g : E → ℂ}
    (hg : g.HasTemperateGrowth) (u : 𝓢'(E, F)) :
    besselPotential E F s (fourierMultiplierCLM F g u) =
      fourierMultiplierCLM F g (besselPotential E F s u) := by
  unfold besselPotential
  rw [fourierMultiplierCLM_fourierMultiplierCLM_apply hg (by fun_prop),
    fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) hg]
  congr 2
  exact mul_comm _ _

/-- The same bound holds in every Sobolev order, using the actual Bessel norm. -/
theorem fourierMultiplier_sobolev_bound (s : ℝ) {g : E → ℂ}
    (hg : g.HasTemperateGrowth) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C)
    (u : sobolevDistributionSubmodule E F s) :
    sobolevNorm E F s
      ⟨fourierMultiplierCLM F g u.val,
        u.property.fourierMultiplierCLM_of_bounded hg ⟨C, hC⟩⟩ ≤
      C * sobolevNorm E F s u := by
  let f := (sobolevCoordinateEquiv E F s).symm u
  let v : sobolevDistributionSubmodule E F s :=
    ⟨fourierMultiplierCLM F g u.val,
      u.property.fourierMultiplierCLM_of_bounded hg ⟨C, hC⟩⟩
  obtain ⟨w, hw, hwn⟩ := fourierMultiplier_l2_bound hg hC f
  have heq : (sobolevCoordinateEquiv E F s).symm v = w := by
    apply (LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
      (F := F) (μ := (volume : Measure E)) (p := 2)))
    change ((sobolevCoordinateEquiv E F s).symm v : 𝓢'(E, F)) = (w : 𝓢'(E, F))
    rw [sobolevCoordinateEquiv_symm_distribution, hw]
    change besselPotential E F s (fourierMultiplierCLM F g u.val) =
      fourierMultiplierCLM F g (f : 𝓢'(E, F))
    rw [besselPotential_fourierMultiplier_comm s hg,
      ← sobolevCoordinateEquiv_symm_distribution]
  change sobolevNorm E F s v ≤ C * sobolevNorm E F s u
  unfold sobolevNorm
  rw [heq]
  exact hwn

/-- Decreasing Sobolev order is the actual identity map on distributions. -/
def sobolevInclusion {s t : ℝ} (hts : t ≤ s) :
    sobolevDistributionSubmodule E F s →ₗ[ℂ] sobolevDistributionSubmodule E F t :=
  Submodule.inclusion (fun _ hu => hu.mono hts)

/-- The usual monotonicity of the Bessel Sobolev norms holds with constant one. -/
theorem sobolevInclusion_norm_le {s t : ℝ} (hts : t ≤ s)
    (u : sobolevDistributionSubmodule E F s) :
    sobolevNorm E F t (sobolevInclusion hts u) ≤ sobolevNorm E F s u := by
  let g : E → ℂ := fun x => (((1 + ‖x‖ ^ 2) ^ ((t - s) / 2) : ℝ) : ℂ)
  have hg : g.HasTemperateGrowth := by dsimp [g]; fun_prop
  have hgb : ∀ x, ‖g x‖ ≤ 1 := by
    intro x
    change ‖(((1 + ‖x‖ ^ 2) ^ ((t - s) / 2) : ℝ) : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by simp)
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hts) (by norm_num)
  let v : sobolevDistributionSubmodule E F s :=
    ⟨fourierMultiplierCLM F g u.val,
      u.property.fourierMultiplierCLM_of_bounded hg ⟨1, hgb⟩⟩
  have heq : sobolevBesselEquiv E F t s (sobolevInclusion hts u) = v := by
    apply Subtype.ext
    rw [sobolevBesselEquiv_distribution]
    rfl
  have hn := sobolevBesselEquiv_norm E F t s (sobolevInclusion hts u)
  rw [heq] at hn
  rw [← hn]
  simpa only [one_mul] using fourierMultiplier_sobolev_bound s hg hgb u

end

/-! Directional derivative estimates in the actual Sobolev norm. -/

open TemperedDistribution _root_.MeasureTheory ENNReal
open scoped SchwartzMap LineDeriv

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The normalized symbol of a first derivative is bounded by the direction's norm. -/
theorem normalizedDerivativeSymbol_bound (m x : E) :
    ‖(Complex.ofReal (inner ℝ x m * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ)))‖ ≤ ‖m‖ := by
  apply le_of_sq_le_sq _ (norm_nonneg _)
  simp only [Complex.ofReal_mul, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  have h₁ : |(1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ)| ^ 2 = (1 + ‖x‖ ^ 2)⁻¹ := by
    field_simp
    norm_cast
    rw [Real.rpow_neg (by positivity), sq_abs, inv_pow]
    field_simp
    calc
      _ = ((1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
        rw [← Real.rpow_mul (by positivity)]
        simp
      _ = _ := by simp
  have h₂ : |inner ℝ x m| ^ 2 ≤ ‖m‖ ^ 2 * (1 + ‖x‖ ^ 2) := by
    grw [abs_real_inner_le_norm]
    rw [mul_pow, mul_comm]
    gcongr
    simp
  grw [h₁, h₂]
  apply le_of_eq
  field_simp

/-- A directional derivative loses one Sobolev order with its explicit norm bound. -/
theorem lineDeriv_sobolev_estimate (s : ℝ) (m : E)
    (u : sobolevDistributionSubmodule E F s) :
    sobolevNorm E F (s - 1) ⟨∂_{m} u.val, u.property.lineDerivOp⟩ ≤
      (2 * Real.pi * ‖m‖) * sobolevNorm E F s u := by
  let g : E → ℂ := fun x =>
    Complex.ofReal (inner ℝ x m * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ))
  have hg : g.HasTemperateGrowth := by dsimp [g]; fun_prop
  have hgb : ∀ x, ‖g x‖ ≤ ‖m‖ := normalizedDerivativeSymbol_bound m
  let v : sobolevDistributionSubmodule E F s :=
    ⟨fourierMultiplierCLM F g u.val, u.property.fourierMultiplierCLM_of_bounded hg ⟨‖m‖, hgb⟩⟩
  let du : sobolevDistributionSubmodule E F (s - 1) := ⟨∂_{m} u.val, u.property.lineDerivOp⟩
  have heq : sobolevBesselEquiv E F (s - 1) s du = (2 * Real.pi * Complex.I : ℂ) • v := by
    apply Subtype.ext
    rw [sobolevBesselEquiv_distribution, show s - 1 - s = -1 by ring]
    exact besselPotential_neg_one_lineDerivOp_eq u.val
  have hc : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
    simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hv : sobolevNorm E F s v ≤ ‖m‖ * sobolevNorm E F s u :=
    fourierMultiplier_sobolev_bound s hg hgb u
  calc
    sobolevNorm E F (s - 1) du =
        sobolevNorm E F s (sobolevBesselEquiv E F (s - 1) s du) :=
      (sobolevBesselEquiv_norm E F (s - 1) s du).symm
    _ = (2 * Real.pi) * sobolevNorm E F s v := by rw [heq, sobolevNorm_smul, hc]
    _ ≤ (2 * Real.pi) * (‖m‖ * sobolevNorm E F s u) :=
      mul_le_mul_of_nonneg_left hv (by positivity)
    _ = (2 * Real.pi * ‖m‖) * sobolevNorm E F s u := by ring

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Bounds.CM.Construction
