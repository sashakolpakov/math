import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceQuotients
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevInv

/-! # Difference Criterion -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceCriterion.CM.Construction

noncomputable section

/-! Bounded actual difference quotients produce genuine L2 weak derivatives. -/

open _root_.MeasureTheory FourierTransform TemperedDistribution Filter
open scoped SchwartzMap LineDeriv _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def fourierDerivativeSymbol (m x : E) : ℂ :=
  (((2 * Real.pi * inner ℝ m x : ℝ) : ℂ) * Complex.I)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem fourierDerivativeSymbol_temperate (m : E) : (fourierDerivativeSymbol m).HasTemperateGrowth := by
  unfold fourierDerivativeSymbol
  fun_prop

/-- Fatou's lemma turns an eventual norm bound on the spatial difference
quotients into square integrability of the actual Fourier derivative symbol. -/
theorem fourierDerivative_memLp_of_difference_bound (m : E) (u : Lp ℂ 2 (volume : Measure E))
    {C : ℝ} (hC : ∀ᶠ t : ℝ in 𝓝[≠] 0, ‖DifferenceQuotients.CM.Construction.l2DifferenceQuotient m t u‖ ≤ C) :
    MemLp (fun x => fourierDerivativeSymbol m x * (𝓕 u : Lp ℂ 2 volume) x) 2 (volume : Measure E) := by
  let f : ℝ → E → ℂ := fun t x => DifferenceQuotients.CM.Construction.differenceQuotientSymbol t (inner ℝ m x) * (𝓕 u : Lp ℂ 2 volume) x
  let g : E → ℂ := fun x => fourierDerivativeSymbol m x * (𝓕 u : Lp ℂ 2 volume) x
  have hf (t : ℝ) : AEStronglyMeasurable (f t) (volume : Measure E) :=
    (Lp.aestronglyMeasurable (𝓕 (DifferenceQuotients.CM.Construction.l2DifferenceQuotient m t u) : Lp ℂ 2 volume)).congr
      (DifferenceQuotients.CM.Construction.fourier_l2DifferenceQuotient_coe m t u)
  have hlim : ∀ᵐ x ∂(volume : Measure E), Tendsto (fun t : ℝ => f t x) (𝓝[≠] 0) (𝓝 (g x)) :=
    Filter.Eventually.of_forall (fun x => (DifferenceQuotients.CM.Construction.differenceQuotientSymbol_tendsto (inner ℝ m x)).mul_const _)
  have hbound : ∀ᶠ t : ℝ in 𝓝[≠] 0, eLpNorm (f t) 2 (volume : Measure E) ≤ ENNReal.ofReal C := by
    filter_upwards [hC] with t ht
    calc
      _ = eLpNorm (𝓕 (DifferenceQuotients.CM.Construction.l2DifferenceQuotient m t u) : Lp ℂ 2 volume) 2 volume :=
        (eLpNorm_congr_ae (DifferenceQuotients.CM.Construction.fourier_l2DifferenceQuotient_coe m t u)).symm
      _ = ENNReal.ofReal ‖DifferenceQuotients.CM.Construction.l2DifferenceQuotient m t u‖ := by
        rw [← Lp.enorm_def, ← ofReal_norm, Lp.norm_fourier_eq]
      _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal ht
  exact (Lp.eLpNorm_le_of_ae_tendsto hbound hf
    (aestronglyMeasurable_of_tendsto_ae (𝓝[≠] (0 : ℝ)) hf hlim) hlim).trans_lt ENNReal.ofReal_lt_top

/-- Multiplication by a temperate coefficient agrees with distributional
multiplication whenever its actual product is in L2. -/
theorem l2_product_distribution {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (u : Lp ℂ 2 (volume : Measure E))
    (hprod : MemLp (fun x => g x * u x) 2 (volume : Measure E)) :
    ((hprod.toLp (fun x => g x * u x) : Lp ℂ 2 volume) : 𝓢'(E, ℂ)) =
      smulLeftCLM ℂ g (u : 𝓢'(E, ℂ)) := by
  ext φ
  simp only [Lp.toTemperedDistribution_apply, smulLeftCLM_apply_apply]
  apply integral_congr_ae
  filter_upwards [hprod.coeFn_toLp] with x hx
  simp only [hx, SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul]
  ring

/-- The limit is the derivative of the given L2 function as a tempered
distribution, rather than an independently chosen formal derivative. -/
theorem l2_weakDerivative_of_difference_bound (m : E) (u : Lp ℂ 2 (volume : Measure E))
    {C : ℝ} (hC : ∀ᶠ t : ℝ in 𝓝[≠] 0, ‖DifferenceQuotients.CM.Construction.l2DifferenceQuotient m t u‖ ≤ C) :
    ∃ v : Lp ℂ 2 (volume : Measure E), (v : 𝓢'(E, ℂ)) = ∂_{m} (u : 𝓢'(E, ℂ)) := by
  let g := fourierDerivativeSymbol m
  have hg : g.HasTemperateGrowth := fourierDerivativeSymbol_temperate m
  have hprod := fourierDerivative_memLp_of_difference_bound m u hC
  let w : Lp ℂ 2 (volume : Measure E) := hprod.toLp _
  refine ⟨𝓕⁻ w, ?_⟩
  rw [← Lp.fourierInv_toTemperedDistribution_eq]
  have hw : (w : 𝓢'(E, ℂ)) = smulLeftCLM ℂ g (𝓕 (u : 𝓢'(E, ℂ))) := by
    rw [Lp.fourier_toTemperedDistribution_eq]
    exact l2_product_distribution hg (𝓕 u) hprod
  rw [hw, TemperedDistribution.lineDeriv_eq_fourierMultiplierCLM, fourierMultiplierCLM_apply]
  have hg0 : (fun x : E => ((inner ℝ x m : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
  have hgeq : g = (2 * Real.pi * Complex.I : ℂ) • (fun x : E => ((inner ℝ x m : ℝ) : ℂ)) := by
    funext x
    simp only [g, fourierDerivativeSymbol, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul,
      Complex.ofReal_ofNat, real_inner_comm m x]
    ring
  rw [hgeq, smulLeftCLM_smul hg0, smul_apply, FourierTransform.fourierInv_smul]

/-- Uniform bounds for all coordinate difference quotients characterize
membership in the actual distributional H1 space in the direction needed
for elliptic regularity. -/
theorem memSobolev_one_of_difference_bounds {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (u : Lp ℂ 2 (volume : Measure E))
    (hbound : ∀ i, ∃ C : ℝ, ∀ᶠ t : ℝ in 𝓝[≠] 0, ‖DifferenceQuotients.CM.Construction.l2DifferenceQuotient (b i) t u‖ ≤ C) :
    MemSobolev 1 2 (u : 𝓢'(E, ℂ)) := by
  have hzero : MemSobolev 0 2 (u : 𝓢'(E, ℂ)) := memSobolev_zero_iff.mpr ⟨u, rfl⟩
  have hd : ∀ i, MemSobolev 0 2 (∂_{b i} (u : 𝓢'(E, ℂ))) := by
    intro i
    obtain ⟨C, hC⟩ := hbound i
    obtain ⟨v, hv⟩ := l2_weakDerivative_of_difference_bound (b i) u hC
    exact memSobolev_zero_iff.mpr ⟨v, hv.symm⟩
  simpa only [zero_add] using (SobolevInv.CM.Construction.memSobolev_succ_iff_derivatives b 0 (u : 𝓢'(E, ℂ))).mpr ⟨hzero, hd⟩

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceCriterion.CM.Construction
