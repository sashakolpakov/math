import OAI.Analysis.PDE.Concentration.Kernel

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory FourierTransform
open scoped ContDiff FourierTransform RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem inverseFourier_dilate (b : E → ℂ) {h : ℝ} (hh : 0 < h) (x : E) :
    𝓕⁻ (fun ξ => b (h • ξ)) x =
      (h ^ Module.finrank ℝ E)⁻¹ • 𝓕⁻ b (h⁻¹ • x) := by
  have hc := Measure.integral_comp_smul_of_nonneg (volume : Measure E)
    (fun ξ => Real.fourierChar (inner ℝ ξ (h⁻¹ • x)) • b ξ) h (hR := hh.le)
  have hi (ξ : E) : inner ℝ (h • ξ) (h⁻¹ • x) = inner ℝ ξ x := by
    rw [real_inner_smul_left, inner_smul_right, ← mul_assoc, mul_inv_cancel₀ hh.ne', one_mul]
  simpa only [Real.fourierInv_eq, hi] using hc

theorem scaledInverseKernel_schwartz {b : E → ℂ} (hb : ContDiff ℝ ∞ b)
    (hc : HasCompactSupport b) {h : ℝ} (hh : 0 < h) :
    ∃ K : SchwartzMap E ℂ, (K : E → ℂ) = scaledInverseKernel b h ∧
      ∀ ξ, 𝓕 (scaledInverseKernel b h) ξ = b (h • ξ) := by
  let f : SchwartzMap E ℂ := (hc.comp_smul hh.ne').toSchwartzMap
    (hb.comp (contDiff_const.smul contDiff_id))
  have hi : ((𝓕⁻ f : SchwartzMap E ℂ) : E → ℂ) = scaledInverseKernel b h := by
    rw [SchwartzMap.fourierInv_coe]
    funext x
    exact inverseFourier_dilate b hh x
  refine ⟨𝓕⁻ f, hi, ?_⟩
  intro ξ
  have he := SchwartzMap.fourier_coe (𝓕⁻ f)
  rw [FourierTransform.fourier_fourierInv_eq, hi] at he
  exact (congrFun he ξ).symm

def planeWave (ξ x : E) : ℂ := Complex.exp ((2 * Real.pi * inner ℝ x ξ : ℝ) * Complex.I)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_planeWave (ξ : E) : Continuous (planeWave ξ) := by
  unfold planeWave
  fun_prop

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem norm_planeWave (ξ x : E) : ‖planeWave ξ x‖ = 1 := by
  simp [planeWave, Complex.norm_exp]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem planeWave_sub (ξ x y : E) :
    planeWave ξ (x - y) = planeWave ξ x *
      Complex.exp ((-2 * Real.pi * inner ℝ y ξ : ℝ) * Complex.I) := by
  unfold planeWave
  rw [← Complex.exp_add, inner_sub_left]
  congr 1
  push_cast
  ring

theorem integral_kernel_planeWave (K : E → ℂ) (ξ x : E) :
    (∫ y, K y * planeWave ξ (x - y)) = planeWave ξ x * 𝓕 K ξ := by
  rw [Real.fourier_eq', ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [planeWave_sub]
  simp only [smul_eq_mul]
  ring

def finiteWave {ι : Type*} [Fintype ι] (ξ : ι → E) (a : ι → ℂ) (x : E) : ℂ :=
  ∑ i, a i * planeWave (ξ i) x

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_finiteWave {ι : Type*} [Fintype ι] (ξ : ι → E) (a : ι → ℂ) :
    Continuous (finiteWave ξ a) := by
  exact continuous_finsetSum _ (fun i _ => continuous_const.mul (continuous_planeWave (ξ i)))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem norm_finiteWave_le {ι : Type*} [Fintype ι] (ξ : ι → E) (a : ι → ℂ) (x : E) :
    ‖finiteWave ξ a x‖ ≤ ∑ i, ‖a i‖ := by
  calc
    _ ≤ ∑ i, ‖a i * planeWave (ξ i) x‖ := norm_sum_le _ _
    _ = _ := by simp

theorem integral_kernel_finiteWave {ι : Type*} [Fintype ι]
    {K : E → ℂ} (hK : Integrable K) (ξ : ι → E) (a : ι → ℂ) (x : E) :
    (∫ y, K y * finiteWave ξ a (x - y)) = finiteWave ξ (fun i => 𝓕 K (ξ i) * a i) x := by
  have hi (i : ι) : Integrable (fun y => K y * (a i * planeWave (ξ i) (x - y))) := by
    apply hK.mul_bdd (c := ‖a i‖)
    · exact (continuous_const.mul ((continuous_planeWave (ξ i)).comp
        (continuous_const.sub continuous_id))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun y => by simp
  simp only [finiteWave, Finset.mul_sum]
  rw [MeasureTheory.integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∫ y, K y * (a i * planeWave (ξ i) (x - y))) =
        a i * (∫ y, K y * planeWave (ξ i) (x - y)) := by
      rw [← integral_const_mul]
      congr 1
      funext y
      ring
    _ = _ := by rw [integral_kernel_planeWave]; ring

/-- Convolution against the actual compact-symbol inverse kernel equals the
finite Fourier multiplier, with no integrability assumption on the periodic wave. -/
theorem scaledKernel_finiteWave {ι : Type*} [Fintype ι]
    {b : E → ℂ} (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
    {h : ℝ} (hh : 0 < h) (ξ : ι → E) (a : ι → ℂ) (x : E) :
    (∫ y, scaledInverseKernel b h (x - y) * finiteWave ξ a y) =
      finiteWave ξ (fun i => b (h • ξ i) * a i) x := by
  obtain ⟨K, he, hf⟩ := scaledInverseKernel_schwartz hb hc hh
  have hK : Integrable (scaledInverseKernel b h) := he ▸ K.integrable
  have hid := integral_kernel_finiteWave hK ξ a x
  simp_rw [hf] at hid
  rw [← hid, ← integral_sub_left_eq_self (fun y => scaledInverseKernel b h y * finiteWave ξ a (x - y)) volume x]
  congr 1
  funext y
  simp

end OAI.Analysis.PDE.Concentration
