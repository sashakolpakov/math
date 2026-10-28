import OAI.Analysis.PDE.Concentration.AngularKernel
import OAI.Analysis.PDE.Concentration.FourierMultiplier
import OAI.Analysis.PDE.Concentration.Recovery

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory Set
open scoped ContDiff
open OAI.Analysis.Calculus.Current

theorem finiteMultiplier_sq_bound {d : ℕ} {ι : Type*} [Fintype ι]
    {b : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ} (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
    {r h C : ℝ} (hr : 0 < r) (hh : 0 < h) (hC : 0 ≤ C)
    (hK : ∀ y, ‖scaledInverseKernel b r y‖ ≤ C * OAI.Analysis.Calculus.Current.smoothingKernel d h y)
    (ξ : ι → OAI.Analysis.Calculus.Current.SpatialSpace d) (a : ι → ℂ) (x : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    ‖finiteWave ξ (fun i => b (r • ξ i) * a i) x‖ ^ 2 ≤ C ^ 2 * smoothedSquare h (finiteWave ξ a) x := by
  have hh := convolution_sq_le_smoothedSquare hh (continuous_finiteWave ξ a).measurable
    (norm_finiteWave_le ξ a) hC hK x
  rwa [scaledKernel_finiteWave hb hc hr ξ a x] at hh

def gaussianWaveOutput {d : ℕ} {ι : Type*} [Fintype ι] (j : Fin 2)
    (ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ) (χ : TransverseSpace d → ℂ) (h L : ℝ)
    (W : TransverseSpace d) (ξ : ι → OAI.Analysis.Calculus.Current.SpatialSpace d) (a : ι → ℂ) : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ :=
  finiteWave ξ (fun i => gaussianForwardSymbol j ρ χ h L W ((2 * Real.pi * h) • ξ i) * a i)

/-- The pointwise input-density bound for the actual Gaussian multiplier
acting on a finite periodic wave, rather than an abstract operator. -/
theorem gaussianWaveOutput_sq_bound {d : ℕ} (j : Fin 2) {ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ}
    {χ : TransverseSpace d → ℂ} (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hpos : ∀ η ∈ tsupport ρ, 0 < gaussianFrequencyK η) (w₀ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : TransverseSpace d, ‖W‖ ≤ w₀ →
      ∀ h : ℝ, 0 < h → ∀ L : ℝ, 1 ≤ L → ∀ {ι : Type} [Fintype ι],
      ∀ (ξ : ι → OAI.Analysis.Calculus.Current.SpatialSpace d) (a : ι → ℂ) (x : OAI.Analysis.Calculus.Current.SpatialSpace d),
      ‖gaussianWaveOutput j ρ χ h L W ξ a x‖ ^ 2 ≤
        (C * (h ^ d)⁻¹ * L ^ (((gaussianDerivativeOrder d : ℕ) : ℝ) / 2 - d / 2)) ^ 2 *
          smoothedSquare h (finiteWave ξ a) x := by
  obtain ⟨C, hC, hkernel⟩ := gaussianForwardAngularKernel_bound j hρ hcρ hχ hcχ hpos w₀
  refine ⟨C, hC, ?_⟩
  intro W hW h hh L hL ι _ ξ a x
  have hb : ContDiff ℝ ∞ (gaussianForwardSymbol j ρ χ h L W) := by
    unfold gaussianForwardSymbol
    exact (contDiff_gaussianForwardCore j hρ hχ hpos (L := L) (by linarith) W).const_smul
      ((h ^ d)⁻¹ * L ^ (-(d : ℝ) / 2))
  have hc : HasCompactSupport (gaussianForwardSymbol j ρ χ h L W) :=
    hcρ.of_isClosed_subset (isClosed_tsupport _) (tsupport_gaussianForwardSymbol j ρ χ h L W)
  exact finiteMultiplier_sq_bound hb hc (by positivity) hh (by positivity)
    (hkernel W hW h hh L hL) ξ a x

theorem cutoff_one_mem_tsupport {d : ℕ} {ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ}
    {χ : TransverseSpace d → ℂ} {s : ℝ} {η : OAI.Analysis.Calculus.Current.SpatialSpace d}
    (h : radialAngularCutoff ρ χ s η = 1) : η ∈ tsupport ρ := by
  apply subset_tsupport
  intro hz
  simp [radialAngularCutoff, hz] at h

/-- Exact recovery by the inverse kernel on the frequency support selected
by the cutoff. No invertibility hypothesis on an abstract operator is used. -/
theorem gaussianWaveOutput_recovery {d : ℕ} {ι : Type*} [Fintype ι]
    {ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ} {χ : TransverseSpace d → ℂ}
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hχ : ContDiff ℝ ∞ χ)
    (hpos : ∀ η ∈ tsupport ρ, 0 < gaussianFrequencyK η)
    (hv : ∀ η ∈ tsupport ρ, ‖gaussianVelocity η‖ ≤ 1)
    {h L : ℝ} (hh : 0 < h) (hL : 1 ≤ L) (W : TransverseSpace d) (hW : ‖W‖ ≤ 1)
    (ξ : ι → OAI.Analysis.Calculus.Current.SpatialSpace d) (a : ι → ℂ)
    (hcut : ∀ i, radialAngularCutoff ρ χ (Real.sqrt L) ((2 * Real.pi * h) • ξ i) = 1)
    (x : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    (∫ y, scaledInverseKernel (gaussianInverseSymbol ρ χ h L W) (2 * Real.pi * h) (x - y) *
      gaussianWaveOutput 0 ρ χ h L W ξ a y) = finiteWave ξ a x := by
  have hb : ContDiff ℝ ∞ (gaussianInverseSymbol ρ χ h L W) := by
    unfold gaussianInverseSymbol
    exact (contDiff_gaussianInverseCore hρ hχ hpos hv (L := L) (by linarith) W hW).const_smul
      (h ^ d * L ^ ((d : ℝ) / 2))
  have hc : HasCompactSupport (gaussianInverseSymbol ρ χ h L W) :=
    hcρ.of_isClosed_subset (isClosed_tsupport _) (tsupport_gaussianInverseSymbol ρ χ h L W)
  unfold gaussianWaveOutput
  rw [scaledKernel_finiteWave hb hc (by positivity)]
  unfold finiteWave
  apply Finset.sum_congr rfl
  intro i _
  have hη := cutoff_one_mem_tsupport (hcut i)
  have he := gaussian_symbols_recover ρ χ (h := h) (L := L) hh (by linarith) W ((2 * Real.pi * h) • ξ i)
    (hpos _ hη) (gaussianB0_pos_of_small hW (hv _ hη)).ne'
  rw [hcut i, one_pow] at he
  have hc' : gaussianInverseSymbol ρ χ h L W ((2 * Real.pi * h) • ξ i) *
      (gaussianForwardSymbol 0 ρ χ h L W ((2 * Real.pi * h) • ξ i) * a i) = a i := by
    calc
      _ = (gaussianForwardSymbol 0 ρ χ h L W ((2 * Real.pi * h) • ξ i) *
        gaussianInverseSymbol ρ χ h L W ((2 * Real.pi * h) • ξ i)) * a i := by ring
      _ = a i := by rw [he, one_mul]
  exact congrArg (fun z : ℂ => z * planeWave (ξ i) x) hc'

/-- The output-density lower bound, valid throughout a semiclassical ball
around the observation point. -/
theorem gaussianWaveOutput_inverse_sq_bound {d : ℕ} {ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ}
    {χ : TransverseSpace d → ℂ} (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hpos : ∀ η ∈ tsupport ρ, 0 < gaussianFrequencyK η)
    (hv : ∀ η ∈ tsupport ρ, ‖gaussianVelocity η‖ ≤ 1)
    (Rχ RW : ℝ) (hsupp : tsupport χ ⊆ Metric.closedBall 0 Rχ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : TransverseSpace d, ‖W‖ ≤ 1 →
      ∀ h : ℝ, 0 < h → ∀ L : ℝ, 1 ≤ L → Real.sqrt L * ‖W‖ ≤ RW →
      ∀ {ι : Type} [Fintype ι] (ξ : ι → OAI.Analysis.Calculus.Current.SpatialSpace d) (a : ι → ℂ),
      (∀ i, radialAngularCutoff ρ χ (Real.sqrt L) ((2 * Real.pi * h) • ξ i) = 1) →
      ∀ x x' : OAI.Analysis.Calculus.Current.SpatialSpace d, ‖x - x'‖ ≤ h →
      ‖finiteWave ξ a x‖ ^ 2 ≤
        (C * h ^ d * L ^ (((gaussianDerivativeOrder d : ℕ) : ℝ) / 2 + d / 2)) ^ 2 *
          3 ^ (d + 3) * smoothedSquare h (gaussianWaveOutput 0 ρ χ h L W ξ a) x' := by
  obtain ⟨C, hC, hkernel⟩ := gaussianInverseAngularKernel_bound hρ hcρ hχ hcχ hpos hv Rχ RW hsupp
  refine ⟨C, hC, ?_⟩
  intro W hW h hh L hL hRW ι _ ξ a hcut x x' hdist
  have hm : Measurable (gaussianWaveOutput 0 ρ χ h L W ξ a) :=
    (continuous_finiteWave ξ _).measurable
  have hb := convolution_sq_le_nearby_smoothedSquare hh hm (norm_finiteWave_le ξ _)
    (by positivity : 0 ≤ C * h ^ d * L ^ (((gaussianDerivativeOrder d : ℕ) : ℝ) / 2 + d / 2))
    (hkernel W hW h hh L hL hRW) hdist
  rwa [gaussianWaveOutput_recovery hρ hcρ hχ hpos hv hh hL W hW ξ a hcut x] at hb

end OAI.Analysis.PDE.Concentration
