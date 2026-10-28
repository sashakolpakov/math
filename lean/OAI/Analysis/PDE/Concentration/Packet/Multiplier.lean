import OAI.Analysis.PDE.Concentration.GaussianCurrent
import OAI.Analysis.PDE.Concentration.Packet.Gaussian
import OAI.Analysis.PDE.Concentration.Packet.Phase

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.Calculus.Current

def transverseRatio {d : ℕ} (z : OAI.Analysis.Calculus.Current.Index d → ℂ) : TransverseSpace d :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℂ)).symm (OAI.Analysis.Calculus.Current.ratio z)

def currentScalarPart {d : ℕ} (j : Fin 2) (W v : Fin d → ℂ) : ℝ :=
  if j = 0 then (currentTimeFactor W v).re else (currentTimeFactor W v).im

theorem gaussianB_eq_currentScalarPart {d : ℕ} (j : Fin 2) (W : TransverseSpace d)
    (η : OAI.Analysis.Calculus.Current.SpatialSpace d) : gaussianB j (W, η) = currentScalarPart j W (gaussianVelocity η) := by
  unfold gaussianB currentScalarPart
  split
  · exact gaussianB0_eq_timeFactor W η
  · exact gaussianB1_eq_timeFactor W η

theorem packet_gaussian_distance {d : ℕ} {κ : ℝ} (hκ : 0 < κ) (v : Fin d → ℝ)
    (z : OAI.Analysis.Calculus.Current.Index d → ℂ) :
    ‖transverseRatio z - gaussianVelocity (packetSpatialFrequency κ v)‖ ^ 2 =
      OAI.Analysis.Calculus.Current.squaredDistance (OAI.Analysis.Calculus.Current.ratio z) v := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  simp [gaussianVelocity_packet_apply hκ, transverseRatio]

/-- The actual Gaussian multiplier agrees with a normalized current mode,
including its dimension-dependent frequency weight. -/
theorem gaussianForwardSymbol_packet {d : ℕ} (j : Fin 2)
    (ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ) (χ : TransverseSpace d → ℂ)
    {h L κ : ℝ} (hh : 0 < h) (hL : 0 < L) (hκ : 0 < κ)
    (v : Fin d → ℝ) (z : OAI.Analysis.Calculus.Current.Index d → ℂ) (hz : ‖z none‖ = h * L)
    (hcut : radialAngularCutoff ρ χ (Real.sqrt L) (h • packetSpatialFrequency κ v) = 1) :
    gaussianForwardSymbol j ρ χ h L (transverseRatio z) (h • packetSpatialFrequency κ v) =
      (currentScalarPart j (OAI.Analysis.Calculus.Current.ratio z) (fun i => (v i : ℂ)) : ℂ) *
        ((κ / ‖z none‖) ^ ((d : ℝ) / 2) : ℝ) *
        (Real.exp (-κ * ‖z none‖ / 2 * OAI.Analysis.Calculus.Current.squaredDistance (OAI.Analysis.Calculus.Current.ratio z) v) : ℝ) := by
  have hk : gaussianFrequencyK (h • packetSpatialFrequency κ v) = h * κ := by
    rw [gaussianFrequencyK_smul hh.le, gaussianFrequencyK_packet hκ.le]
  have hv : gaussianVelocity (h • packetSpatialFrequency κ v) =
      gaussianVelocity (packetSpatialFrequency κ v) := gaussianVelocity_smul hh.ne' hh.le _
  have hb : gaussianB j (transverseRatio z, h • packetSpatialFrequency κ v) =
      currentScalarPart j (OAI.Analysis.Calculus.Current.ratio z) (fun i => (v i : ℂ)) := by
    rw [gaussianB_eq_currentScalarPart, hv]
    congr 1
    funext i
    exact gaussianVelocity_packet_apply hκ v i
  rw [gaussianForwardSymbol_eq_source j ρ χ hh hL _ _ (by rw [hk]; positivity),
    hcut, one_mul, hb, hk, hv, packet_gaussian_distance hκ, hz]
  have hdiv : h * κ / (h * (h * L)) = κ / (h * L) := by field_simp
  rw [hdiv, Complex.ofReal_exp]
  congr 2
  push_cast
  ring

def packetScalarCurrent {d : ℕ} {ι : Type*} [Fintype ι] (j : Fin 2)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (z : OAI.Analysis.Calculus.Current.Index d → ℂ) : ℂ :=
  ∑ i, (currentScalarPart j (OAI.Analysis.Calculus.Current.ratio z) (fun k => (v i k : ℂ)) : ℂ) *
    currentModeScalar (κ i) (cR i) (cI i) (v i) x z

theorem gaussianWaveOutput_eq_packetScalarCurrent {d : ℕ} {ι : Type*} [Fintype ι]
    (j : Fin 2) (ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ) (χ : TransverseSpace d → ℂ)
    {h L : ℝ} (hh : 0 < h) (hL : 0 < L)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (hκ : ∀ i, 0 < κ i)
    (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (z : OAI.Analysis.Calculus.Current.Index d → ℂ) (hz : ‖z none‖ = h * L)
    (hcut : ∀ i, radialAngularCutoff ρ χ (Real.sqrt L) (h • packetSpatialFrequency (κ i) (v i)) = 1)
    (y : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    gaussianWaveOutput j ρ χ h L (transverseRatio z)
      (fun i => packetCycleFrequency (κ i) (v i))
      (fun i => OAI.Analysis.Calculus.Current.phaseComplex (cR i) (cI i) (OAI.Analysis.Calculus.Current.modeCovector (κ i) (v i)) x) y =
    packetScalarCurrent j κ cR cI v (x - nullSpatialShift y) z := by
  unfold gaussianWaveOutput finiteWave packetScalarCurrent
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  rw [scaled_packetCycleFrequency,
    gaussianForwardSymbol_packet j ρ χ hh hL (hκ i) (v i) z hz (hcut i)]
  unfold currentModeScalar
  rw [phaseComplex_translate_packet]
  push_cast
  ring

/-- The literal quaternionic current density is the sum of the squares of
the two constructed Gaussian Fourier multipliers, not an auxiliary proxy. -/
theorem waveCurrent_timeComponent_gaussian {d : ℕ} {ι : Type*} [Fintype ι]
    (ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ) (χ : TransverseSpace d → ℂ)
    {h L : ℝ} (hh : 0 < h) (hL : 0 < L)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (hκ : ∀ i, 0 < κ i)
    (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (z : OAI.Analysis.Calculus.Current.Index d → ℂ) (hz : ‖z none‖ = h * L)
    (hcut : ∀ i, radialAngularCutoff ρ χ (Real.sqrt L) (h • packetSpatialFrequency (κ i) (v i)) = 1)
    (y : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    OAI.Analysis.Calculus.Current.timeComponent (OAI.Analysis.Calculus.Current.waveCurrent κ cR cI v (x - nullSpatialShift y) z) =
      ‖gaussianWaveOutput 0 ρ χ h L (transverseRatio z)
        (fun i => packetCycleFrequency (κ i) (v i))
        (fun i => OAI.Analysis.Calculus.Current.phaseComplex (cR i) (cI i) (OAI.Analysis.Calculus.Current.modeCovector (κ i) (v i)) x) y‖ ^ 2 +
      ‖gaussianWaveOutput 1 ρ χ h L (transverseRatio z)
        (fun i => packetCycleFrequency (κ i) (v i))
        (fun i => OAI.Analysis.Calculus.Current.phaseComplex (cR i) (cI i) (OAI.Analysis.Calculus.Current.modeCovector (κ i) (v i)) x) y‖ ^ 2 := by
  have hY : z none ≠ 0 := by
    intro he
    rw [he, norm_zero] at hz
    exact (mul_pos hh hL).ne' hz.symm
  rw [gaussianWaveOutput_eq_packetScalarCurrent 0 ρ χ hh hL κ cR cI v hκ x z hz hcut,
    gaussianWaveOutput_eq_packetScalarCurrent 1 ρ χ hh hL κ cR cI v hκ x z hz hcut]
  simpa [packetScalarCurrent, currentScalarPart] using
    waveCurrent_timeComponent_eq κ cR cI v hκ (x - nullSpatialShift y) z hY

end OAI.Analysis.PDE.Concentration
