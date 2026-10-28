import OAI.Analysis.PDE.Concentration.Packet.Multiplier
import OAI.Analysis.PDE.Concentration.Lattice.Smoothing
import OAI.Analysis.PDE.Concentration.FourierPeriodicity

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion
open scoped Matrix Matrix.Norms.Elementwise

local instance {ι : Type*} [Fintype ι] : NormedAddCommGroup (Matrix ι ι (Quaternion ℝ)) :=
  inferInstanceAs (NormedAddCommGroup (ι → ι → Quaternion ℝ))
local instance {ι : Type*} [Fintype ι] : NormedSpace ℝ (Matrix ι ι (Quaternion ℝ)) :=
  inferInstanceAs (NormedSpace ℝ (ι → ι → Quaternion ℝ))
local instance {ι : Type*} [Fintype ι] : ContinuousENorm (Matrix ι ι (Quaternion ℝ)) :=
  inferInstanceAs (ContinuousENorm (ι → ι → Quaternion ℝ))

def timeComponentCLM (d : ℕ) : Matrix (OAI.Analysis.Calculus.Current.Index d) (OAI.Analysis.Calculus.Current.Index d) (Quaternion ℝ) →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • OAI.Analysis.Calculus.Quaternion.currentQuadraticCLM (OAI.Analysis.Calculus.Current.timeVector d)

theorem timeComponentCLM_apply {d : ℕ} (A : Matrix (OAI.Analysis.Calculus.Current.Index d) (OAI.Analysis.Calculus.Current.Index d) (Quaternion ℝ)) :
    timeComponentCLM d A = OAI.Analysis.Calculus.Current.timeComponent A := by
  rw [OAI.Analysis.Calculus.Current.timeComponent_eq_quadratic]
  change (1 / 2 : ℝ) * (star (OAI.Analysis.Calculus.Current.timeVector d) ⬝ᵥ (A *ᵥ OAI.Analysis.Calculus.Current.timeVector d)).re = _
  ring

theorem timeComponent_integral {d : ℕ} {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {A : α → Matrix (OAI.Analysis.Calculus.Current.Index d) (OAI.Analysis.Calculus.Current.Index d) (Quaternion ℝ)}
    (hA : Integrable A μ) : OAI.Analysis.Calculus.Current.timeComponent (∫ x, A x ∂μ) = ∫ x, OAI.Analysis.Calculus.Current.timeComponent (A x) ∂μ := by
  calc
    _ = timeComponentCLM d (∫ x, A x ∂μ) := (timeComponentCLM_apply _).symm
    _ = ∫ x, timeComponentCLM d (A x) ∂μ := ((timeComponentCLM d).integral_comp_comm hA).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun x => timeComponentCLM_apply (A x))

theorem nullSpatialShift_sub {d : ℕ} (x y : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    nullSpatialShift (x - y) = nullSpatialShift x - nullSpatialShift y := by
  funext i
  cases i with
  | none => simp [nullSpatialShift, sub_div] ; ring
  | some i => cases i <;> simp [nullSpatialShift, sub_div] <;> ring

def packetGaussianField {d : ℕ} {ι : Type*} [Fintype ι]
    (j : Fin 2) (ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ) (χ : TransverseSpace d → ℂ)
    (h L : ℝ) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (z : OAI.Analysis.Calculus.Current.Index d → ℂ) : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ :=
  gaussianWaveOutput j ρ χ h L (transverseRatio z)
    (fun i => packetCycleFrequency (κ i) (v i))
    (fun i => OAI.Analysis.Calculus.Current.phaseComplex (cR i) (cI i) (OAI.Analysis.Calculus.Current.modeCovector (κ i) (v i)) x)

theorem continuous_packetGaussianField {d : ℕ} {ι : Type*} [Fintype ι]
    (j : Fin 2) (ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ) (χ : TransverseSpace d → ℂ)
    (h L : ℝ) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (z : OAI.Analysis.Calculus.Current.Index d → ℂ) :
    Continuous (packetGaussianField j ρ χ h L κ cR cI v x z) := continuous_finiteWave _ _

theorem packetGaussianField_periodic_of_dual {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (j : Fin 2) (ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ) (χ : TransverseSpace d → ℂ)
    (h L : ℝ) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (hfreq : ∀ i l, ∃ m : ℤ, inner ℝ (packetSpatialFrequency (κ i) (v i))
      (R (EuclideanSpace.single l 1)) = (m : ℝ) * (2 * Real.pi) / 100)
    (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (z : OAI.Analysis.Calculus.Current.Index d → ℂ) (y : OAI.Analysis.Calculus.Current.SpatialSpace d) (k : Option (Fin d) → ℤ) :
    packetGaussianField j ρ χ h L κ cR cI v x z (y + (100 : ℝ) • R (latticeIntegerVector k)) =
      packetGaussianField j ρ χ h L κ cR cI v x z y := by
  apply finiteWave_periodic_integer
  intro i
  choose m hm using hfreq i
  exact ⟨∑ l, k l * m l, packetCycleFrequency_lattice_integer R (κ i) (v i) m hm k⟩

/-- Exact identification of the source's regularized time density. The only
lattice premise is periodicity of its Fourier modes; the current averaging,
the two orthogonal components and the positive cofactor term are retained. -/
theorem latticeRegularizedCurrent_time_gaussian {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ) (χ : TransverseSpace d → ℂ)
    {h L : ℝ} (hh : 0 < h) (hL : 0 < L) (a : ℝ)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (hκ : ∀ i, 0 < κ i)
    (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (z : OAI.Analysis.Calculus.Current.Index d → ℂ) (hz : ‖z none‖ = h * L)
    (hcut : ∀ i, radialAngularCutoff ρ χ (Real.sqrt L) (h • packetSpatialFrequency (κ i) (v i)) = 1)
    (hfreq : ∀ i l, ∃ m : ℤ, inner ℝ (packetSpatialFrequency (κ i) (v i))
      (R (EuclideanSpace.single l 1)) = (m : ℝ) * (2 * Real.pi) / 100)
    (y : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    OAI.Analysis.Calculus.Current.timeComponent (latticeRegularizedCurrent R h a κ cR cI v (x - nullSpatialShift y) z) =
      OAI.Analysis.Calculus.Current.phaseCutoff (OAI.Analysis.Calculus.Current.phi z / (a : ℂ)) *
        (smoothedSquare h (packetGaussianField 0 ρ χ h L κ cR cI v x z) y +
         smoothedSquare h (packetGaussianField 1 ρ χ h L κ cR cI v x z) y) +
      h ^ (50 * (d + 1)) * OAI.Analysis.Calculus.Current.timeComponent (OAI.Analysis.Calculus.Current.fiberCofactor (1 / 10) a z) := by
  let := latticeKernelMeasure_isProbability R h hh
  have hp := fun j => packetGaussianField_periodic_of_dual R j ρ χ h L κ cR cI v hfreq x z
  have hY : z none ≠ 0 := by
    intro he
    rw [he, norm_zero] at hz
    exact (mul_pos hh hL).ne' hz.symm
  have hA := integrable_latticeWave_translates R h hh κ cR cI v (x - nullSpatialShift y) z hY
  have hi (j : Fin 2) : Integrable (fun t =>
      ‖packetGaussianField j ρ χ h L κ cR cI v x z (y - R (spatialCubeVector t))‖ ^ 2)
      (latticeKernelMeasure R h) := by
    have hc : Continuous (fun t => packetGaussianField j ρ χ h L κ cR cI v x z
        (y - R (spatialCubeVector t))) :=
      (continuous_packetGaussianField j ρ χ h L κ cR cI v x z).comp
        (continuous_const.sub (R.continuous.comp (continuous_spatialCubeVector d)))
    exact (hc.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [latticeRegularizedCurrent, OAI.Analysis.Calculus.Current.regularizedCurrent, OAI.Analysis.Calculus.Current.timeComponent_add, OAI.Analysis.Calculus.Current.timeComponent_smul,
    OAI.Analysis.Calculus.Current.cutoffCurrent, OAI.Analysis.Calculus.Current.timeComponent_smul, OAI.Analysis.Calculus.Current.averagedWaveCurrent, timeComponent_integral hA]
  congr 2
  calc
    _ = ∫ t, (‖packetGaussianField 0 ρ χ h L κ cR cI v x z (y - R (spatialCubeVector t))‖ ^ 2 +
        ‖packetGaussianField 1 ρ χ h L κ cR cI v x z (y - R (spatialCubeVector t))‖ ^ 2)
        ∂latticeKernelMeasure R h := by
      apply integral_congr_ae
      filter_upwards [] with t
      have he : x - nullSpatialShift y + latticeCubeShift R t =
          x - nullSpatialShift (y - R (spatialCubeVector t)) := by
        rw [nullSpatialShift_sub]
        unfold latticeCubeShift
        abel
      rw [he]
      exact waveCurrent_timeComponent_gaussian ρ χ hh hL κ cR cI v hκ x z hz hcut _
    _ = _ := by
      rw [integral_add (hi 0) (hi 1),
        integral_latticeKernel_square R hh _ (continuous_packetGaussianField 0 ρ χ h L κ cR cI v x z) (hp 0),
        integral_latticeKernel_square R hh _ (continuous_packetGaussianField 1 ρ χ h L κ cR cI v x z) (hp 1)]

end OAI.Analysis.PDE.Concentration
