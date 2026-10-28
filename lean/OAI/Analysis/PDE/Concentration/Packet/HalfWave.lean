import OAI.Analysis.PDE.Concentration.Packet.Gaussian
import OAI.Analysis.PDE.Concentration.Output.Coordinates
import OAI.Analysis.PDE.Concentration.DensityBounds

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.Calculus.Current
open scoped ContDiff

theorem phaseArgument_physicalNullTime {d : ℕ} {κ : ℝ} (hκ : 0 ≤ κ)
    (v : Fin d → ℝ) (t : ℝ) :
    OAI.Analysis.Calculus.Current.phaseArgument (OAI.Analysis.Calculus.Current.modeCovector κ v) (physicalNullTime d t) =
      -t * ‖packetSpatialFrequency κ v‖ := by
  rw [norm_packetSpatialFrequency hκ]
  simp only [OAI.Analysis.Calculus.Current.phaseArgument, OAI.Analysis.Calculus.Current.modeCovector, Fintype.sum_option, OAI.Analysis.Calculus.Current.realPhaseRow, physicalNullTime,
    mul_zero, Finset.sum_const_zero, add_zero]
  ring

theorem planeWave_packetCycleFrequency {d : ℕ} (κ : ℝ) (v : Fin d → ℝ) (y : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    planeWave (packetCycleFrequency κ v) y =
      Complex.exp ((inner ℝ y (packetSpatialFrequency κ v) : ℝ) * Complex.I) := by
  unfold planeWave packetCycleFrequency
  rw [inner_smul_right]
  congr 2
  field_simp

/-- The sign and normalization are exactly the half-wave convention used by
the transfer theorem: `exp(-I*t*|ξ|) exp(I*x·ξ)`, with angular frequencies. -/
theorem packetBaseWave_eq_halfWave_sum {d : ℕ} {ι : Type*} [Fintype ι]
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (hκ : ∀ i, 0 ≤ κ i) (t : ℝ) (y : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    packetBaseWave κ cR cI v (physicalNullTime d t) y =
      ∑ i, (cR i + cI i * Complex.I) *
        Complex.exp (-Complex.I * ((t * ‖packetSpatialFrequency (κ i) (v i)‖ : ℝ) : ℂ)) *
        Complex.exp ((inner ℝ y (packetSpatialFrequency (κ i) (v i)) : ℝ) * Complex.I) := by
  unfold packetBaseWave finiteWave
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only
  rw [phaseComplex_eq_exp, phaseArgument_physicalNullTime (hκ i), planeWave_packetCycleFrequency]
  congr 2
  congr 1
  push_cast
  ring

theorem contDiff_packetBaseWave_time_space {d : ℕ} {ι : Type*} [Fintype ι]
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    ContDiff ℝ ∞ (fun p : ℝ × OAI.Analysis.Calculus.Current.SpatialSpace d =>
      packetBaseWave κ cR cI v (physicalNullTime d p.1) p.2) := by
  simp_rw [packetBaseWave_eq_halfWave_sum κ cR cI v hκ]
  apply ContDiff.sum
  intro i hi
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × OAI.Analysis.Calculus.Current.SpatialSpace d =>
      ((p.1 * ‖packetSpatialFrequency (κ i) (v i)‖ : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_fst.mul contDiff_const)
  have h2 : ContDiff ℝ ∞ (fun p : ℝ × OAI.Analysis.Calculus.Current.SpatialSpace d =>
      ((inner ℝ p.2 (packetSpatialFrequency (κ i) (v i)) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_snd.inner ℝ contDiff_const)
  exact (contDiff_const.mul (Complex.contDiff_exp.comp (contDiff_const.mul h1))).mul
    (Complex.contDiff_exp.comp (h2.mul contDiff_const))

end OAI.Analysis.PDE.Concentration
