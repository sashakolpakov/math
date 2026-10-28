import OAI.Analysis.PDE.Concentration.FourierMultiplier
import OAI.Analysis.PDE.Concentration.Packet.Frequency

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.Calculus.Current

def packetCycleFrequency {d : ℕ} (κ : ℝ) (v : Fin d → ℝ) : OAI.Analysis.Calculus.Current.SpatialSpace d :=
  (2 * Real.pi)⁻¹ • packetSpatialFrequency κ v

theorem phaseComplex_eq_exp {d : ℕ} (cR cI : ℝ) (L x : OAI.Analysis.Calculus.Current.Index d → ℝ) :
    OAI.Analysis.Calculus.Current.phaseComplex cR cI L x = (cR + cI * Complex.I) *
      Complex.exp ((OAI.Analysis.Calculus.Current.phaseArgument L x : ℂ) * Complex.I) := by
  rw [Complex.exp_mul_I]
  apply Complex.ext <;> simp [OAI.Analysis.Calculus.Current.phaseComplex, OAI.Analysis.Calculus.Current.phaseF, OAI.Analysis.Calculus.Current.phaseG, Complex.mul_re, Complex.mul_im,
    Complex.cos_ofReal_re, Complex.sin_ofReal_re]

theorem phaseComplex_translate_packet {d : ℕ} (κ cR cI : ℝ) (v : Fin d → ℝ)
    (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (y : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    OAI.Analysis.Calculus.Current.phaseComplex cR cI (OAI.Analysis.Calculus.Current.modeCovector κ v) (x - nullSpatialShift y) =
      OAI.Analysis.Calculus.Current.phaseComplex cR cI (OAI.Analysis.Calculus.Current.modeCovector κ v) x * planeWave (packetCycleFrequency κ v) y := by
  have ha : OAI.Analysis.Calculus.Current.phaseArgument (OAI.Analysis.Calculus.Current.modeCovector κ v) (x - nullSpatialShift y) =
      OAI.Analysis.Calculus.Current.phaseArgument (OAI.Analysis.Calculus.Current.modeCovector κ v) x + inner ℝ y (packetSpatialFrequency κ v) := by
    simp only [OAI.Analysis.Calculus.Current.phaseArgument, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    change OAI.Analysis.Calculus.Current.phaseArgument (OAI.Analysis.Calculus.Current.modeCovector κ v) x -
      OAI.Analysis.Calculus.Current.phaseArgument (OAI.Analysis.Calculus.Current.modeCovector κ v) (nullSpatialShift y) = _
    rw [packetSpatialFrequency_phase, real_inner_comm]
    unfold OAI.Analysis.Calculus.Current.phaseArgument
    ring
  have hb : 2 * Real.pi * inner ℝ y (packetCycleFrequency κ v) =
      inner ℝ y (packetSpatialFrequency κ v) := by
    rw [packetCycleFrequency, inner_smul_right]
    field_simp
  rw [phaseComplex_eq_exp, ha, Complex.ofReal_add, phaseComplex_eq_exp, planeWave, hb]
  simp only [add_mul, Complex.exp_add]
  ring

theorem scaled_packetCycleFrequency {d : ℕ} (h κ : ℝ) (v : Fin d → ℝ) :
    (2 * Real.pi * h) • packetCycleFrequency κ v = h • packetSpatialFrequency κ v := by
  rw [packetCycleFrequency, smul_smul]
  congr 1
  field_simp

end OAI.Analysis.PDE.Concentration
