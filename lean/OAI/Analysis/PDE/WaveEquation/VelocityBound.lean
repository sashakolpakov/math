import OAI.Analysis.PDE.WaveEquation.VelocityScaling

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology
noncomputable section
namespace OAI.Analysis.PDE.WaveEquation

theorem angularSchwartzMultiplier_sub_one {n : ℕ} {m : Space n → ℝ}
    (hm : m.HasTemperateGrowth) (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    OAI.Analysis.Fourier.BesselPotential.angularSchwartzMultiplier (fun ξ ↦ m ξ - 1) f x =
      OAI.Analysis.Fourier.BesselPotential.angularSchwartzMultiplier m f x - f x := by
  have hd : (fun ξ ↦ m ξ - 1).HasTemperateGrowth :=
    hm.sub (Function.HasTemperateGrowth.const 1)
  have hi : Integrable (fun ξ ↦ m ξ • OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ) := by
    have he := funext (OAI.Analysis.Fourier.BesselPotential.angularFourier_angularSchwartzMultiplier hm f)
    rw [← he]
    exact OAI.Analysis.Fourier.Restriction.integrable_angularFourier_schwartz (OAI.Analysis.Fourier.BesselPotential.angularSchwartzMultiplier m f)
  rw [OAI.Analysis.Fourier.BesselPotential.angularSchwartzMultiplier_eq_integral hd,
    OAI.Analysis.Fourier.BesselPotential.angularSchwartzMultiplier_eq_integral hm,
    ← OAI.Analysis.Fourier.Restriction.angularInverse_angularFourier_schwartz f x,
    ← OAI.Analysis.Fourier.LocalSmoothing.angularInverse_sub_of_integrable hi (OAI.Analysis.Fourier.Restriction.integrable_angularFourier_schwartz f)]
  congr 1
  funext ξ
  simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
  ring

/-- `J/|D|` with its low frequencies removed is bounded on every finite
`Lᵖ`, `p ≥ 1`. Its order-zero principal part is the identity; the rest is
summed as an actual order-minus-two annular kernel. -/
theorem velocityShiftSymbol_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Space n) ℂ, ∀ p : ℝ≥0∞,
      1 ≤ p → p ≠ ⊤ →
      eLpNorm (OAI.Analysis.Fourier.BesselPotential.angularSchwartzMultiplier velocityShiftSymbol f) p volume ≤
        ENNReal.ofReal C * eLpNorm f p volume := by
  let d : Space n → ℝ := fun ξ ↦ velocityShiftSymbol ξ - 1
  have hd : d.HasTemperateGrowth :=
    (temperate_velocityShiftSymbol n).sub (Function.HasTemperateGrowth.const 1)
  let low : Space n → ℂ := fun ξ ↦ (d ξ : ℂ) * OAI.Analysis.Fourier.LocalSmoothing.smoothingLowCutoff ξ
  have hl : ContDiff ℝ ∞ low :=
    (Complex.ofRealCLM.contDiff.comp hd.1).mul (OAI.Analysis.Fourier.LocalSmoothing.contDiff_smoothingLowCutoff n)
  have hlc : HasCompactSupport low := (OAI.Analysis.Fourier.LocalSmoothing.hasCompactSupport_smoothingLowCutoff n).mul_left
  let B : ℝ≥0∞ := eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse low) 1 volume
  have hBt : B ≠ ⊤ := (memLp_one_iff_integrable.mpr
    (OAI.Analysis.Fourier.BochnerRiesz.integrable_angularInverse_cutoff hl hlc)).eLpNorm_ne_top
  obtain ⟨A,hA,hAb⟩ := OAI.Analysis.Fourier.BochnerRiesz.uniform_frequencyHalfWave_zero_bound
    (K := Icc (0:ℝ) 1) isCompact_Icc (OAI.Analysis.Fourier.LocalSmoothing.hasCompactSupport_smoothingAnnularCutoff n)
    (contDiff_velocityShiftAnnulus n) (tsupport_velocityShiftAnnulus n)
  let w : ℕ → ℝ := fun j ↦ OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale j ^ 2
  have hw0 : ∀ j, 0 ≤ w j := fun j ↦ sq_nonneg _
  have hw : Summable w := by
    have he : w = fun j : ℕ ↦ ((2:ℝ)⁻¹ ^ 2)^j := by
      funext j
      exact pow_right_comm _ j 2
    rw [he]
    exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
  let D : ℝ := B.toReal + A * ∑' j, w j
  have hD : 0 ≤ D := add_nonneg ENNReal.toReal_nonneg (mul_nonneg hA (tsum_nonneg hw0))
  refine ⟨1+D,by linarith,?_⟩
  intro f p hp hptop
  let u := OAI.Analysis.Fourier.BesselPotential.angularSchwartzMultiplier d f
  have hu : eLpNorm u p volume ≤ ENNReal.ofReal D * eLpNorm f p volume := by
    apply schwartz_norm_le_of_dyadic_bounds u hp hw0 hw ENNReal.toReal_nonneg hA
    · have he : OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave OAI.Analysis.Fourier.LocalSmoothing.smoothingLowCutoff 1 0 u =
          OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave low 1 0 f := by
        funext x
        simpa only [one_smul] using frequencyHalfWave_zero_transfer f u
          OAI.Analysis.Fourier.LocalSmoothing.smoothingLowCutoff low 1 1 (fun ξ ↦ by
            simp only [u, OAI.Analysis.Fourier.BesselPotential.angularFourier_angularSchwartzMultiplier hd, low,
              Complex.real_smul, Complex.ofReal_one, one_mul, one_smul]
            ring) x
      rw [he, ENNReal.ofReal_toReal hBt]
      exact OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_frequencyHalfWave_zero_le hl.continuous hlc
        (by norm_num) f.integrable hp hptop
    · intro j
      have he : OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave OAI.Analysis.Fourier.LocalSmoothing.smoothingAnnularCutoff (OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale j) 0 u =
          w j • OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave (fun ξ ↦ velocityShiftAnnulus (OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale j,ξ))
            (OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale j) 0 f := by
        funext x
        apply frequencyHalfWave_zero_transfer
        intro ξ
        simp only [u, OAI.Analysis.Fourier.BesselPotential.angularFourier_angularSchwartzMultiplier hd, Complex.real_smul]
        rw [← mul_assoc, mul_comm (OAI.Analysis.Fourier.LocalSmoothing.smoothingAnnularCutoff _),
          velocityShiftAnnulus_scaling (OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale_pos j)
            (OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale_le_one j)]
      rw [he, eLpNorm_const_smul, Real.enorm_eq_ofReal (hw0 j)]
      have hb := hAb (OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale j)
        ⟨(OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale_pos j).le,OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale_le_one j⟩
        (OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale j) (OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale_pos j) f f.integrable p hp hptop
      apply (mul_le_mul_right hb _).trans_eq
      rw [ENNReal.ofReal_mul hA]
      ac_rfl
  have he : (OAI.Analysis.Fourier.BesselPotential.angularSchwartzMultiplier velocityShiftSymbol f : Space n → ℂ) =
      (fun x ↦ f x + u x) := by
    funext x
    have hx := angularSchwartzMultiplier_sub_one (temperate_velocityShiftSymbol n) f x
    change u x = _ at hx
    rw [hx]
    ring
  rw [he]
  calc
    _ ≤ eLpNorm f p volume + eLpNorm u p volume := eLpNorm_add_le hp
    _ ≤ eLpNorm f p volume + ENNReal.ofReal D * eLpNorm f p volume := add_le_add le_rfl hu
    _ = _ := by rw [ENNReal.ofReal_add (by norm_num) hD, ENNReal.ofReal_one, add_mul, one_mul]

end OAI.Analysis.PDE.WaveEquation
