import OAI.Analysis.Fourier.SquareFunction.OperatorDecomposition
import OAI.Analysis.Fourier.WavePackets.SteinAmplitude
import OAI.Analysis.Fourier.WavePackets.SteinRemainder

open OAI.Analysis.Fourier.Wave

/-! The Stein square-function estimate, deduced from Euclidean local smoothing.
The operator here is the actual radius derivative Fourier integral, not a
surrogate square function or an assumed multiplier estimate. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set
open scoped ENNReal ContDiff

theorem localSmoothing_steinSquareFunction_gt_two (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {p α : ℝ} (hp : 2 < p)
    (hα : 1 / 2 + OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (OAI.Analysis.Fourier.SquareFunction.steinSquareFunction α f) (ENNReal.ofReal p) volume ∧
      eLpNorm (OAI.Analysis.Fourier.SquareFunction.steinSquareFunction α f) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume := by
  let : NeZero n := ⟨by omega⟩
  have hα0 : 1 / 2 < α := by
    have : 0 ≤ OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p := le_max_left _ _
    linarith
  obtain ⟨B, hB, hcB, hzB, heB, hsB⟩ := OAI.Analysis.Fourier.WavePackets.exists_stein_amplitude n α
  obtain ⟨C, hC, hcC, heC, hsC⟩ := OAI.Analysis.Fourier.WavePackets.exists_stein_remainder n α
  let A : ℝ × Space n → ℂ := fun z => (‖z.2‖ ^ 2 : ℝ) * C z
  have hA : ContDiff ℝ ∞ A :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_snd.norm_sq ℝ)).mul hC
  have hcA : HasCompactSupport A := hcC.mul_left
  have heA (r : ℝ) (hr : r ∈ Icc (1 : ℝ) 2) (ξ : Space n) :
      A (r, ξ) = (radiusMultiplier α ‖ξ‖ r : ℂ) *
        (1 - (OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff (4 * (r - ‖ξ‖)) : ℂ)) :=
    heC r ξ hr.1 hr.2
  obtain ⟨E, hE, hEb⟩ := localSmoothing_boundaryShellEnvelope hls hn hB hcB hzB
    (fun r ξ h => ⟨(hsB r ξ h).2.1.le, (hsB r ξ h).2.2.le⟩) hp hα 2
  obtain ⟨D, hD, hDb⟩ := dyadicRemainderSquare_bound hA hcA hα0 hp
    (fun r hr ξ => by rw [heA r hr ξ]; exact norm_remainder_symbol_le α ‖ξ‖ r)
  have hED : E + D ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hE, hD⟩
  have hconstant : E + D ≤ ENNReal.ofReal ((E + D).toReal + 1) := by
    calc
      _ = ENNReal.ofReal (E + D).toReal := (ENNReal.ofReal_toReal hED).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
  refine ⟨(E + D).toReal + 1, by positivity, fun f => ?_⟩
  have hpoint (x : Space n) : OAI.Analysis.Fourier.SquareFunction.steinSquareFunction α f x ≤
      boundaryShellEnvelope B hB.continuous α 2 f x + dyadicSmoothRadiusSquare A hA.continuous f x := by
    apply (steinSquareFunction_le_boundary_add_remainder hA.continuous hcA hα0 heA f x).trans
    exact add_le_add (dyadicBoundarySquare_le_envelope hB.continuous hcB hα0
      (fun r hr ξ => heB r ξ hr.1 hr.2) f x) le_rfl
  have hb : eLpNorm (OAI.Analysis.Fourier.SquareFunction.steinSquareFunction α f) (ENNReal.ofReal p) volume ≤
      (E + D) * eLpNorm f (ENNReal.ofReal p) volume := by
    calc
      _ ≤ eLpNorm (fun x => boundaryShellEnvelope B hB.continuous α 2 f x +
          dyadicSmoothRadiusSquare A hA.continuous f x) (ENNReal.ofReal p) volume :=
        eLpNorm_mono_enorm (measurable_steinSquareFunction α f).aestronglyMeasurable
          (fun x => by simpa only [enorm_eq_self] using hpoint x)
      _ ≤ eLpNorm (boundaryShellEnvelope B hB.continuous α 2 f) (ENNReal.ofReal p) volume +
          eLpNorm (dyadicSmoothRadiusSquare A hA.continuous f) (ENNReal.ofReal p) volume :=
        eLpNorm_add_le (by simpa only [ENNReal.ofReal_one] using
          ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))
      _ ≤ E * eLpNorm f (ENNReal.ofReal p) volume + D * eLpNorm f (ENNReal.ofReal p) volume :=
        add_le_add (hEb f) (hDb f)
      _ = _ := (add_mul _ _ _).symm
  exact ⟨hb.trans_lt (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hED)
    (f.memLp _ volume).eLpNorm_lt_top), hb.trans (mul_le_mul' hconstant le_rfl)⟩

theorem stein_threshold_eq (n : ℕ) (p : ℝ) :
    1 / 2 + OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p = max (1 / 2) ((n : ℝ) * (1 / 2 - 1 / p)) := by
  unfold OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder
  rw [add_max]
  congr 1 <;> ring

/-- The complete strict Stein range, including the unconditional Plancherel
endpoint p=2. No auxiliary analytic estimate is assumed. -/
theorem localSmoothing_steinSquareConjecture (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing) :
    OAI.Analysis.Fourier.SquareFunction.SteinSquareConjecture := by
  intro n hn p α hp hα
  by_cases hp2 : p = 2
  · subst p
    let : NeZero n := ⟨by omega⟩
    have hα0 : 1 / 2 < α := lt_of_le_of_lt (le_max_left _ _) hα
    simpa only [ENNReal.ofReal_ofNat] using steinSquareFunction_L2 (n := n) hα0
  · exact localSmoothing_steinSquareFunction_gt_two hls hn (lt_of_le_of_ne hp (Ne.symm hp2))
      (by rwa [stein_threshold_eq])

end OAI.Analysis.Fourier.SquareFunction
