import OAI.Analysis.Calculus.Current.RegularizedDivergence
import OAI.Analysis.Calculus.Quaternion.CompactSmooth

/-! Full smoothness of the compactly averaged regularized current. -/

noncomputable section
namespace OAI.Analysis.Calculus.Current

open _root_.MeasureTheory OAI.Analysis.Calculus.Quaternion
open scoped Matrix Matrix.Norms.Elementwise Topology ContDiff

variable {d : ℕ} {ι α : Type*} [Fintype ι]
  [TopologicalSpace α] [CompactSpace α] [T2Space α] [SecondCountableTopology α]
  [MeasurableSpace α] [BorelSpace α] (μ : Measure α) [IsFiniteMeasure μ]

theorem contDiffOn_averagedWaveCurrent (shift : α → Index d → ℝ)
    (hshift : Continuous shift) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) :
    ContDiffOn ℝ ∞
      (fun q : CurrentSpace d => averagedWaveCurrent μ shift κ cR cI v q.1 q.2)
      (currentNonzeroDomain d) := by
  have hc := OAI.Analysis.Calculus.Quaternion.contDiffOn_integral_translate isOpen_currentNonzeroDomain
    (waveField κ cR cI v) ((contDiffOn_waveField κ cR cI v).of_le le_top)
    (fun t => (shift t, (0 : Index d → ℂ))) (hshift.prodMk continuous_const)
    (fun q hq t => shiftedWave_mem shift q t hq) (μ := μ)
  simpa only [waveField, averagedWaveCurrent, Prod.fst_add, Prod.snd_add, add_zero] using! hc

theorem contDiffAt_averagedWaveCurrent (shift : α → Index d → ℝ)
    (hshift : Continuous shift) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (q : CurrentSpace d) (hq : q ∈ currentNonzeroDomain d) :
    ContDiffAt ℝ ∞
      (fun y : CurrentSpace d => averagedWaveCurrent μ shift κ cR cI v y.1 y.2) q :=
  (contDiffOn_averagedWaveCurrent μ shift hshift κ cR cI v q hq).contDiffAt
    (isOpen_currentNonzeroDomain.mem_nhds hq)

theorem contDiffAt_regularizedCurrent (shift : α → Index d → ℝ)
    (hshift : Continuous shift) (h a : ℝ) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (q : CurrentSpace d) (hq : q ∈ currentNonzeroDomain d) :
    ContDiffAt ℝ ∞
      (fun y : CurrentSpace d => regularizedCurrent μ shift h a κ cR cI v y.1 y.2) q := by
  have hφ : ContDiffAt ℝ ∞ (phi : (Index d → ℂ) → ℂ) q.2 :=
    (contDiffAt_phi_real q.2 hq).of_le le_top
  have hg : ContDiffAt ℝ ∞ (fun y : CurrentSpace d => phaseCutoff (phi y.2 / (a : ℂ))) q :=
    (phaseCutoff_contDiff.contDiffAt.comp q.2 (hφ.div_const (a : ℂ))).comp q contDiffAt_snd
  have hA := contDiffAt_averagedWaveCurrent μ shift hshift κ cR cI v q hq
  have hC : ContDiffAt ℝ ∞ (fun y : CurrentSpace d =>
      (fiberCofactor (1 / 10) a y.2 : Index d → Index d → OAI.Analysis.Calculus.Quaternion.Q)) q := by
    simpa only using! ((contDiffAt_fiberCofactor (1 / 10) a q.2 hq).of_le le_top).comp q
      contDiffAt_snd
  exact (hg.smul hA).add ((contDiffAt_const (c := h ^ (50 * (d + 1)))).smul hC)

theorem contDiffOn_regularizedCurrent (shift : α → Index d → ℝ)
    (hshift : Continuous shift) (h a : ℝ) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) :
    ContDiffOn ℝ ∞
      (fun y : CurrentSpace d => regularizedCurrent μ shift h a κ cR cI v y.1 y.2)
      (currentNonzeroDomain d) :=
  fun q hq => (contDiffAt_regularizedCurrent μ shift hshift h a κ cR cI v q hq).contDiffWithinAt

end OAI.Analysis.Calculus.Current
