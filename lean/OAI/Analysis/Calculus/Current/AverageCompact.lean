import OAI.Analysis.Calculus.Current.Regularized
import OAI.Analysis.Calculus.Quaternion.CompactAverage

/-! Actual averaging of the finite wave current over compact spatial translations. -/

noncomputable section
namespace OAI.Analysis.Calculus.Current

open _root_.MeasureTheory OAI.Analysis.Calculus.Quaternion
open scoped Matrix Matrix.Norms.Elementwise Topology

variable {d : ℕ} {ι α : Type*} [Fintype ι]

def waveField (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (q : CurrentSpace d) :
    Matrix (Index d) (Index d) (Quaternion ℝ) := waveCurrent κ cR cI v q.1 q.2

def currentNonzeroDomain (d : ℕ) : Set (CurrentSpace d) := {q | q.2 none ≠ 0}

theorem isOpen_currentNonzeroDomain : IsOpen (currentNonzeroDomain d) :=
  isOpen_ne.preimage ((continuous_apply none).comp continuous_snd)

theorem contDiffAt_waveField (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (q : CurrentSpace d) (hq : q ∈ currentNonzeroDomain d) :
    ContDiffAt ℝ ⊤ (waveField κ cR cI v) q := by
  apply contDiffAt_pi.mpr
  intro a
  apply contDiffAt_pi.mpr
  intro b
  exact contDiffAt_waveCurrent κ cR cI v q.1 q.2 hq a b

theorem contDiffOn_waveField (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) :
    ContDiffOn ℝ ⊤ (waveField κ cR cI v) (currentNonzeroDomain d) :=
  fun q hq => (contDiffAt_waveField κ cR cI v q hq).contDiffWithinAt

theorem waveField_divergence_zero (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (q : CurrentSpace d) (hq : q ∈ currentNonzeroDomain d) (b : Index d) :
    OAI.Analysis.Calculus.Quaternion.strongDivergence OAI.Analysis.Calculus.Quaternion.threeSlots
      (fun p => fderiv ℝ (waveField κ cR cI v) q (currentDirection p)) b = 0 := by
  have hd := (contDiffAt_waveField κ cR cI v q hq).differentiableAt (by simp)
  change OAI.Analysis.Calculus.Quaternion.strongDivergence OAI.Analysis.Calculus.Quaternion.threeSlots
    (fun p => fderiv ℝ (fun y : CurrentSpace d => waveCurrent κ cR cI v y.1 y.2)
      (q.1, q.2) (currentDirection p)) b = 0
  simp_rw [fderiv_currentDirection hd]
  exact waveCurrent_strongDivergence κ cR cI v q.1 q.2 hq b

def shiftedWave (shift : α → Index d → ℝ) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (q : CurrentSpace d) (t : α) : Matrix (Index d) (Index d) (Quaternion ℝ) :=
  waveField κ cR cI v (q + (shift t, 0))

theorem shiftedWave_mem (shift : α → Index d → ℝ) (q : CurrentSpace d) (t : α)
    (hq : q ∈ currentNonzeroDomain d) : q + (shift t, 0) ∈ currentNonzeroDomain d := by
  simpa [currentNonzeroDomain] using hq

theorem hasFDerivAt_shiftedWave (shift : α → Index d → ℝ)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (q : CurrentSpace d) (t : α)
    (hq : q ∈ currentNonzeroDomain d) :
    HasFDerivAt (fun y => shiftedWave shift κ cR cI v y t)
      (fderiv ℝ (waveField κ cR cI v) (q + (shift t, 0))) q := by
  have hf := (contDiffAt_waveField κ cR cI v _ (shiftedWave_mem shift q t hq)).differentiableAt
    (by simp)
  simpa only [ContinuousLinearMap.comp_id] using!
    hf.hasFDerivAt.comp q ((hasFDerivAt_id q).add_const (shift t, 0))

theorem fderiv_shiftedWave (shift : α → Index d → ℝ)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (q : CurrentSpace d) (t : α)
    (hq : q ∈ currentNonzeroDomain d) :
    fderiv ℝ (fun y => shiftedWave shift κ cR cI v y t) q =
      fderiv ℝ (waveField κ cR cI v) (q + (shift t, 0)) := by
  simpa only using! (hasFDerivAt_shiftedWave shift κ cR cI v q t hq).fderiv

section Compact
variable [TopologicalSpace α] [CompactSpace α] [T2Space α] [SecondCountableTopology α]
  [MeasurableSpace α] [BorelSpace α] (μ : Measure α) [IsFiniteMeasure μ]

local instance : ContinuousENorm (Matrix (Index d) (Index d) (Quaternion ℝ)) :=
  inferInstanceAs (ContinuousENorm (Index d → Index d → Quaternion ℝ))

omit [CompactSpace α] [T2Space α] [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α] in
theorem continuousOn_shiftedWave (shift : α → Index d → ℝ) (hshift : Continuous shift)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) :
    ContinuousOn (Function.uncurry (shiftedWave shift κ cR cI v))
      (currentNonzeroDomain d ×ˢ Set.univ) := by
  exact (contDiffOn_waveField κ cR cI v).continuousOn.comp
    (continuous_fst.add ((hshift.comp continuous_snd).prodMk continuous_const)).continuousOn
    (fun p hp => shiftedWave_mem shift p.1 p.2 hp.1)

omit [CompactSpace α] [T2Space α] [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α] in
theorem continuousOn_fderiv_shiftedWave (shift : α → Index d → ℝ) (hshift : Continuous shift)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) :
    ContinuousOn (fun p : CurrentSpace d × α =>
      fderiv ℝ (fun y => shiftedWave shift κ cR cI v y p.2) p.1)
      (currentNonzeroDomain d ×ˢ Set.univ) := by
  have hc : ContinuousOn (fun p : CurrentSpace d × α =>
      fderiv ℝ (waveField κ cR cI v) (p.1 + (shift p.2, 0)))
      (currentNonzeroDomain d ×ˢ Set.univ) :=
    ((contDiffOn_waveField κ cR cI v).continuousOn_fderiv_of_isOpen
    isOpen_currentNonzeroDomain (by simp)).comp
      (continuous_fst.add ((hshift.comp continuous_snd).prodMk continuous_const)).continuousOn
        (fun p hp => shiftedWave_mem shift p.1 p.2 hp.1)
  apply hc.congr
  intro p hp
  exact fderiv_shiftedWave shift κ cR cI v p.1 p.2 hp.1

theorem integrable_shiftedWave (shift : α → Index d → ℝ) (hshift : Continuous shift)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (q : CurrentSpace d)
    (hq : q ∈ currentNonzeroDomain d) : Integrable (shiftedWave shift κ cR cI v q) μ := by
  have hc := OAI.Analysis.Calculus.Quaternion.continuous_section_of_continuousOn _ (continuousOn_shiftedWave shift hshift κ cR cI v) hq
  simpa only [IntegrableOn, Measure.restrict_univ] using!
    hc.continuousOn.integrableOn_compact (μ := μ) isCompact_univ

theorem integrable_waveCurrent_translate (shift : α → Index d → ℝ) (hshift : Continuous shift)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (x : Index d → ℝ) (z : Index d → ℂ)
    (hY : z none ≠ 0) : Integrable (fun t => waveCurrent κ cR cI v (x + shift t) z) μ := by
  have hh := integrable_shiftedWave μ shift hshift κ cR cI v (x, z) hY
  have he : shiftedWave shift κ cR cI v (x, z) =
      (fun t => waveCurrent κ cR cI v (x + shift t) z) := by
    funext t
    simp [shiftedWave, waveField]
  rw [he] at hh
  exact hh

theorem differentiableAt_averagedWaveCurrent (shift : α → Index d → ℝ)
    (hshift : Continuous shift) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (q : CurrentSpace d) (hq : q ∈ currentNonzeroDomain d) :
    DifferentiableAt ℝ (fun y : CurrentSpace d => averagedWaveCurrent μ shift κ cR cI v y.1 y.2) q := by
  have hd := OAI.Analysis.Calculus.Quaternion.hasFDerivAt_integral_compact isOpen_currentNonzeroDomain
    (shiftedWave shift κ cR cI v) hq
    (continuousOn_shiftedWave shift hshift κ cR cI v)
    (continuousOn_fderiv_shiftedWave shift hshift κ cR cI v)
    (fun y hy t => (hasFDerivAt_shiftedWave shift κ cR cI v y t hy).differentiableAt)
    (μ := μ)
  simpa only [shiftedWave, waveField, averagedWaveCurrent, Prod.fst_add, Prod.snd_add,
    add_zero] using! hd.differentiableAt

theorem averagedWaveCurrent_divergence_zero (shift : α → Index d → ℝ)
    (hshift : Continuous shift) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (q : CurrentSpace d) (hq : q ∈ currentNonzeroDomain d) (b : Index d) :
    OAI.Analysis.Calculus.Quaternion.strongDivergence OAI.Analysis.Calculus.Quaternion.threeSlots (fun p =>
      fderiv ℝ (fun y : CurrentSpace d => averagedWaveCurrent μ shift κ cR cI v y.1 y.2)
        q (currentDirection p)) b = 0 := by
  have hz : ∀ᵐ t ∂μ, OAI.Analysis.Calculus.Quaternion.currentDivergenceCLM OAI.Analysis.Calculus.Quaternion.threeSlots (currentDirection (d := d)) b
      (fderiv ℝ (fun y => shiftedWave shift κ cR cI v y t) q) = 0 := by
    apply Filter.Eventually.of_forall
    intro t
    rw [fderiv_shiftedWave shift κ cR cI v q t hq]
    exact waveField_divergence_zero κ cR cI v _ (shiftedWave_mem shift q t hq) b
  have hc := OAI.Analysis.Calculus.Quaternion.integral_fderiv_linear_zero_compact isOpen_currentNonzeroDomain
    (shiftedWave shift κ cR cI v) hq
    (continuousOn_shiftedWave shift hshift κ cR cI v)
    (continuousOn_fderiv_shiftedWave shift hshift κ cR cI v)
    (fun y hy t => (hasFDerivAt_shiftedWave shift κ cR cI v y t hy).differentiableAt)
    (OAI.Analysis.Calculus.Quaternion.currentDivergenceCLM OAI.Analysis.Calculus.Quaternion.threeSlots (currentDirection (d := d)) b) hz
  have he : (fun y => ∫ t, shiftedWave shift κ cR cI v y t ∂μ) =
      (fun y : CurrentSpace d => averagedWaveCurrent μ shift κ cR cI v y.1 y.2) := by
    funext y
    simp only [shiftedWave, waveField, averagedWaveCurrent, Prod.fst_add, Prod.snd_add, add_zero]
  rw [he] at hc
  exact hc

end Compact
end OAI.Analysis.Calculus.Current
