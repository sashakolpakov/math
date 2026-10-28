import OAI.Analysis.Calculus.Current.AverageCompact

/-! Conservation of the actual compactly averaged, cut off, regularized current. -/

noncomputable section
namespace OAI.Analysis.Calculus.Current

open _root_.MeasureTheory OAI.Analysis.Calculus.Quaternion
open scoped Matrix Matrix.Norms.Elementwise Topology ContDiff

private theorem fderiv_snd_value {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : F → G} (q : E × F) (hf : DifferentiableAt ℝ f q.2) :
    fderiv ℝ (fun y : E × F => f y.2) q =
      (fderiv ℝ f q.2).comp (ContinuousLinearMap.snd ℝ E F) := by
  simpa only using! (hf.hasFDerivAt.comp q (ContinuousLinearMap.snd ℝ E F).hasFDerivAt).fderiv

private theorem differentiableAt_add_smul_value {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : E → F} {q : E} (hf : DifferentiableAt ℝ f q)
    (hg : DifferentiableAt ℝ g q) (c : ℝ) :
    DifferentiableAt ℝ (fun y => f y + c • g y) q :=
  hf.add (hg.const_smul c)

private theorem fderiv_add_smul_value {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : E → F} {q : E} (hf : DifferentiableAt ℝ f q)
    (hg : DifferentiableAt ℝ g q) (c : ℝ) (v : E) :
    fderiv ℝ (fun y => f y + c • g y) q v =
      fderiv ℝ f q v + c • fderiv ℝ g q v := by
  simpa only [add_apply, smul_apply] using!
    congrArg (fun L => L v) (hf.hasFDerivAt.add (hg.hasFDerivAt.const_smul c)).fderiv

variable {d : ℕ} {ι α : Type*} [Fintype ι]

local instance : NormedAddCommGroup (Matrix (Index d) (Index d) OAI.Analysis.Calculus.Quaternion.Q) :=
  inferInstanceAs (NormedAddCommGroup (Index d → Index d → OAI.Analysis.Calculus.Quaternion.Q))

local instance : NormedSpace ℝ (Matrix (Index d) (Index d) OAI.Analysis.Calculus.Quaternion.Q) :=
  inferInstanceAs (NormedSpace ℝ (Index d → Index d → OAI.Analysis.Calculus.Quaternion.Q))

local instance : ContinuousSMul ℝ (Matrix (Index d) (Index d) OAI.Analysis.Calculus.Quaternion.Q) :=
  inferInstanceAs (ContinuousSMul ℝ (Index d → Index d → OAI.Analysis.Calculus.Quaternion.Q))

local instance : ContinuousConstSMul ℝ (Matrix (Index d) (Index d) OAI.Analysis.Calculus.Quaternion.Q) :=
  inferInstanceAs (ContinuousConstSMul ℝ (Index d → Index d → OAI.Analysis.Calculus.Quaternion.Q))

theorem differentiableAt_cutoffCurrent (g : ℂ → ℝ) (a : ℝ)
    (A : (Index d → ℝ) → (Index d → ℂ) → Matrix (Index d) (Index d) OAI.Analysis.Calculus.Quaternion.Q)
    (q : CurrentSpace d) (hq : q ∈ currentNonzeroDomain d)
    (hg : DifferentiableAt ℝ g (phi q.2 / (a : ℂ)))
    (hA : DifferentiableAt ℝ (fun y : CurrentSpace d => A y.1 y.2) q) :
    DifferentiableAt ℝ (fun y : CurrentSpace d => cutoffCurrent g a A y.1 y.2) q := by
  have hφ := (differentiableAt_phi q.2 hq).restrictScalars ℝ
  have hscale : DifferentiableAt ℝ (fun z : ℂ => z / (a : ℂ)) (phi q.2) := by fun_prop
  have hgs : DifferentiableAt ℝ (fun z : Index d → ℂ => g (phi z / (a : ℂ))) q.2 :=
    hg.comp q.2 (hscale.comp q.2 hφ)
  exact (hgs.comp q differentiableAt_snd).smul hA

theorem differentiableAt_fiberCofactor_field (w a : ℝ) (q : CurrentSpace d)
    (hq : q ∈ currentNonzeroDomain d) :
    DifferentiableAt ℝ (fun y : CurrentSpace d => fiberCofactor w a y.2) q :=
  ((contDiffAt_fiberCofactor w a q.2 hq).differentiableAt (by simp)).comp q
    differentiableAt_snd

theorem fiberCofactor_field_divergence_zero (w a : ℝ) (q : CurrentSpace d)
    (hq : q ∈ currentNonzeroDomain d) (b : Index d) :
    OAI.Analysis.Calculus.Quaternion.strongDivergence OAI.Analysis.Calculus.Quaternion.threeSlots (fun p =>
      fderiv ℝ (fun y : CurrentSpace d => fiberCofactor w a y.2) q
        (currentDirection p)) b = 0 := by
  have hC := (contDiffAt_fiberCofactor w a q.2 hq).differentiableAt (by simp)
  change DifferentiableAt ℝ (fun z : Index d → ℂ =>
    (fiberCofactor w a z : Index d → Index d → OAI.Analysis.Calculus.Quaternion.Q)) q.2 at hC
  have hF : fderiv ℝ (fun y : CurrentSpace d => fiberCofactor w a y.2) q =
      (fderiv ℝ (fiberCofactor w a) q.2).comp
        (ContinuousLinearMap.snd ℝ (Index d → ℝ) (Index d → ℂ)) := by
    simpa only using! fderiv_snd_value q hC
  simp only [hF, ContinuousLinearMap.comp_apply]
  change OAI.Analysis.Calculus.Quaternion.strongDivergence OAI.Analysis.Calculus.Quaternion.threeSlots (fun p =>
    fderiv ℝ (fiberCofactor w a) q.2 ((currentDirection p).2)) b = 0
  simp only [currentDirection_snd]
  exact fiberCofactor_divergence_zero w a q.2 hq b

section Compact
variable [TopologicalSpace α] [CompactSpace α] [T2Space α] [SecondCountableTopology α]
  [MeasurableSpace α] [BorelSpace α] (μ : Measure α) [IsFiniteMeasure μ]

theorem cutoff_averagedWaveCurrent_divergence_zero (shift : α → Index d → ℝ)
    (hshift : Continuous shift) (g : ℂ → ℝ) (a : ℝ)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (q : CurrentSpace d)
    (hq : q ∈ currentNonzeroDomain d)
    (hg : DifferentiableAt ℝ g (phi q.2 / (a : ℂ))) (b : Index d) :
    OAI.Analysis.Calculus.Quaternion.strongDivergence OAI.Analysis.Calculus.Quaternion.threeSlots (fun p => fderiv ℝ
      (fun y : CurrentSpace d =>
        cutoffCurrent g a (averagedWaveCurrent μ shift κ cR cI v) y.1 y.2) q
      (currentDirection p)) b = 0 := by
  have hA := differentiableAt_averagedWaveCurrent μ shift hshift κ cR cI v q hq
  have hcut := differentiableAt_cutoffCurrent g a _ q hq hg hA
  have hdiv : ∀ b, OAI.Analysis.Calculus.Quaternion.strongDivergence OAI.Analysis.Calculus.Quaternion.threeSlots
      (threeSlotMatrixDerivative (averagedWaveCurrent μ shift κ cR cI v) q.1 q.2) b = 0 := by
    intro j
    simpa only [fderiv_currentDirection hA] using
      averagedWaveCurrent_divergence_zero μ shift hshift κ cR cI v q hq j
  have htan : ∀ b, ∑ c, complexK (phaseRow (ratio q.2) c) *
      averagedWaveCurrent μ shift κ cR cI v q.1 q.2 c b = 0 := by
    intro j
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using
      averagedWaveCurrent_tangent μ shift κ cR cI v q.1 q.2
        (integrable_waveCurrent_translate μ shift hshift κ cR cI v q.1 q.2 hq)
        (Pi.single j 1)
  simpa only [fderiv_currentDirection hcut] using
    cutoffCurrent_divergence_zero g a hq hg hA htan hdiv b

theorem differentiableAt_regularizedCurrent (shift : α → Index d → ℝ)
    (hshift : Continuous shift) (h a : ℝ) (κ cR cI : ι → ℝ)
    (v : ι → Fin d → ℝ) (q : CurrentSpace d) (hq : q ∈ currentNonzeroDomain d) :
    DifferentiableAt ℝ
      (fun y : CurrentSpace d => regularizedCurrent μ shift h a κ cR cI v y.1 y.2) q := by
  have hA := differentiableAt_averagedWaveCurrent μ shift hshift κ cR cI v q hq
  have hg := phaseCutoff_contDiff.differentiable (by simp) (phi q.2 / (a : ℂ))
  have hC := differentiableAt_fiberCofactor_field (1 / 10) a q hq
  change DifferentiableAt ℝ (fun y : CurrentSpace d =>
    (fiberCofactor (1 / 10) a y.2 : Index d → Index d → OAI.Analysis.Calculus.Quaternion.Q)) q at hC
  simpa only using! differentiableAt_add_smul_value
    (differentiableAt_cutoffCurrent phaseCutoff a _ q hq hg hA) hC (h ^ (50 * (d + 1)))

/-- The divergence vanishes for the defined regularized current, with no
    conservation, tangency, or differentiation-under-integral premise. -/
theorem regularizedCurrent_divergence_zero (shift : α → Index d → ℝ)
    (hshift : Continuous shift) (h a : ℝ) (κ cR cI : ι → ℝ)
    (v : ι → Fin d → ℝ) (q : CurrentSpace d) (hq : q ∈ currentNonzeroDomain d)
    (b : Index d) :
    OAI.Analysis.Calculus.Quaternion.strongDivergence OAI.Analysis.Calculus.Quaternion.threeSlots (fun p => fderiv ℝ
      (fun y : CurrentSpace d => regularizedCurrent μ shift h a κ cR cI v y.1 y.2) q
      (currentDirection p)) b = 0 := by
  have hA := differentiableAt_averagedWaveCurrent μ shift hshift κ cR cI v q hq
  have hg := phaseCutoff_contDiff.differentiable (by simp) (phi q.2 / (a : ℂ))
  have hcut := differentiableAt_cutoffCurrent phaseCutoff a _ q hq hg hA
  have hC := differentiableAt_fiberCofactor_field (1 / 10) a q hq
  change DifferentiableAt ℝ (fun y : CurrentSpace d =>
    (fiberCofactor (1 / 10) a y.2 : Index d → Index d → OAI.Analysis.Calculus.Quaternion.Q)) q at hC
  change DifferentiableAt ℝ (fun y : CurrentSpace d =>
    (cutoffCurrent phaseCutoff a (averagedWaveCurrent μ shift κ cR cI v) y.1 y.2 :
      Index d → Index d → OAI.Analysis.Calculus.Quaternion.Q)) q at hcut
  have hF (p : Index d × Fin 3) : fderiv ℝ
      (fun y : CurrentSpace d => regularizedCurrent μ shift h a κ cR cI v y.1 y.2) q
        (currentDirection p) =
      fderiv ℝ (fun y : CurrentSpace d => cutoffCurrent phaseCutoff a
        (averagedWaveCurrent μ shift κ cR cI v) y.1 y.2) q (currentDirection p) +
      h ^ (50 * (d + 1)) • fderiv ℝ
        (fun y : CurrentSpace d => fiberCofactor (1 / 10) a y.2) q (currentDirection p) := by
    simpa only using! fderiv_add_smul_value hcut hC (h ^ (50 * (d + 1))) (currentDirection p)
  simp only [hF, OAI.Analysis.Calculus.Quaternion.strongDivergence_add, OAI.Analysis.Calculus.Quaternion.strongDivergence_smul,
    cutoff_averagedWaveCurrent_divergence_zero μ shift hshift phaseCutoff a κ cR cI v q hq hg b,
    fiberCofactor_field_divergence_zero (1 / 10) a q hq b, smul_zero, add_zero]

end Compact
end OAI.Analysis.Calculus.Current
