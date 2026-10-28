import OAI.AlgebraicGeometry.Comparison.Betti.ParametricVectorCauchy

/-! # Vector Cauchy Cutoff -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.VectorCauchyCutoff.Dolbeault

noncomputable section

/-! A scalar cutoff localizes vector-valued Cauchy input and preserves
its actual parameter derivatives. -/

open Set Filter
open scoped ContDiff _root_.Topology

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def cutoffVectorCauchyInput (χ : ℂ → ℝ) (g : P → ℂ → F) (p : P) (w : ℂ) : F :=
  χ w • g p w

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem cutoffVectorCauchyInput_support (χ : ℂ → ℝ) (g : P → ℂ → F) (p : P) (w : ℂ)
    (hw : w ∉ tsupport χ) : cutoffVectorCauchyInput χ g p w = 0 := by
  unfold cutoffVectorCauchyInput
  rw [image_eq_zero_of_notMem_tsupport hw, zero_smul]

theorem cutoffVectorCauchyInput_smooth {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {g : P → ℂ → F} {S : Set P} {U : Set ℂ} (hS : IsOpen S) (hU : IsOpen U)
    (hsub : tsupport χ ⊆ U) (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (S ×ˢ U)) :
    ContDiffOn ℝ ∞ (Function.uncurry (cutoffVectorCauchyInput χ g)) (S ×ˢ univ) := by
  intro q hq
  apply ContDiffAt.contDiffWithinAt
  by_cases hw : q.2 ∈ tsupport χ
  · exact (hχ.comp contDiff_snd).contDiffAt.smul
      (hg.contDiffAt ((hS.prod hU).mem_nhds ⟨hq.1, hsub hw⟩))
  · apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
    filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hw).comp_tendsto
      continuous_snd.continuousAt] with t ht
    change χ t.2 • g t.1 t.2 = 0
    rw [show χ t.2 = 0 from ht, zero_smul]

theorem cutoffVectorCauchyInput_parameterDerivative {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {g : P → ℂ → F} {S : Set P} {U : Set ℂ} (hS : IsOpen S) (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (S ×ˢ U))
    {p : P} (hp : p ∈ S) {w : ℂ} (hw : w ∈ U) (v : P) :
    fderiv ℝ (Function.uncurry (cutoffVectorCauchyInput χ g)) (p, w) (v, 0) =
      χ w • fderiv ℝ (Function.uncurry g) (p, w) (v, 0) := by
  have hcoeff := (hχ.differentiable (by simp) w).hasFDerivAt.comp (p, w)
    (hasFDerivAt_snd (𝕜 := ℝ) (p := (p, w)))
  have hinput : DifferentiableAt ℝ (Function.uncurry g) (p, w) :=
    (hg.contDiffAt ((hS.prod hU).mem_nhds ⟨hp, hw⟩)).differentiableAt (by simp)
  have hd := congrArg (fun D : (P × ℂ) →L[ℝ] F => D (v, 0))
    (hcoeff.smul hinput.hasFDerivAt).fderiv
  change fderiv ℝ (Function.uncurry (cutoffVectorCauchyInput χ g)) (p, w) (v, 0) =
    χ w • fderiv ℝ (Function.uncurry g) (p, w) (v, 0) +
      fderiv ℝ χ w 0 • g p w at hd
  simpa only [map_zero, zero_smul, add_zero] using hd

theorem cutoffVectorCauchyInput_fderiv_zero {χ : ℂ → ℝ} {g : P → ℂ → F}
    {p : P} {w : ℂ} (hw : w ∉ tsupport χ) :
    fderiv ℝ (Function.uncurry (cutoffVectorCauchyInput χ g)) (p, w) = 0 := by
  have he : Function.uncurry (cutoffVectorCauchyInput χ g) =ᶠ[𝓝 (p, w)] 0 := by
    filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hw).comp_tendsto
      continuous_snd.continuousAt] with q hq
    change χ q.2 • g q.1 q.2 = 0
    rw [show χ q.2 = 0 from hq, zero_smul]
  rw [he.fderiv_eq]
  exact (hasFDerivAt_const (0 : F) (p, w)).fderiv

end

end OAI.AlgebraicGeometry.Comparison.Betti.VectorCauchyCutoff.Dolbeault
