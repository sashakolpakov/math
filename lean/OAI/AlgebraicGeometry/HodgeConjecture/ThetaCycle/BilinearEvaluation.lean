import Mathlib

/-! # Bilinear Evaluation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BilinearEvaluation.CM

noncomputable section

/-! Smooth evaluation of a varying bilinear tensor on two varying slots. -/

open scoped ContDiff

theorem bilinear_evaluation_smoothAt
    {𝕜 E V G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {f : E → V [×2]→L[𝕜] G} {u v : E → V} {x : E}
    (hf : ContDiffAt 𝕜 ∞ f x) (hu : ContDiffAt 𝕜 ∞ u x) (hv : ContDiffAt 𝕜 ∞ v x) :
    ContDiffAt 𝕜 ∞ (fun y => f y ![u y, v y]) x := by
  let C : (V [×2]→L[𝕜] G) →L[𝕜] V →L[𝕜] V [×1]→L[𝕜] G :=
    continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin 2 => V) G
  let D : (V [×1]→L[𝕜] G) →L[𝕜] V →L[𝕜] G := continuousMultilinearCurryFin1 𝕜 V G
  have hcraw := hf.continuousLinearMap_comp (G := V →L[𝕜] V [×1]→L[𝕜] G) C
  have hc : ContDiffAt 𝕜 ∞ (fun y => (f y).curryLeft) x := by
    simpa only [C, Function.comp_def] using! hcraw
  have h₁ : ContDiffAt 𝕜 ∞ (fun y => (f y).curryLeft (u y)) x := hc.clm_apply hu
  have hd : ContDiffAt 𝕜 ∞
      (fun y => continuousMultilinearCurryFin1 𝕜 V G ((f y).curryLeft (u y))) x := by
    simpa only [D, Function.comp_def] using!
      h₁.continuousLinearMap_comp (G := V →L[𝕜] G) D
  have h₂ := hd.clm_apply hv
  convert h₂ using 1
  funext y
  simp only [continuousMultilinearCurryFin1_apply, ContinuousMultilinearMap.curryLeft_apply]
  congr 1
  ext i
  fin_cases i <;> rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BilinearEvaluation.CM
