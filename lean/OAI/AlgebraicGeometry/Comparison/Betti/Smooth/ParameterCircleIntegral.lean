import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.ParameterIntervalIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-! # Parameter Circle Integral -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Smooth.ParameterCircleIntegral.Dolbeault

noncomputable section

/-! The actual derivative of a contour integral with real parameters
is the contour integral of its actual parameter derivative. -/

open Set _root_.Metric _root_.Complex
open scoped Interval

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

theorem hasFDerivAt_parameter_circleIntegral
    {g : P → ℂ → F} {g' : P → ℂ → P →L[ℝ] F} {S : Set P}
    (hS : IsOpen S) {p : P} (hp : p ∈ S) {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hg : ContinuousOn (Function.uncurry g) (S ×ˢ sphere c r))
    (hg' : ContinuousOn (Function.uncurry g') (S ×ˢ sphere c r))
    (hD : ∀ q ∈ S, ∀ z ∈ sphere c r, HasFDerivAt (fun x => g x z) (g' q z) q) :
    HasFDerivAt (fun q => circleIntegral (g q) c r) (circleIntegral (g' p) c r) p := by
  let H : P → ℝ → F := fun q t => deriv (circleMap c r) t • g q (circleMap c r t)
  let H' : P → ℝ → P →L[ℝ] F := fun q t => deriv (circleMap c r) t • g' q (circleMap c r t)
  have hmap : Continuous (fun q : P × ℝ => (q.1, circleMap c r q.2)) :=
    continuous_fst.prodMk ((continuous_circleMap c r).comp continuous_snd)
  have hmaps : MapsTo (fun q : P × ℝ => (q.1, circleMap c r q.2))
      (S ×ˢ uIcc 0 (2 * Real.pi)) (S ×ˢ sphere c r) :=
    fun q hq => ⟨hq.1, circleMap_mem_sphere c hr q.2⟩
  have hder : Continuous (fun q : P × ℝ => deriv (circleMap c r) q.2) := by
    simp only [deriv_circleMap]
    exact ((continuous_circleMap 0 r).comp continuous_snd).mul_const I
  have hH : ContinuousOn (Function.uncurry H) (S ×ˢ uIcc 0 (2 * Real.pi)) :=
    hder.continuousOn.smul (hg.comp hmap.continuousOn hmaps)
  have hH' : ContinuousOn (Function.uncurry H') (S ×ˢ uIcc 0 (2 * Real.pi)) :=
    hder.continuousOn.smul (hg'.comp hmap.continuousOn hmaps)
  have hHD : ∀ q ∈ S, ∀ t ∈ uIcc 0 (2 * Real.pi),
      HasFDerivAt (fun x => H x t) (H' q t) q := by
    intro q hq t _
    exact (hD q hq _ (circleMap_mem_sphere c hr t)).const_smul (deriv (circleMap c r) t)
  have hF : @NormedSpace.complexToReal F _ _ = (inferInstance : NormedSpace ℝ F) :=
    NormedSpace.restrictScalars_eq (𝕜 := ℝ) (𝕜' := ℂ)
  have hDF : @NormedSpace.complexToReal (P →L[ℝ] F) _ _ =
      (inferInstance : NormedSpace ℝ (P →L[ℝ] F)) :=
    NormedSpace.restrictScalars_eq (𝕜 := ℝ) (𝕜' := ℂ)
  unfold circleIntegral
  rw [hF, hDF]
  exact ParameterIntervalIntegral.Dolbeault.hasFDerivAt_parameter_intervalIntegral hS hp hH hH' hHD

end

end OAI.AlgebraicGeometry.Comparison.Betti.Smooth.ParameterCircleIntegral.Dolbeault
