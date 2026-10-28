import Mathlib.Analysis.Complex.CauchyIntegral

/-! # Circle Integral Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.CircleIntegralNaturality.Dolbeault

noncomputable section

/-! Continuous complex-linear maps commute with the actual contour
integral. This includes evaluation of Banach-valued compact families. -/

open _root_.MeasureTheory _root_.Complex

variable {F G : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

theorem circleIntegral_map (L : F →L[ℂ] G) {g : ℂ → F} {c : ℂ} {r : ℝ}
    (hg : CircleIntegrable g c r) :
    L (circleIntegral g c r) = circleIntegral (fun z => L (g z)) c r := by
  let : NormedSpace ℝ G := NormedSpace.restrictScalars ℝ ℂ G
  unfold circleIntegral
  rw [← L.intervalIntegral_comp_comm hg.out]
  apply intervalIntegral.integral_congr
  intro θ hθ
  exact L.map_smul (deriv (circleMap c r) θ) (g (circleMap c r θ))

end

end OAI.AlgebraicGeometry.Comparison.Betti.CircleIntegralNaturality.Dolbeault
