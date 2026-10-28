import OAI.AlgebraicGeometry.Comparison.Betti.Open.AntiholomorphicContraction
import OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.LinearOpenPullback

/-! # Contraction Pullback -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.ContractionPullback.Dolbeault

noncomputable section

/-! The actual antiholomorphic contraction commutes with open-domain
pullback by complex-linear maps. -/

open _root_.TopologicalSpace Set

variable {E F : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  {U : Opens E} {V : Opens F}

theorem openAntiContraction_pullback (n : ℕ) (v : E) (L : E →L[ℂ] F)
    (hL : MapsTo L (U : Set E) (V : Set F)) (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm V (n + 1)) :
    AntiholomorphicContraction.Dolbeault.openAntiContraction U n v (DivisorClass.Chern.Complex.LinearOpenPullback.complexLinearOpenPullback L hL a) =
      DivisorClass.Chern.Complex.LinearOpenPullback.complexLinearOpenPullback L hL (AntiholomorphicContraction.Dolbeault.openAntiContraction V n (L v) a) := by
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro x
  rw [AntiholomorphicContraction.Dolbeault.openAntiContraction_apply, DivisorClass.Chern.Complex.LinearOpenPullback.complexLinearOpenPullback_apply,
    AntiholomorphicContractionPurity.Dolbeault.antiContraction_pullback, DivisorClass.Chern.Complex.LinearOpenPullback.complexLinearOpenPullback_apply, AntiholomorphicContraction.Dolbeault.openAntiContraction_apply]

theorem openAntiContraction_pullback_zero (n : ℕ) (v : E) (L : E →L[ℂ] F)
    (hL : MapsTo L (U : Set E) (V : Set F)) (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm V (n + 1))
    (ha : AntiholomorphicContraction.Dolbeault.openAntiContraction V n (L v) a = 0) :
    AntiholomorphicContraction.Dolbeault.openAntiContraction U n v (DivisorClass.Chern.Complex.LinearOpenPullback.complexLinearOpenPullback L hL a) = 0 := by
  rw [openAntiContraction_pullback, ha, map_zero]

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.ContractionPullback.Dolbeault
