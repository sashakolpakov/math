import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-! # Hilbert Coercive Energy Bound -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HilbertCoerciveEnergyBound

/-! The original coercive energy identity bounds each energy component by the source norm. -/

theorem hilbert_coercive_energy_component_bound
    {H P Q : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup P] [InnerProductSpace ℂ P]
    [NormedAddCommGroup Q] [InnerProductSpace ℂ Q]
    (v f : H) (p : P) (q : Q)
    (hc : ‖v‖ ^ 2 ≤ ‖p‖ ^ 2 + ‖q‖ ^ 2)
    (he : inner ℂ v f = inner ℂ p p + inner ℂ q q) : ‖q‖ ≤ ‖f‖ := by
  have he' : (inner ℂ v f).re = ‖p‖ ^ 2 + ‖q‖ ^ 2 :=
    (congrArg Complex.re he).trans ((Complex.add_re _ _).trans
      (congrArg₂ (fun x y : ℝ => x + y)
        (inner_self_eq_norm_sq (𝕜 := ℂ) p) (inner_self_eq_norm_sq (𝕜 := ℂ) q)))
  have hcs := (Complex.re_le_norm (inner ℂ v f)).trans (norm_inner_le_norm v f)
  have hv : ‖v‖ ≤ ‖f‖ := by
    nlinarith only [hc, he', hcs, norm_nonneg v, norm_nonneg f]
  have hm := mul_le_mul_of_nonneg_right hv (norm_nonneg f)
  nlinarith only [he', hcs, hm, sq_nonneg ‖p‖, norm_nonneg q, norm_nonneg f]

end OAI.AlgebraicGeometry.DivisorClass.Chern.HilbertCoerciveEnergyBound
