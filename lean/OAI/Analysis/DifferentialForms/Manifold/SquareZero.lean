import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Complex.Basic

/-! # Square Zero -/

namespace OAI.Analysis.DifferentialForms.Manifold.SquareZero

/-! Square-zero for actual smooth complex-valued real differential forms.

These local analytic lemmas discharge the regularity conditions in mathlib's
exterior-derivative theorem. They apply both to global forms on a real normed
space and to chart domains, without a finite-dimensionality assumption.
-/

open scoped ContDiff

theorem minSmoothness_real_two_le_infty : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ} {form : E → E [⋀^Fin n]→L[ℝ] ℂ}

theorem extDeriv_extDeriv_of_contDiffAt {x : E} (hω : ContDiffAt ℝ ∞ form x) :
    extDeriv (extDeriv form) x = 0 := by
  exact _root_.extDeriv_extDeriv_apply hω minSmoothness_real_two_le_infty

theorem extDeriv_extDeriv_of_contDiff (hω : ContDiff ℝ ∞ form) :
    extDeriv (extDeriv form) = 0 := by
  exact _root_.extDeriv_extDeriv hω minSmoothness_real_two_le_infty

theorem extDerivWithin_extDerivWithin_of_contDiffOn
    {s : Set E} (hs : IsOpen s) (hω : ContDiffOn ℝ ∞ form s)
    {x : E} (hx : x ∈ s) :
    extDerivWithin (extDerivWithin form s) s x = 0 := by
  apply _root_.extDerivWithin_extDerivWithin_apply
    (hω.contDiffWithinAt hx) minSmoothness_real_two_le_infty hs.uniqueDiffOn
  · apply subset_closure
    simpa only [hs.interior_eq] using hx
  · exact hx

end OAI.Analysis.DifferentialForms.Manifold.SquareZero
