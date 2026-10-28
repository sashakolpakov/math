import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Field

/-! # Root Ratio -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RootRatio.Frame

noncomputable section

/-! Continuous nonzero square-root frames with a constant determinant
ratio differ by the constant determined at any one base point. -/

theorem continuous_root_ratio_constant {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    (f g : X → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hf0 : ∀ x, f x ≠ 0) (hg0 : ∀ x, g x ≠ 0)
    (c : ℂ) (hsq : ∀ x, f x ^ 2 = c * g x ^ 2) (x₀ : X) :
    ∀ x, f x = (f x₀ / g x₀) * g x := by
  have hr : Continuous (fun x => f x / g x) := hf.div hg hg0
  have hs (x : X) : (f x / g x) ^ 2 = c := by
    rw [div_pow, hsq]
    exact mul_div_cancel_right₀ c (pow_ne_zero 2 (hg0 x))
  have he := isPreconnected_univ.eq_of_sq_eq hr.continuousOn
    (continuous_const.continuousOn : ContinuousOn (fun _ : X => f x₀ / g x₀) Set.univ)
    (fun x _ => (hs x).trans (hs x₀).symm)
    (fun _ => div_ne_zero (hf0 x₀) (hg0 x₀)) (Set.mem_univ x₀) rfl
  intro x
  exact (div_eq_iff (hg0 x)).mp (he (Set.mem_univ x))

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RootRatio.Frame
