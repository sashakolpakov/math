import OAI.Analysis.PDE.Schauder.Dirichlet.HalfspaceLowerInterpolation
import OAI.Analysis.PDE.Schauder.Calculus.Boundary.HolderExtension

open Set InnerProductSpace
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

variable {m : ℕ} {α : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local instance jetExtensionFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance jetExtensionFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance

/-- Coordinate form of the norm-controlled folding extension. -/
theorem exists_coordinate_halfspace_holder_extension
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (k : Fin m) (f : E → F) (hf : Continuous f) {H M : ℝ}
    (hα : 0 ≤ α) (hH : 0 ≤ H) (hM : 0 ≤ M)
    (hbound : ∀ x, 0 ≤ x k → ‖f x‖ ≤ M)
    (hh : ∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k →
      ‖f x - f y‖ ≤ H * ‖x-y‖ ^ α) :
    ∃ A : OAI.Analysis.Normed.Function.Holder.HolderMap E F α,
      (∀ x, 0 ≤ x k → OAI.Analysis.Normed.Function.Holder.HolderMap.value A x = f x) ∧ ‖A‖ ≤ max M H := by
  have hn : ‖(EuclideanSpace.single k 1 : E)‖ = 1 := by simp
  obtain ⟨A, hA, hnorm⟩ := exists_bounded_halfspace_holder_extension
    (EuclideanSpace.single k 1) hn f hf hα hH hM
    (by simpa only [EuclideanSpace.inner_single_left, map_one, one_mul] using hbound)
    (by simpa only [EuclideanSpace.inner_single_left, map_one, one_mul] using hh)
  refine ⟨A, ?_, hnorm⟩
  simpa only [EuclideanSpace.inner_single_left, map_one, one_mul] using hA

/-- The actual lower jets on a halfspace have global Hölder extensions with
arbitrarily small dependence on the top-order seminorm. Their behavior on
the opposite halfspace is constructed, not assumed. -/
theorem halfspace_lower_jet_holder_extensions (k : Fin m)
    (hα : 0 < α) (hα1 : α ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ B > 0, ∀ (u : E → ℝ), ContDiff ℝ 2 u → HasCompactSupport u →
      ∀ H M, 0 ≤ H → 0 ≤ M → (∀ x, 0 ≤ x k → |u x| ≤ M) →
      (∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k →
        ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ H * ‖x-y‖ ^ α) →
      ∃ (U : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α) (V : OAI.Analysis.Normed.Function.Holder.HolderMap E (E →L[ℝ] ℝ) α),
        (∀ x, 0 ≤ x k → OAI.Analysis.Normed.Function.Holder.HolderMap.value U x = u x) ∧
        (∀ x, 0 ≤ x k → OAI.Analysis.Normed.Function.Holder.HolderMap.value V x = fderiv ℝ u x) ∧
        ‖U‖ ≤ ε * H + B * M ∧ ‖V‖ ≤ ε * H + B * M := by
  obtain ⟨B₀, hB₀, hinterp⟩ := halfspace_lower_jet_interpolation k hα hα1 hε
  refine ⟨B₀ + 1, by positivity, ?_⟩
  intro u hu huc H M hH hM hbound hh
  obtain ⟨_, hgrad, hvalue, hfirst⟩ := hinterp u hu huc H M hH hM hbound hh
  let D := ε * H + B₀ * M
  have hD : 0 ≤ D := by dsimp [D]; positivity
  obtain ⟨U, hU, hUn⟩ := exists_coordinate_halfspace_holder_extension k u hu.continuous
    hα.le hD hM (by simpa only [Real.norm_eq_abs] using hbound)
    (by simpa only [Real.norm_eq_abs] using hvalue)
  obtain ⟨V, hV, hVn⟩ := exists_coordinate_halfspace_holder_extension k (fderiv ℝ u)
    (hu.continuous_fderiv (by norm_num)) hα.le hD hD hgrad hfirst
  have hDle : D ≤ ε * H + (B₀ + 1) * M := by dsimp [D]; nlinarith
  have hMle : M ≤ ε * H + (B₀ + 1) * M := by
    nlinarith [mul_nonneg hε.le hH, mul_nonneg hB₀.le hM]
  exact ⟨U, V, hU, hV, hUn.trans (max_le hMle hDle),
    hVn.trans (by simpa only [max_self] using hDle)⟩

end OAI.Analysis.PDE.Schauder
