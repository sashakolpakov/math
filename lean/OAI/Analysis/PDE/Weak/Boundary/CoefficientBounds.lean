import OAI.Analysis.PDE.Weak.Boundary.SmoothBounded

noncomputable section
open Set
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_fderiv_bound_of_eq_const_off_compact
    {f : OAI.Analysis.PDE.Variational.CellCoordinates m → E} (hf : ContDiff ℝ ∞ f)
    {K : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hK : IsCompact K) (c : E)
    (he : ∀ x ∉ K, f x = c) : ∃ D : ℝ, 0 ≤ D ∧ ∀ x, ‖fderiv ℝ f x‖ ≤ D := by
  have hs : HasCompactSupport (fun x => f x - c) := by
    apply hK.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hn
    exact hx (sub_eq_zero.mpr (he x hn))
  have hdiff : ContDiff ℝ 1 (fun x => f x - c) := (hf.sub contDiff_const).of_le (by simp)
  obtain ⟨D, hD⟩ := (hs.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    (hdiff.continuous_fderiv one_ne_zero)
  have heq (x) : fderiv ℝ (fun x => f x - c) x = fderiv ℝ f x :=
    ((hf.differentiable (by simp) x).hasFDerivAt.sub_const c).fderiv
  refine ⟨D, (norm_nonneg _).trans (hD 0), ?_⟩
  intro x
  simpa only [heq] using hD x

end OAI.Analysis.PDE.Weak
