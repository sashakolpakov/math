import OAI.Analysis.Calculus.FiniteExtension.Halfspace.Extension.Local

/-! A local half-chart has a genuine global Cᴺ representative after
shrinking the chart. -/

noncomputable section
open Set Metric
open scoped ContDiff
namespace OAI.Analysis.Calculus.FiniteExtension

variable {m N : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
local notation "E" => EuclideanSpace ℝ (Fin m)

theorem exists_contDiff_extension_halfball
    (ℓ : E →L[ℝ] ℝ) (ν : E) (hν : ℓ ν = 1)
    {R : ℝ} (hR : 0 < R) (f : E → F)
    (hf : ContDiffOn ℝ N f ({x | 0 ≤ ℓ x} ∩ ball 0 R)) :
    ∃ g : E → F, ContDiff ℝ N g ∧
      EqOn g f ({x | 0 ≤ ℓ x} ∩ closedBall 0 (R/2)) := by
  let b : ContDiffBump (0 : E) := ⟨R/2, 3*R/4, by positivity, by linarith⟩
  have hb : tsupport (b : E → ℝ) ⊆ ball 0 R := by
    have hs : tsupport (b : E → ℝ) ⊆ closedBall 0 (3*R/4) := by
      apply closure_minimal _ isClosed_closedBall
      intro x hx
      change b x ≠ 0 at hx
      by_contra hn
      have hdist : 3*R/4 ≤ dist x 0 := (lt_of_not_ge hn).le
      exact hx (b.zero_of_le_dist hdist)
    exact hs.trans (closedBall_subset_ball (by linarith))
  obtain ⟨g, hg, heq⟩ := exists_contDiff_extension_of_local_halfspace ℓ ν hν
    isOpen_ball f hf b b.contDiff hb
  refine ⟨g, hg, ?_⟩
  intro x hx
  exact heq x hx.1 (b.one_of_mem_closedBall hx.2)

/-- Coordinate-halfball form used by the normalized boundary charts. -/
theorem exists_contDiff_extension_coordinate_halfball
    (k : Fin m) {R : ℝ} (hR : 0 < R) (f : E → F)
    (hf : ContDiffOn ℝ N f ({x | 0 ≤ x k} ∩ ball 0 R)) :
    ∃ g : E → F, ContDiff ℝ N g ∧
      EqOn g f ({x | 0 ≤ x k} ∩ closedBall 0 (R/2)) := by
  exact exists_contDiff_extension_halfball (EuclideanSpace.proj k)
    (EuclideanSpace.single k 1) (by simp) hR f hf

end OAI.Analysis.Calculus.FiniteExtension
