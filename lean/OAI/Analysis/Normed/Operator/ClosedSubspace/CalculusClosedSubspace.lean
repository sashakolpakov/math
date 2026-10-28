import OAI.Analysis.Normed.Operator.ClosedSubspace.Smooth

open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.Normed.Operator.ClosedSubspace

universe u
variable {E F G : Type u}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem contDiffOn_nat_of_isometry
    (e : F →ₗᵢ[ℝ] G) {f : E → F} {S : Set E} (hS : IsOpen S) (n : ℕ)
    (h : ContDiffOn ℝ n (fun x => e (f x)) S) : ContDiffOn ℝ n f S := by
  induction n generalizing F G with
  | zero =>
      change ContDiffOn ℝ 0 f S
      rw [contDiffOn_zero,continuousOn_iff_continuous_domRestrict]
      apply e.isometry.isEmbedding.continuous_iff.mpr
      exact continuousOn_iff_continuous_domRestrict.mp h.continuousOn
  | succ n ih =>
      have hd x (hx : x ∈ S) : ∃ L : E →L[ℝ] F,
          HasFDerivAt f L x ∧ e.toContinuousLinearMap.comp L = fderiv ℝ (fun y => e (f y)) x :=
        exists_hasFDerivAt_of_isometry e
          (((h x hx).contDiffAt (hS.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
      classical
      let L (x : E) : E →L[ℝ] F := if hx : x ∈ S then (hd x hx).choose else 0
      have hL x (hx : x ∈ S) : HasFDerivAt f (L x) x ∧
          e.toContinuousLinearMap.comp (L x) = fderiv ℝ (fun y => e (f y)) x := by
        simpa only [L,dite_eq_left hx] using (hd x hx).choose_spec
      have hD : ContDiffOn ℝ n (fderiv ℝ (fun y => e (f y))) S :=
        h.fderiv_of_isOpen hS (by simp)
      have hLC : ContDiffOn ℝ n L S := ih (postcompIsometry e) (hD.congr
        (fun x hx => (hL x hx).2))
      rw [show (↑(n+1) : ℕ∞ω) = (n : ℕ∞ω)+1 by simp,
        contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hS.uniqueDiffOn]
      exact ⟨by simp, L,hLC,fun x hx => (hL x hx).1.hasFDerivWithinAt⟩

theorem contDiffOn_infty_of_isometry
    (e : F →ₗᵢ[ℝ] G) {f : E → F} {S : Set E} (hS : IsOpen S)
    (h : ContDiffOn ℝ ∞ (fun x => e (f x)) S) : ContDiffOn ℝ ∞ f S := by
  rw [contDiffOn_infty] at h ⊢
  exact fun n => contDiffOn_nat_of_isometry e hS n (h n)

end OAI.Analysis.Normed.Operator.ClosedSubspace
