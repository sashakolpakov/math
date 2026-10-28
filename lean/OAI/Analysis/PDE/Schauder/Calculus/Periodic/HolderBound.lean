import OAI.Analysis.PDE.Dirichlet.Periodic.HigherJet
import OAI.Analysis.Normed.Function.Holder.Banach.Norm

open Set Metric Module
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder

variable {E P V F ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]

/-- A fixed compact set controls the whole periodic Hölder norm, with
linear dependence on the value and first-derivative bound. -/
theorem exists_periodic_holder_control_ball
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : Continuous r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ R : ℝ, 0 < R ∧ ∀ (f : E → F) (T : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} F α) (M : ℝ),
      0 ≤ M → OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b f →
      (∀ x ∈ closedBall 0 R, DifferentiableAt ℝ f x) →
      (∀ x ∈ closedBall 0 R, ‖f x‖ ≤ M) →
      (∀ x ∈ closedBall 0 R, ‖fderiv ℝ f x‖ ≤ M) →
      (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value T x = f x) → ‖T‖ ≤ 4 * M := by
  let S := OAI.Analysis.PDE.Dirichlet.latticeSublevelCell e b K r
  have hS : IsCompact S := OAI.Analysis.PDE.Dirichlet.isCompact_latticeSublevelCell e b hK hr
  obtain ⟨R₀,hR₀⟩ := hS.cthickening.exists_bound_of_continuousOn
    (f := fun x : E => x) continuous_id.continuousOn
  let R := max R₀ 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hball : cthickening 1 S ⊆ closedBall 0 R := by
    intro x hx
    simpa only [mem_closedBall,dist_zero_right] using (hR₀ x hx).trans (le_max_left R₀ 1)
  have hsub : S ⊆ cthickening 1 S := by
    intro x hx
    exact ((closedBall_subset_cthickening_singleton x 1).trans
      (cthickening_subset_of_subset 1 (singleton_subset_iff.mpr hx))) (by simp)
  refine ⟨R,hR,?_⟩
  intro f T M hM hp hd hf hD hT
  have hnorm (x) (hx : r x ≤ 0) : ‖f x‖ ≤ M := by
    rw [← hp.representative x]
    exact hf _ (hball (hsub (OAI.Analysis.PDE.Dirichlet.latticeRepresentative_mem_sublevelCell e b hrp hbounded hx)))
  have hlocal : ∀ x ∈ cthickening 1 S, ∀ y ∈ cthickening 1 S,
      ‖f x-f y‖ ≤ (2*M)*dist x y^α := by
    intro x hx y hy
    by_cases hxy : dist x y ≤ 1
    · have h := (convex_closedBall (0 : E) R).norm_image_sub_le_of_norm_fderiv_le
        hd hD (hball hy) (hball hx)
      have hm : ‖f x-f y‖ ≤ M*dist x y := by simpa only [dist_eq_norm] using h
      have hpw := Real.self_le_rpow_of_le_one dist_nonneg hxy hα1
      exact hm.trans ((mul_le_mul_of_nonneg_left hpw hM).trans
        (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg dist_nonneg α)))
    · have hpw : 1 ≤ dist x y^α := Real.one_le_rpow (le_of_not_ge hxy) hα
      have hn : ‖f x-f y‖ ≤ 2*M := (norm_sub_le _ _).trans
        (by linarith [hf x (hball hx),hf y (hball hy)])
      exact hn.trans (le_mul_of_one_le_right (by positivity) hpw)
  have hholder := OAI.Analysis.PDE.Dirichlet.lattice_holder_of_thickened_cell e b hrp hbounded
    (fun _ : Unit => f) (fun _ => hp) hα (by positivity : 0 ≤ 2*M) hM
    (fun _ => hnorm) (fun _ x hx y hy => hlocal x hx.1 y hy.1)
  apply OAI.Analysis.Normed.Function.Holder.HolderMap.norm_le_of_bounds hα (by positivity : 0 ≤ 4*M)
  · intro x
    rw [hT]
    exact (hnorm x x.property).trans (by linarith)
  · intro x y
    rw [hT,hT]
    simpa only [show 2*M+2*M = 4*M by ring,Subtype.dist_eq] using
      hholder () x x.property y y.property

end OAI.Analysis.PDE.Schauder
