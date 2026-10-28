import OAI.Analysis.Calculus.Coefficients.Lattice
import OAI.Analysis.PDE.Dirichlet.Periodic.Data

open Set Filter Module Metric
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A C¹ map has a finite Hölder bound of every exponent at most one on
each compact set, without assuming the compact set is convex. -/
theorem smooth_jet_compact_holder_bound
    (f : E → F) (hf : ContDiff ℝ 1 f) {K : Set E} (hK : IsCompact K)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ (∀ x ∈ K, ‖f x‖ ≤ C) ∧
      ∀ x ∈ K, ∀ y ∈ K, ‖f x-f y‖ ≤ C*dist x y^α := by
  obtain ⟨R,hR⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  have hsub : K ⊆ closedBall (0 : E) R := by
    intro x hx
    simpa only [mem_closedBall,dist_zero_right,id_eq] using hR x hx
  obtain ⟨L,hL⟩ := hf.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall (0 : E) R) (isCompact_closedBall (0 : E) R)
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hf.continuous.continuousOn
  let U := max M 0
  have hU : 0 ≤ U := le_max_right _ _
  have hU' x (hx : x ∈ K) : ‖f x‖ ≤ U := (hM x hx).trans (le_max_left _ _)
  refine ⟨(L : ℝ)+2*U+1,by positivity,?_,?_⟩
  · intro x hx
    exact (hU' x hx).trans (by nlinarith [L.coe_nonneg])
  · intro x hx y hy
    by_cases hd : dist x y ≤ 1
    · have hp := Real.self_le_rpow_of_le_one dist_nonneg hd hα1
      have hxy : ‖f x-f y‖ ≤ (L : ℝ)*dist x y := by
        simpa only [dist_eq_norm] using hL.dist_le_mul x (hsub hx) y (hsub hy)
      exact hxy.trans ((mul_le_mul_of_nonneg_left hp L.coe_nonneg).trans
        (mul_le_mul_of_nonneg_right (by nlinarith) (Real.rpow_nonneg dist_nonneg α)))
    · have hp : 1 ≤ dist x y^α := Real.one_le_rpow (le_of_not_ge hd) hα
      have hb : ‖f x-f y‖ ≤ 2*U := (norm_sub_le _ _).trans (by linarith [hU' x hx,hU' y hy])
      calc
        _ ≤ 2*U := hb
        _ ≤ 2*U*(dist x y)^α := by nlinarith
        _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith [L.coe_nonneg]) (Real.rpow_nonneg dist_nonneg α)

variable {P V ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

theorem periodic_smooth_jet_holder_bound
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : Continuous r) (hrp : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (f : E → F) (hf : ContDiff ℝ 1 f) (hfp : LatticePeriodic e b f)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ (∀ x, r x ≤ 0 → ‖f x‖ ≤ C) ∧
      ∀ x, r x ≤ 0 → ∀ y, r y ≤ 0 → ‖f x-f y‖ ≤ C*dist x y^α := by
  obtain ⟨C,hC,hCB,hCH⟩ := OAI.Analysis.Calculus.Coefficients.periodic_global_bound_holder_of_compact_bounds
    e b hK hr hrp hbounded (fun _ : ℕ ↦ f) (fun _ ↦ hfp) hα (by
      intro S hS
      obtain ⟨M,hM,hMB,hMH⟩ := smooth_jet_compact_holder_bound f hf hS hα hα1
      exact ⟨M,hM,fun _ ↦ hMB,fun _ ↦ hMH⟩)
  exact ⟨C,hC,hCB 0,hCH 0⟩

end OAI.Analysis.PDE.Dirichlet
