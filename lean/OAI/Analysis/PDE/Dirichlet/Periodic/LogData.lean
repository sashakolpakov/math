import OAI.Analysis.PDE.Dirichlet.Periodic.Data
import OAI.Analysis.PDE.Dirichlet.LogData

open Set Module
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion

variable {E P V ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

theorem exists_log_first_derivative_bound_lattice
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {C : Set V} (hC : IsCompact C) {r : E → ℝ} (hr : Continuous r)
    (hrper : LatticePeriodic e lat r) (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) (hFper : LatticePeriodic e lat F)
    (hpos : ∀ x, r x ≤ 0 → 0 < F x) :
    ∃ L : ℝ, 0 < L ∧ ∀ x, r x ≤ 0 → ‖fderiv ℝ (fun z ↦ Real.log (F z)) x‖ ≤ L := by
  have hc : ContinuousOn (fun x ↦ fderiv ℝ (fun z ↦ Real.log (F z)) x)
      {x | r x ≤ 0} := by
    intro x hx
    exact ((hF.contDiffAt.log (hpos x hx).ne').fderiv_right
      (m := 1) (by norm_num)).continuousAt.continuousWithinAt
  exact exists_lattice_norm_bound e lat hC hr hrper hbounded hc
    (hFper.comp Real.log).fderiv

theorem exists_log_second_directional_bound_lattice
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {C : Set V} (hC : IsCompact C) {r : E → ℝ} (hr : Continuous r)
    (hrper : LatticePeriodic e lat r) (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) (hFper : LatticePeriodic e lat F)
    (hpos : ∀ x, r x ≤ 0 → 0 < F x) :
    ∃ L : ℝ, 0 < L ∧ ∀ x, r x ≤ 0 → ∀ v : E,
      -L * ‖v‖ ^ 2 ≤ deriv (deriv (fun t : ℝ ↦ Real.log (F (x + t • v)))) 0 := by
  have hloc : ∀ x, r x ≤ 0 → ContDiffAt ℝ 2 (fun z ↦ Real.log (F z)) x :=
    fun x hx ↦ hF.contDiffAt.log (hpos x hx).ne'
  have hc : ContinuousOn (fun x ↦ fderiv ℝ (fderiv ℝ (fun z ↦ Real.log (F z))) x)
      {x | r x ≤ 0} := by
    intro x hx
    exact (((hloc x hx).fderiv_right (m := 1) (by norm_num)).fderiv_right
      (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  obtain ⟨L, hL, hbound⟩ := exists_lattice_norm_bound e lat hC hr hrper hbounded hc
    (hFper.comp Real.log).fderiv.fderiv
  refine ⟨L, hL, ?_⟩
  intro x hx v
  rw [second_deriv_line (hloc x hx)]
  have h := (bilinear_abs_le (fderiv ℝ (fderiv ℝ (fun z ↦ Real.log (F z))) x) v v).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hbound x hx)
      (norm_nonneg v)) (norm_nonneg v))
  have hlow := neg_abs_le (fderiv ℝ (fderiv ℝ (fun z ↦ Real.log (F z))) x v v)
  nlinarith

end OAI.Analysis.PDE.Dirichlet
