import OAI.Analysis.PDE.Dirichlet.Periodic.Calculus
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Set Module Metric
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

/-- Shift both points by the same lattice element before using a local
Hölder estimate. Independently reducing the two points to a cell would
not preserve their distance and would be insufficient at cell faces. -/
theorem lattice_holder_of_thickened_cell {E P V F J ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [Fintype ι]
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {K : Set V} {r : E → ℝ}
    (hr : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (g : J → E → F) (hg : ∀ p, LatticePeriodic e b (g p))
    {α C M : ℝ} (hα : 0 ≤ α) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hnorm : ∀ p x, r x ≤ 0 → ‖g p x‖ ≤ M)
    (hholder : ∀ p x, x ∈ cthickening 1 (latticeSublevelCell e b K r) ∩ {z | r z ≤ 0} →
      ∀ y, y ∈ cthickening 1 (latticeSublevelCell e b K r) ∩ {z | r z ≤ 0} →
        ‖g p x - g p y‖ ≤ C * (dist x y) ^ α) :
    ∀ p x, r x ≤ 0 → ∀ y, r y ≤ 0 →
      ‖g p x - g p y‖ ≤ (C + 2 * M) * (dist x y) ^ α := by
  intro p x hx y hy
  by_cases hxy : dist x y ≤ 1
  · let l : Submodule.span ℤ (Set.range b) := -ZSpan.floor b (e x).1
    let t : E := e.symm ((l : P), 0)
    have hrep : t + x = latticeRepresentative e b x := by
      change e.symm ((l : P), 0) + x = _
      rw [← lattice_translate_eq]
      simp only [l, latticeRepresentative, ZSpan.fract_apply, Submodule.coe_neg, sub_eq_add_neg]
    have hcell : t + x ∈ latticeSublevelCell e b K r := by
      rw [hrep]
      exact latticeRepresentative_mem_sublevelCell e b hr hbounded hx
    have hshift (z : E) : g p (t + z) = g p z := by
      simpa only [lattice_translate_eq, t] using hg p z l
    have hrshift (z : E) : r (t + z) = r z := by
      simpa only [lattice_translate_eq, t] using hr z l
    have hball : closedBall (t + x) 1 ⊆ cthickening 1 (latticeSublevelCell e b K r) :=
      (closedBall_subset_cthickening_singleton _ _).trans
        (cthickening_subset_of_subset 1 (singleton_subset_iff.mpr hcell))
    have hx' : t + x ∈ cthickening 1 (latticeSublevelCell e b K r) ∩ {z | r z ≤ 0} :=
      ⟨hball (by simp), by change r (t + x) ≤ 0; rwa [hrshift]⟩
    have hy' : t + y ∈ cthickening 1 (latticeSublevelCell e b K r) ∩ {z | r z ≤ 0} := by
      refine ⟨hball ?_, by change r (t + y) ≤ 0; rwa [hrshift]⟩
      simpa only [mem_closedBall, dist_add_left, dist_comm y x] using hxy
    have hh := hholder p (t + x) hx' (t + y) hy'
    rw [hshift, hshift, dist_add_left] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg dist_nonneg _))
  · have hdist : 1 ≤ (dist x y) ^ α := Real.one_le_rpow (le_of_lt (lt_of_not_ge hxy)) hα
    calc
      ‖g p x - g p y‖ ≤ ‖g p x‖ + ‖g p y‖ := norm_sub_le _ _
      _ ≤ 2 * M := by linarith [hnorm p x hx, hnorm p y hy]
      _ ≤ C + 2 * M := by linarith
      _ ≤ (C + 2 * M) * (dist x y) ^ α := le_mul_of_one_le_right (by positivity) hdist

end OAI.Analysis.PDE.Dirichlet
