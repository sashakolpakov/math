import OAI.Analysis.Normed.Function.Holder.C2HolderLattice
import Mathlib.Topology.MetricSpace.Cauchy

open Set Module Filter Metric
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

/-- Uniform Cauchy convergence on a fundamental cell controls the supremum
norm on the whole closed periodic domain. Cell faces need not be removed. -/
theorem cauchySeq_bcf_of_lattice_cell {E P V F ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) {K : Set V} {r : E → ℝ}
    (hr : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (u : ℕ → ({x | r x ≤ 0} →ᵇ F))
    (huper : ∀ n, LatticePeriodic e lat (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (u n)))
    (hu : UniformCauchySeqOn (fun n ↦ OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (u n)) atTop
      (latticeSublevelCell e lat K r)) : CauchySeq u := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.mp hu (ε / 2) (half_pos hε)
  refine ⟨N, ?_⟩
  intro m hm n hn
  apply lt_of_le_of_lt ?_ (half_lt_self hε)
  rw [dist_eq_norm]
  apply (BoundedContinuousFunction.norm_le (half_pos hε).le).mpr
  intro x
  let y := latticeRepresentative e lat x
  have hy : y ∈ latticeSublevelCell e lat K r :=
    latticeRepresentative_mem_sublevelCell e lat hr hbounded x.property
  have hmrep := (huper m).representative x
  have hnrep := (huper n).representative x
  rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply _ x.property] at hmrep hnrep
  have hsmall := hN m hm n hn y hy
  change dist (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (u m) (latticeRepresentative e lat x))
    (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (u n) (latticeRepresentative e lat x)) < ε / 2 at hsmall
  rw [hmrep, hnrep, dist_eq_norm] at hsmall
  exact hsmall.le

end OAI.Analysis.PDE.Dirichlet
