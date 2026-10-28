import OAI.Analysis.DifferentialForms.Manifold.Charts
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-! # Integration -/

namespace OAI.Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing

noncomputable section

/-! PolarizedPairing: compactly supported chart integrands and finite chart partitions. -/

open scoped _root_.Manifold ContDiff _root_.Topology BigOperators
open Set Function Filter _root_.MeasureTheory

section Cutoff

variable {E M F : Type*}
  [TopologicalSpace E] [T2Space E]
  [TopologicalSpace M] [CompactSpace M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Extend a chart integrand weighted by a subordinate cutoff by zero. -/
def chartCutoff (e : OpenPartialHomeomorph M E) (ρ : M → ℝ) (f : E → F) : E → F :=
  e.target.indicator (fun y => ρ (e.symm y) • f y)

omit [T2Space E] [CompactSpace M] in
theorem support_chartCutoff_subset (e : OpenPartialHomeomorph M E)
    (ρ : M → ℝ) (f : E → F) :
    support (chartCutoff e ρ f) ⊆ e '' tsupport ρ := by
  intro y hy
  have hyt : y ∈ e.target := by
    by_contra ht
    exact hy (by simp [chartCutoff, ht])
  have hρ : ρ (e.symm y) ≠ 0 := by
    intro hz
    exact hy (by simp [chartCutoff, hyt, hz])
  exact ⟨e.symm y, subset_tsupport _ hρ, e.right_inv hyt⟩

omit [T2Space E] in
theorem isCompact_chartCutoff_bound (e : OpenPartialHomeomorph M E)
    (ρ : M → ℝ) (hρ : tsupport ρ ⊆ e.source) : IsCompact (e '' tsupport ρ) := by
  have hc : IsCompact (tsupport ρ) := isClosed_closure.isCompact
  exact hc.image_of_continuousOn (e.continuousOn.mono hρ)

theorem chartCutoff_hasCompactSupport (e : OpenPartialHomeomorph M E)
    (ρ : M → ℝ) (hρ : tsupport ρ ⊆ e.source) (f : E → F) :
    HasCompactSupport (chartCutoff e ρ f) :=
  (isCompact_chartCutoff_bound e ρ hρ).of_isClosed_subset isClosed_closure
    (closure_minimal (support_chartCutoff_subset e ρ f)
      (isCompact_chartCutoff_bound e ρ hρ).isClosed)

theorem chartCutoff_continuous (e : OpenPartialHomeomorph M E)
    (ρ : M → ℝ) (hρ : Continuous ρ) (hs : tsupport ρ ⊆ e.source)
    (f : E → F) (hf : ContinuousOn f e.target) :
    Continuous (chartCutoff e ρ f) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  by_cases hy : y ∈ e.target
  · have hc : ContinuousOn (fun y => ρ (e.symm y) • f y) e.target :=
      (hρ.comp_continuousOn e.symm.continuousOn).smul hf
    have he : chartCutoff e ρ f =ᶠ[𝓝 y] (fun y => ρ (e.symm y) • f y) := by
      filter_upwards [e.open_target.mem_nhds hy] with z hz
      simp [chartCutoff, hz]
    exact (hc.continuousAt (e.open_target.mem_nhds hy)).congr_of_eventuallyEq he
  · have hk := isCompact_chartCutoff_bound e ρ hs
    have hyk : y ∉ e '' tsupport ρ := by
      rintro ⟨x, hx, rfl⟩
      exact hy (e.map_source (hs hx))
    have he : chartCutoff e ρ f =ᶠ[𝓝 y] (fun _ => 0) := by
      filter_upwards [hk.isClosed.isOpen_compl.mem_nhds hyk] with z hz
      exact notMem_support.mp (fun h => hz (support_chartCutoff_subset e ρ f h))
    exact continuousAt_const.congr_of_eventuallyEq he

end Cutoff

variable (E M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

/-- Finite atlas data and a genuine subordinate smooth partition of unity. -/
structure FiniteChartPartition where
  centers : Finset M
  partition : SmoothPartitionOfUnity centers 𝓘(ℝ, E) M
  subordinate : ∀ i : centers, tsupport (partition i) ⊆ (chartAt E i.val).source

theorem finiteChartPartition_nonempty : Nonempty (FiniteChartPartition E M) := by
  classical
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : M => (chartAt E x).source) (fun x => (chartAt E x).open_source)
    (fun x _ => mem_iUnion.mpr ⟨x, mem_chart_source E x⟩)
  have hcover : (Set.univ : Set M) ⊆ ⋃ i : s, (chartAt E i.val).source := by
    intro x hx
    obtain ⟨i, hi, hix⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hix⟩
  obtain ⟨p, hp⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, E)) isClosed_univ (fun i : s => (chartAt E i.val).source)
    (fun i => (chartAt E i.val).open_source) hcover
  exact ⟨⟨s, p, hp⟩⟩

def canonicalChartPartition : FiniteChartPartition E M :=
  (finiteChartPartition_nonempty E M).some

end

end OAI.Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing
