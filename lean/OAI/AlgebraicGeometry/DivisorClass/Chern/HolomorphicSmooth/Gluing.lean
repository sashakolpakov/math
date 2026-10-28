import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.MultiplierReal
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.FormPartition

/-! # Gluing -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.Gluing

noncomputable section

/-! Actual smooth representatives of sufficiently small cutoffs glue to a global smooth representative of the original bundle L² element. -/

open _root_.TopologicalSpace Set
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

theorem holomorphic_smooth_representative_of_local_cutoffs (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (n : ℕ)
    (v : Holomorphic.IntegralPairZero.HolomorphicFormL2With V h n)
    (hlocal : ∀ x : V.analyticSpace, ∃ U : Set V.analyticSpace, IsOpen U ∧ x ∈ U ∧
      ∀ ρ : V.analyticSpace → ℝ, ∀ hρ : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ ρ,
        tsupport ρ ⊆ U → ∃ a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n,
          Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h n a = Holomorphic.MultiplierReal.holomorphicMetricRealL2Multiplier V h n ρ hρ v) :
    ∃ a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n, Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h n a = v := by
  classical
  choose U hU hxU hrepr using hlocal
  obtain ⟨s, hcover⟩ := isCompact_univ.elim_finite_subcover U hU
    (fun x _ => mem_iUnion.mpr ⟨x, hxU x⟩)
  have hscover : ∀ x : V.analyticSpace, ∃ i : s, x ∈ U i.val := by
    intro x
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover (mem_univ x))
    exact ⟨⟨y, hy⟩, hxy⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, V.analyticModel)) isClosed_univ (fun i : s => U i.val) (fun i => hU i.val)
    (fun x _ => mem_iUnion.mpr (hscover x))
  have hρsmooth (i : s) : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ (ρ i) := (ρ i).contMDiff
  have hρsum (x : V.analyticSpace) : ∑ i : s, ρ i x = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ x)
  choose a ha using (fun i : s => hrepr i.val (ρ i) (hρsmooth i) (hρ i))
  refine ⟨∑ i : s, a i, ?_⟩
  rw [map_sum]
  simp only [ha]
  exact Holomorphic.MultiplierReal.holomorphicMetricRealL2Multiplier_partition V h n (fun i : s => ρ i) hρsmooth hρsum v

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.Gluing
