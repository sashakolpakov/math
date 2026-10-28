import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

open Set Metric Filter
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

/-- Quantitative Hölder control gives equicontinuity with one modulus for the
whole family, as needed by the compactness step of the continuity method. -/
theorem equicontinuous_of_uniform_holder
    {E Y ι : Type*} [PseudoMetricSpace E] [NormedAddCommGroup Y]
    {u : ι → E → Y} {α C : ℝ} (hα : 0 < α)
    (hu : ∀ i x y, ‖u i x - u i y‖ ≤ C * (dist x y) ^ α) : Equicontinuous u := by
  intro x₀
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  have ht : Tendsto (fun d : ℝ ↦ C * d ^ α) (𝓝 0) (𝓝 0) := by
    simpa [Real.zero_rpow hα.ne'] using
      (show Continuous (fun d : ℝ ↦ C * d ^ α) from
        continuous_const.mul (Real.continuous_rpow_const hα.le)).tendsto 0
  obtain ⟨δ, hδ, hsmall⟩ := Metric.mem_nhds_iff.mp (ht (Iio_mem_nhds hε))
  refine ⟨δ, hδ, ?_⟩
  intro x hx i
  have hd : dist x₀ x ∈ ball (0 : ℝ) δ := by
    simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg dist_nonneg,
      dist_comm x₀ x] using hx
  have hb : dist (u i x₀) (u i x) ≤ C * (dist x₀ x) ^ α := by
    simpa only [dist_eq_norm] using hu i x₀ x
  exact hb.trans_lt (hsmall hd)

/-- A bounded equicontinuous family on a compact metric space has an actual
uniformly convergent subsequence. -/
theorem exists_uniform_limit_of_equicontinuous
    {E Y : Type*} [MetricSpace E] [CompactSpace E]
    [NormedAddCommGroup Y] [ProperSpace Y]
    (u : ℕ → E → Y) (hu : ∀ k, Continuous (u k))
    {M : ℝ}
    (hbound : ∀ k x, ‖u k x‖ ≤ M)
    (heq : Equicontinuous u) :
    ∃ v : E → Y, Continuous v ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoUniformly (fun k ↦ u (φ k)) v atTop := by
  classical
  let f : ℕ → BoundedContinuousFunction E Y :=
    fun k ↦ BoundedContinuousFunction.mkOfCompact ⟨u k, hu k⟩
  have hrange : ∀ g : Set.range f, ∃ k, g.val = f k := fun g ↦
    let ⟨k, hk⟩ := g.property
    ⟨k, hk.symm⟩
  choose j hj using hrange
  have heq' : Equicontinuous ((↑) : Set.range f → E → Y) := by
    convert heq.comp j using 1
    funext g x
    change g.val x = u (j g) x
    rw [hj g]
    rfl
  have hc : IsCompact (closure (range f)) := BoundedContinuousFunction.arzela_ascoli
    (closedBall (0 : Y) M) (isCompact_closedBall _ _) (range f)
    (by
      intro g x hg
      obtain ⟨k, rfl⟩ := hg
      rw [mem_closedBall, dist_zero_right]
      exact hbound k x) heq'
  obtain ⟨v, _, φ, hφ, hlim⟩ := hc.tendsto_subseq (fun k ↦ subset_closure (mem_range_self k))
  refine ⟨v, v.continuous, φ, hφ, ?_⟩
  exact BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hlim

/-- A uniformly bounded Hölder family on a compact metric space has a
uniformly convergent subsequence. This extracts an actual limit function. -/
theorem exists_uniform_limit_of_holder
    {E Y : Type*} [MetricSpace E] [CompactSpace E]
    [NormedAddCommGroup Y] [ProperSpace Y]
    (u : ℕ → E → Y) (hu : ∀ k, Continuous (u k))
    {α C M : ℝ} (hα : 0 < α)
    (hbound : ∀ k x, ‖u k x‖ ≤ M)
    (hholder : ∀ k x y, ‖u k x - u k y‖ ≤ C * (dist x y) ^ α) :
    ∃ v : E → Y, Continuous v ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoUniformly (fun k ↦ u (φ k)) v atTop :=
  exists_uniform_limit_of_equicontinuous u hu hbound
    (equicontinuous_of_uniform_holder hα hholder)

end OAI.Analysis.PDE.Dirichlet
