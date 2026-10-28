import OAI.Analysis.PDE.Concentration.CompactMixing

namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory Set Metric InnerProductSpace Laplacian Filter
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

/-- Local version of compact-region mixing. The extension away from the
region is constructed and plays no role in the superharmonic assumptions. -/
theorem exists_uniform_local_compact_volume_mixing
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {K : Set P} (hK : IsCompact K) (hc : Convex ℝ K)
    {φ : P → E} (hφ : ContinuousOn φ K) {s : ℝ} (hs : 0 < s)
    {U : Set E} (hU : IsOpen U)
    (hdom : ∀ x ∈ φ '' K, closedBall x (7 * s) ⊆ U) :
    ∃ M : ℝ, 0 < M ∧ ∀ f : E → ℝ, ContDiffOn ℝ ∞ f U →
      (∀ y ∈ U, 0 ≤ f y) → (∀ y ∈ U, Δ f y ≤ 0) →
      ∀ x ∈ φ '' K, (∫ y in φ '' K, f y) ≤ M * f x := by
  obtain ⟨M, hM, hmix⟩ := exists_uniform_compact_volume_mixing hK hc hφ hs
  refine ⟨M, hM, ?_⟩
  intro f hf hn hΔ
  let A := φ '' K
  let B := (fun p : E × E => p.1 + p.2) '' (A ×ˢ closedBall (0 : E) (7 * s))
  have hA : IsCompact A := hK.image_of_continuousOn hφ
  have hB : IsCompact B := (hA.prod (isCompact_closedBall 0 (7 * s))).image
    (continuous_fst.add continuous_snd)
  have hBU : B ⊆ U := by
    rintro y ⟨⟨x, z⟩, ⟨hx, hz⟩, rfl⟩
    apply hdom x hx
    simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero] using hz
  obtain ⟨F, hF, he⟩ := exists_global_smooth_eq_near_closed hB.isClosed hU hBU hf
  have hball {x y : E} (hx : x ∈ A) (hy : y ∈ closedBall x (7 * s)) : y ∈ B := by
    refine ⟨(x, y - x), ⟨hx, ?_⟩, ?_⟩
    · simpa only [mem_closedBall, dist_eq_norm, sub_zero] using hy
    · simp
  have hAB : A ⊆ B := fun x hx => hball hx (mem_closedBall_self (by positivity))
  have hbound := hmix F (hF.of_le (by simp))
    (fun x hx y hy => by rw [(he y (hball hx hy)).self_of_nhds]; exact hn y (hdom x hx hy))
    (fun x hx y hy => by
      rw [(laplacian_congr_nhds (he y (hball hx hy))).self_of_nhds]
      exact hΔ y (hdom x hx hy))
  have hint : (∫ y in A, F y) = ∫ y in A, f y :=
    setIntegral_congr_fun hA.measurableSet (fun y hy => (he y (hAB hy)).self_of_nhds)
  intro x hx
  have hh := hbound x hx
  change (∫ y in A, F y) ≤ M * F x at hh
  rw [hint, (he x (hAB hx)).self_of_nhds] at hh
  exact hh

end OAI.Analysis.PDE.Concentration
