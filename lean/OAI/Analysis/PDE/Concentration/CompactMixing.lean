import OAI.Analysis.PDE.Concentration.BallChain

namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory Set Metric InnerProductSpace Laplacian Filter
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

theorem compact_integral_le_ball_sum {A : Set E} (hA : IsCompact A)
    {f : E → ℝ} (hf : Continuous f) {s : ℝ} (S : Finset E)
    (hcover : A ⊆ ⋃ z ∈ S, closedBall z s)
    (hn : ∀ z ∈ S, ∀ y ∈ closedBall z s, 0 ≤ f y) :
    (∫ y in A, f y) ≤ ∑ z ∈ S, ∫ y in closedBall z s, f y := by
  classical
  have hi (z : E) : Integrable ((closedBall z s).indicator f) :=
    (integrable_indicator_iff measurableSet_closedBall).mpr
      (hf.continuousOn.integrableOn_compact (isCompact_closedBall z s))
  have hnonneg (z : E) (hz : z ∈ S) (y : E) : 0 ≤ (closedBall z s).indicator f y := by
    by_cases hy : y ∈ closedBall z s
    · simpa only [indicator_of_mem hy] using hn z hz y hy
    · simp only [indicator_of_notMem hy, le_refl]
  have hpoint (y : E) : A.indicator f y ≤ ∑ z ∈ S, (closedBall z s).indicator f y := by
    by_cases hy : y ∈ A
    · rw [indicator_of_mem hy]
      obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.mp (hcover hy)
      calc
        f y = (closedBall z s).indicator f y := (indicator_of_mem hyz f).symm
        _ ≤ ∑ w ∈ S, (closedBall w s).indicator f y :=
          Finset.single_le_sum (fun w hw => hnonneg w hw y) hz
    · rw [indicator_of_notMem hy]
      exact Finset.sum_nonneg (fun z hz => hnonneg z hz y)
  have hh := integral_mono
    ((integrable_indicator_iff hA.measurableSet).mpr (hf.continuousOn.integrableOn_compact hA))
    (MeasureTheory.integrable_finsetSum S (fun z _ => hi z)) hpoint
  rw [integral_indicator hA.measurableSet, MeasureTheory.integral_finsetSum S (fun z _ => hi z)] at hh
  simpa only [integral_indicator measurableSet_closedBall] using hh

/-- A nonnegative superharmonic function controls its whole compact connected
region in L¹ from any point of that region. The constant is constructed from
positive local means, finite chains, and a finite ball cover. -/
theorem exists_uniform_compact_volume_mixing
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {K : Set P} (hK : IsCompact K) (hc : Convex ℝ K)
    {φ : P → E} (hφ : ContinuousOn φ K) {s : ℝ} (hs : 0 < s) :
    ∃ M : ℝ, 0 < M ∧ ∀ f : E → ℝ, ContDiff ℝ 2 f →
      (∀ x ∈ φ '' K, ∀ y ∈ closedBall x (7 * s), 0 ≤ f y) →
      (∀ x ∈ φ '' K, ∀ y ∈ closedBall x (7 * s), Δ f y ≤ 0) →
      ∀ x ∈ φ '' K, (∫ y in φ '' K, f y) ≤ M * f x := by
  classical
  have hA : IsCompact (φ '' K) := hK.image_of_continuousOn hφ
  obtain ⟨S, hSA, hS, hcover⟩ := hA.elim_finite_subcover_image
    (b := φ '' K) (c := fun z => ball z s) (fun _ _ => isOpen_ball)
    (fun z hz => mem_iUnion₂.mpr ⟨z, hz, mem_ball_self hs⟩)
  obtain ⟨M, hM, hmix⟩ := exists_uniform_compact_ball_mixing hK hc hφ hs
  refine ⟨(hS.toFinset.card : ℝ) * M + 1, by positivity, ?_⟩
  intro f hf hn hΔ x hx
  have hfx : 0 ≤ f x := hn x hx x (mem_closedBall_self (by positivity))
  have hh := compact_integral_le_ball_sum hA hf.continuous hS.toFinset
    (fun y hy => by
      obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.mp (hcover hy)
      exact mem_iUnion₂.mpr ⟨z, hS.mem_toFinset.mpr hz, ball_subset_closedBall hyz⟩)
    (fun z hz y hy => hn z (hSA (hS.mem_toFinset.mp hz)) y
      (closedBall_subset_closedBall (by linarith) hy))
  have hb : (∑ z ∈ hS.toFinset, ∫ y in closedBall z s, f y) ≤
      (hS.toFinset.card : ℝ) * (M * f x) := by
    calc
      _ ≤ ∑ _z ∈ hS.toFinset, M * f x := Finset.sum_le_sum (fun z hz =>
        hmix f hf hn hΔ x hx z (hSA (hS.mem_toFinset.mp hz)))
      _ = _ := by simp
  nlinarith [hh.trans hb]

end OAI.Analysis.PDE.Concentration
