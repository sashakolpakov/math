import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

noncomputable section
open Set Metric TopologicalSpace Function _root_.MeasureTheory Module
  ContinuousLinearMap Filter MeasureTheory.Measure Bornology
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Weak

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A compactly supported smooth cutoff with a genuine open plateau.
The ambient norm need not itself be smooth. -/
theorem exists_cutoff_with_open_plateau {Ω : Set E} (hΩ : IsOpen Ω) {x : E} (hx : x ∈ Ω) :
    ∃ (η : E → ℝ) (U : Set E), IsOpen U ∧ x ∈ U ∧ U ⊆ Ω ∧
      ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ tsupport η ⊆ Ω ∧
      (∀ y, η y ∈ Icc (0 : ℝ) 1) ∧ (∀ y ∈ U, η y = 1) := by
  obtain ⟨d, hd, hdsub⟩ : ∃ d : ℝ, 0 < d ∧ Euclidean.closedBall x d ⊆ Ω :=
    Euclidean.nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds hx)
  let c : ContDiffBump (toEuclidean x) :=
    { rIn := d / 2, rOut := d, rIn_pos := half_pos hd, rIn_lt_rOut := half_lt_self hd }
  let η : E → ℝ := c ∘ toEuclidean
  let U := Euclidean.ball x (d / 2)
  have hs : support η ⊆ Euclidean.ball x d := by
    intro y hy
    have hc : toEuclidean y ∈ support c := by
      simpa only [η, mem_support, comp_apply, Ne] using hy
    rwa [c.support_eq] at hc
  have hts : tsupport η ⊆ Euclidean.closedBall x d := by
    rw [tsupport, ← Euclidean.closure_ball _ hd.ne']
    exact closure_mono hs
  have hc : HasCompactSupport η := by
    apply isCompact_of_isClosed_isBounded isClosed_closure
    exact Euclidean.isCompact_closedBall.isBounded.subset hts
  have hcd : ContDiff ℝ ∞ η := c.contDiff.comp (ContinuousLinearEquiv.contDiff _)
  have hone : ∀ y ∈ U, η y = 1 := by
    intro y hy
    apply c.one_of_mem_closedBall
    change dist (toEuclidean y) (toEuclidean x) < d / 2 at hy
    exact hy.le
  refine ⟨η, U, Euclidean.isOpen_ball, ?_, ?_, hcd, hc, hts.trans hdsub, ?_, hone⟩
  · exact Euclidean.mem_ball_self (half_pos hd)
  · intro y hy
    exact hdsub (hts (subset_tsupport η (by
      change η y ≠ 0
      rw [hone y hy]
      norm_num)))
  · intro y
    exact ⟨c.nonneg, c.le_one⟩

end OAI.Analysis.PDE.Weak
