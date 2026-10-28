import OAI.Analysis.PDE.Weak.Boundary.Halfspace.LocalH2
import OAI.Analysis.PDE.Weak.Boundary.TangentialLocalH1
import OAI.Analysis.PDE.Variational.LocalizedEquation

/-! Boundary H² and zero-trace tangential H¹ representatives on genuine
neighborhoods, with all auxiliary cutoffs and their bounds constructed. -/

noncomputable section
open Set Filter _root_.MeasureTheory InnerProductSpace Metric
open scoped ContDiff Topology
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem local_halfspace_H2_near_point
    (k : Fin (m + 1)) (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (hA : ContDiff ℝ ∞ A) {lam Λ D : ℝ}
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hD : 0 ≤ D)
    (hAM : ∀ x, ‖A x‖ ≤ Λ) (hDA : ∀ x, ‖fderiv ℝ A x‖ ≤ D)
    (hell : ∀ x z, lam * ‖z‖ ^ 2 ≤ inner ℝ (A x z) z)
    (p : H1Pair m) (hp : p ∈ H1Zero {x | 0 < x k})
    (f : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))
    {U : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hU : IsOpen U)
    (hweak : WeakDivergenceEquation ({x | 0 < x k} ∩ U)
      (fieldMultiplierCLM A hA.continuous.aestronglyMeasurable (Eventually.of_forall hAM) p.2) f)
    (x₀ : OAI.Analysis.PDE.Variational.CellCoordinates m) (hx₀ : x₀ ∈ U) :
    ∃ V : Set (OAI.Analysis.PDE.Variational.CellCoordinates m), IsOpen V ∧ x₀ ∈ V ∧ V ⊆ U ∧
      (∀ j : Fin (m + 1), ∃ g : Lp (OAI.Analysis.PDE.Variational.CellVectors m) 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)),
        HasWeakDirectionalDerivativeOn volume ({x | 0 < x k} ∩ V) (Pi.single j 1) p.2 g) ∧
      (∀ j : Fin (m + 1), j ≠ k → ∃ q : H1Pair m, q ∈ H1Zero {x | 0 < x k} ∧
        HasWeakDirectionalDerivativeOn volume ({x | 0 < x k} ∩ V) (Pi.single j 1) p.1 q.1 ∧
        HasWeakDirectionalDerivativeOn volume ({x | 0 < x k} ∩ V) (Pi.single j 1) p.2 q.2) := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
  obtain ⟨η, hη, hηrange, hone, hzero⟩ := OAI.Analysis.PDE.Green.exists_smooth_cutoff_near_compact
    (isCompact_closedBall x₀ (r / 2)) (isOpen_ball : IsOpen (ball x₀ r))
    (closedBall_subset_ball (by linarith)) (k := ⊤)
  have hηsupp : tsupport η ⊆ ball x₀ r := by
    intro x hx
    by_contra hnot
    exact (notMem_tsupport_iff_eventuallyEq.mpr (hzero x hnot)) hx
  have hs : HasCompactSupport η :=
    isCompact_of_isClosed_isBounded (isClosed_tsupport η) (isBounded_ball.subset hηsupp)
  have hηM : ∀ x, |η x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (hηrange x).1]
    exact (hηrange x).2
  have hηone : ∀ x ∈ ball x₀ (r / 2), η x = 1 := fun x hx =>
    (hone x (ball_subset_closedBall hx)).eq_of_nhds
  obtain ⟨K, hK⟩ := (hasCompactSupport_cellGradient hs).exists_bound_of_continuous
    (OAI.Analysis.PDE.Variational.continuous_cellGradient (hη.of_le (by simp)))
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  obtain ⟨L, hL⟩ := (hs.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    ((hη.of_le (by simp) : ContDiff ℝ 1 η).continuous_fderiv one_ne_zero)
  refine ⟨ball x₀ (r / 2), isOpen_ball, mem_ball_self (by positivity), (ball_subset_ball (by linarith)).trans hrU, ?_, ?_⟩
  · exact local_halfspace_gradient_weak_derivatives_on_plateau k A hA hlam hΛ hD hK0 hAM hDA hell
      p hp f hU hweak η hη hs (hηsupp.trans hrU) hηM hK hL isOpen_ball hηone ((ball_subset_ball (by linarith)).trans hrU)
  · intro j hj
    let ℓ : OAI.Analysis.PDE.Variational.CellCoordinates m →L[ℝ] ℝ := ContinuousLinearMap.proj k
    obtain ⟨q, hq, hv, hg⟩ := local_halfspace_tangential_H1_derivative ℓ A (hA.of_le (by simp))
      hlam hΛ hD hK0 hAM hDA hell p hp f hU hweak η hη hs (hηsupp.trans hrU) hηM hK hL j
      (by simp [ℓ, Ne.symm hj])
    have he := OAI.Analysis.PDE.Variational.cutoffH1Pair_eq_on (ball x₀ (r / 2)) isOpen_ball η (hη.of_le (by simp)) hηM hK hηone p
    refine ⟨q, hq, ?_, ?_⟩
    · apply (hv.on).congr_on volume
      · filter_upwards [he] with x hx
        exact fun hxs => (hx hxs.2).1
      · exact Eventually.of_forall fun _ _ => rfl
    · apply (hg.on).congr_on volume
      · filter_upwards [he] with x hx
        exact fun hxs => (hx hxs.2).2
      · exact Eventually.of_forall fun _ _ => rfl

end OAI.Analysis.PDE.Weak
