import OAI.RepresentationTheory.Weil.Local.NonarchimedeanNorm
import Mathlib.Topology.Algebra.Group.Quotient

/-! # Bruhat Approximation -/

namespace OAI.RepresentationTheory.Weil.Local.BruhatApproximation.Construction

noncomputable section

/-! Uniform approximation by compact locally constant functions, with one fixed compact support. -/

open scoped Classical

theorem compact_continuous_locallyConstant_approximation
    {E : Type*} [NormedAddCommGroup E] [IsUltrametricDist E] [ProperSpace E]
    {f : E → ℂ} (hf : Continuous f) (hs : HasCompactSupport f) :
    ∃ K : Set E, IsCompact K ∧ tsupport f ⊆ K ∧
      ∀ ε : ℝ, 0 < ε → ∃ g : E → ℂ,
        IsLocallyConstant g ∧ tsupport g ⊆ K ∧ ∀ x, ‖g x - f x‖ < ε := by
  obtain ⟨R, hR, hbound⟩ := hs.isBounded.exists_pos_norm_le
  let K : Set E := Metric.closedBall 0 (R + 1)
  have hK : IsCompact K := isCompact_closedBall _ _
  refine ⟨K, hK, ?_, fun ε hε => ?_⟩
  · intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (hbound x hx).trans (le_add_of_nonneg_right zero_le_one)
  · obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuous_iff.mp
      (hs.uniformContinuous_of_continuous hf) ε hε
    let r : ℝ := min (δ / 2) 1
    have hr : 0 < r := lt_min (half_pos hδ) zero_lt_one
    let U := IsUltrametricDist.closedBall_openAddSubgroup E hr
    let q : E → E ⧸ U.toAddSubgroup := QuotientAddGroup.mk
    let g : E → ℂ := fun x => f (Quotient.out (q x))
    have hrep (x : E) : ‖Quotient.out (q x) - x‖ ≤ r := by
      obtain ⟨t, ht⟩ := QuotientAddGroup.mk_out_eq_add U.toAddSubgroup x
      change ‖(QuotientAddGroup.mk x : E ⧸ U.toAddSubgroup).out - x‖ ≤ r
      rw [ht, add_sub_cancel_left]
      have htU := t.property
      change t.val ∈ Metric.closedBall 0 r at htU
      simpa only [Metric.mem_closedBall, dist_zero_right] using htU
    have hglc : IsLocallyConstant g :=
      (IsLocallyConstant.of_discrete (fun z : E ⧸ U.toAddSubgroup => f z.out)).comp_continuous
        QuotientAddGroup.continuous_mk
    refine ⟨g, hglc, ?_, fun x => ?_⟩
    · apply closure_minimal _ hK.isClosed
      intro x hx
      have hrepR : ‖Quotient.out (q x)‖ ≤ R := hbound _ (subset_tsupport f hx)
      rw [Metric.mem_closedBall, dist_zero_right]
      calc
        ‖x‖ ≤ ‖Quotient.out (q x)‖ + ‖Quotient.out (q x) - x‖ := by
          simpa only [norm_sub_rev] using norm_le_insert' x (Quotient.out (q x))
        _ ≤ R + 1 := add_le_add hrepR ((hrep x).trans (min_le_right _ _))
    · change ‖f (Quotient.out (q x)) - f x‖ < ε
      rw [← dist_eq_norm]
      apply hδf
      rw [dist_eq_norm]
      exact (hrep x).trans_lt ((min_le_left _ _).trans_lt (half_lt_self hδ))

end

end OAI.RepresentationTheory.Weil.Local.BruhatApproximation.Construction
