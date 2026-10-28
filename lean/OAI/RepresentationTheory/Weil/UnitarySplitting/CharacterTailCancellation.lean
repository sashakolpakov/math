import OAI.RepresentationTheory.Weil.UnitarySplitting.CharacterCutoffs

/-! # Character Tail Cancellation -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.CharacterTailCancellation.Construction

noncomputable section

/-! Exact cancellation of sufficiently distant character integrals when
the domain is preserved by a bounded additive translation. -/

open _root_.MeasureTheory _root_.Topology

theorem ultra_character_cutoff_stable_on_set
    {F : Type} [NormedField F] [IsUltrametricDist F] [ProperSpace F]
    [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure] (ψ : AddChar F ℂ)
    (hc : Continuous (fun x : F => ψ x)) (t : F) (ht : ψ t ≠ 1)
    (S : Set F) (hS : MeasurableSet S) (R : ℝ) (htR : ‖t‖ ≤ R)
    (htranslate : ∀ x : F, R < ‖x‖ → (t + x ∈ S ↔ x ∈ S))
    (r : ℝ) (hr : R ≤ r) :
    (∫ x in Metric.closedBall 0 r ∩ S, ψ x ∂μ) =
      ∫ x in Metric.closedBall 0 R ∩ S, ψ x ∂μ := by
  let A : Set F := {x | x ∈ Metric.closedBall 0 r ∧ x ∉ Metric.closedBall 0 R ∧ x ∈ S}
  have hA : MeasurableSet A := measurableSet_closedBall.inter (measurableSet_closedBall.compl.inter hS)
  have htrans (x : F) : t + x ∈ A ↔ x ∈ A := by
    have hbr := CharacterCutoffs.Construction.ultra_closedBall_translate r t (htR.trans hr) x
    have hbR := CharacterCutoffs.Construction.ultra_closedBall_translate R t htR x
    by_cases hxR : x ∈ Metric.closedBall 0 R
    · simp only [A, Set.mem_ofPred_eq, hxR, hbR.mpr hxR, not_true_eq_false, false_and, and_false]
    · have hx : R < ‖x‖ := by
        simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hxR
      simp only [A, Set.mem_ofPred_eq, hbr, hbR, htranslate x hx]
  have hzero := CharacterCutoffs.Construction.character_cutoff_integral_zero μ ψ A t htrans ht
  rw [integral_indicator hA] at hzero
  have hset : (Metric.closedBall (0 : F) r ∩ S) \ (Metric.closedBall 0 R ∩ S) = A := by
    ext x
    simp only [A, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq]
    tauto
  have hsub : Metric.closedBall (0 : F) R ∩ S ⊆ Metric.closedBall 0 r ∩ S :=
    Set.inter_subset_inter_left _ (Metric.closedBall_subset_closedBall hr)
  have hi : IntegrableOn (fun x : F => ψ x) (Metric.closedBall 0 r ∩ S) μ :=
    (hc.continuousOn.integrableOn_compact (isCompact_closedBall 0 r)).mono_set Set.inter_subset_left
  rw [← hset, setIntegral_sdiff (measurableSet_closedBall.inter hS) hi hsub] at hzero
  exact sub_eq_zero.mp hzero

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.CharacterTailCancellation.Construction
