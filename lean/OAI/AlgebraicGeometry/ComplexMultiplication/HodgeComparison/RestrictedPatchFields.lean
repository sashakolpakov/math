import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CompactPatchFields

/-! # Restricted Patch Fields -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison

noncomputable section

/-! Restricting measurable compact-chart frames to an additional compact
set preserves boundedness and strong measurability of their coefficients. -/

open _root_.MeasureTheory Set

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
  {F : Type*} [NormedAddCommGroup F]

def CompactMetricCover.CM.Construction.CompactMetricChartCover.restrictedPatchField (K : Set V.analyticSpace) (f : Fin C.size → V.analyticSpace → F) :
    V.analyticSpace → F := K.indicator (C.patchField f)

theorem CompactMetricCover.CM.Construction.CompactMetricChartCover.restrictedPatchField_eq_sum (K : Set V.analyticSpace) (f : Fin C.size → V.analyticSpace → F) :
    C.restrictedPatchField K f = ∑ i, (K ∩ C.piece i).indicator (f i) := by
  classical
  funext x
  by_cases hx : x ∈ K
  · obtain ⟨i, hi⟩ := C.exists_piece x
    change K.indicator (C.patchField f) x = _
    rw [indicator_of_mem hx, C.patchField_eq f hi, Finset.sum_apply, Finset.sum_eq_single i]
    · rw [indicator_of_mem (show x ∈ K ∩ C.piece i from ⟨hx, hi⟩)]
    · intro j _ hji
      exact indicator_of_notMem (fun hj => Set.disjoint_left.mp (C.pieces_disjoint hji) hj.2 hi) _
    · simp
  · change K.indicator (C.patchField f) x = _
    rw [indicator_of_notMem hx, Finset.sum_apply]
    symm
    apply Finset.sum_eq_zero
    intro i _
    exact indicator_of_notMem (fun hi => hx hi.1) _

theorem CompactMetricCover.CM.Construction.CompactMetricChartCover.restrictedPatchField_aestronglyMeasurable {K : Set V.analyticSpace} (hK : IsCompact K)
    (f : Fin C.size → V.analyticSpace → F) (hf : ∀ i, ContinuousOn (f i) (K ∩ C.compactSet i)) :
    AEStronglyMeasurable (C.restrictedPatchField K f) (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) := by
  rw [C.restrictedPatchField_eq_sum]
  apply Finset.aestronglyMeasurable_sum
  intro i _
  have hKi : MeasurableSet (K ∩ C.piece i) := hK.measurableSet.inter (C.piece_measurable i)
  exact (aestronglyMeasurable_indicator_iff hKi).mpr
    ((hf i).aestronglyMeasurable_of_subset_isCompact (hK.inter (C.isCompact i)) hKi
      (fun x hx => ⟨hx.1, C.piece_subset i hx.2⟩))

theorem CompactMetricCover.CM.Construction.CompactMetricChartCover.restrictedPatchField_bounded {K : Set V.analyticSpace} (hK : IsCompact K)
    (f : Fin C.size → V.analyticSpace → F) (hf : ∀ i, ContinuousOn (f i) (K ∩ C.compactSet i)) :
    ∃ B : ℝ, 0 < B ∧ ∀ x, ‖C.restrictedPatchField K f x‖ ≤ B := by
  classical
  choose B hB using fun i => (hK.inter (C.isCompact i)).exists_bound_of_continuousOn (hf i)
  refine ⟨1 + ∑ i, max (B i) 0, by positivity, fun x => ?_⟩
  by_cases hx : x ∈ K
  · obtain ⟨i, hi⟩ := C.exists_piece x
    change ‖K.indicator (C.patchField f) x‖ ≤ _
    rw [indicator_of_mem hx, C.patchField_eq f hi]
    calc
      _ ≤ B i := hB i x ⟨hx, C.piece_subset i hi⟩
      _ ≤ max (B i) 0 := le_max_left _ _
      _ ≤ ∑ j, max (B j) 0 := Finset.single_le_sum (fun j _ => le_max_right _ _) (Finset.mem_univ i)
      _ ≤ _ := by linarith
  · change ‖K.indicator (C.patchField f) x‖ ≤ _
    rw [indicator_of_notMem hx, norm_zero]
    positivity

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison
