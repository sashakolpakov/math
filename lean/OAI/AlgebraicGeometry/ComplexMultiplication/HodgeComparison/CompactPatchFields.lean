import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CompactMetricCover
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-! # Compact Patch Fields -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison

noncomputable section

/-! Actual measurable fields in a finite compact coordinate refinement. -/

open _root_.MeasureTheory Set
open scoped ENNReal

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
  {F : Type*} [NormedAddCommGroup F]

def CompactMetricCover.CM.Construction.CompactMetricChartCover.patchField (f : Fin C.size → V.analyticSpace → F) (x : V.analyticSpace) : F :=
  ∑ i, (C.piece i).indicator (f i) x

theorem CompactMetricCover.CM.Construction.CompactMetricChartCover.patchField_eq (f : Fin C.size → V.analyticSpace → F)
    {i : Fin C.size} {x : V.analyticSpace} (hx : x ∈ C.piece i) : C.patchField f x = f i x := by
  classical
  rw [CompactMetricCover.CM.Construction.CompactMetricChartCover.patchField, Finset.sum_eq_single i]
  · exact indicator_of_mem hx _
  · intro j _ hji
    exact indicator_of_notMem (fun hj => Set.disjoint_left.mp (C.pieces_disjoint hji) hj hx) _
  · simp

theorem CompactMetricCover.CM.Construction.CompactMetricChartCover.patchField_aestronglyMeasurable (f : Fin C.size → V.analyticSpace → F)
    (hf : ∀ i, ContinuousOn (f i) (C.compactSet i)) :
    AEStronglyMeasurable (C.patchField f) (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) := by
  have h (i : Fin C.size) : AEStronglyMeasurable ((C.piece i).indicator (f i))
      (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) :=
    (aestronglyMeasurable_indicator_iff (C.piece_measurable i)).mpr
      ((hf i).aestronglyMeasurable_of_subset_isCompact
        (C.isCompact i) (C.piece_measurable i) (C.piece_subset i))
  have heq : C.patchField f = ∑ i, (C.piece i).indicator (f i) := by
    funext x
    simp only [CompactMetricCover.CM.Construction.CompactMetricChartCover.patchField, Finset.sum_apply]
  rw [heq]
  exact Finset.aestronglyMeasurable_sum Finset.univ (fun i _ => h i)

theorem CompactMetricCover.CM.Construction.CompactMetricChartCover.patchField_bounded (f : Fin C.size → V.analyticSpace → F)
    (hf : ∀ i, ContinuousOn (f i) (C.compactSet i)) :
    ∃ B : ℝ, 0 < B ∧ ∀ x, ‖C.patchField f x‖ ≤ B := by
  classical
  choose B hB using fun i => (C.isCompact i).exists_bound_of_continuousOn (hf i)
  refine ⟨1 + ∑ i, max (B i) 0, by positivity, ?_⟩
  intro x
  obtain ⟨i, hi⟩ := C.exists_piece x
  rw [C.patchField_eq f hi]
  calc
    ‖f i x‖ ≤ B i := hB i x (C.piece_subset i hi)
    _ ≤ max (B i) 0 := le_max_left _ _
    _ ≤ ∑ j, max (B j) 0 := Finset.single_le_sum (fun j _ => le_max_right _ _) (Finset.mem_univ i)
    _ ≤ _ := by linarith

theorem CompactMetricCover.CM.Construction.CompactMetricChartCover.patchField_memLp (f : Fin C.size → V.analyticSpace → F)
    (hf : ∀ i, ContinuousOn (f i) (C.compactSet i)) (p : ℝ≥0∞) :
    MemLp (C.patchField f) p (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) := by
  obtain ⟨B, _, hB⟩ := C.patchField_bounded f hf
  exact MemLp.of_bound (C.patchField_aestronglyMeasurable f hf) B
    (Filter.Eventually.of_forall hB)

theorem CompactMetricCover.CM.Construction.CompactMetricChartCover.patchField_add (f g : Fin C.size → V.analyticSpace → F) :
    C.patchField (fun i x => f i x + g i x) = C.patchField f + C.patchField g := by
  funext x
  obtain ⟨i, hi⟩ := C.exists_piece x
  simp only [Pi.add_apply, C.patchField_eq _ hi]

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 F]

theorem CompactMetricCover.CM.Construction.CompactMetricChartCover.patchField_smul (a : 𝕜) (f : Fin C.size → V.analyticSpace → F) :
    C.patchField (fun i x => a • f i x) = a • C.patchField f := by
  funext x
  obtain ⟨i, hi⟩ := C.exists_piece x
  simp only [Pi.smul_apply, C.patchField_eq _ hi]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison
