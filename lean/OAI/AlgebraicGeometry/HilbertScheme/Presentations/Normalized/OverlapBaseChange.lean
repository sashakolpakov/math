import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.ChartBaseChange

/-! # Overlap Base Change -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.OverlapBaseChange.Grassmannian

noncomputable section

/-! Changes of base preserve the principal overlaps and their transition maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {ι ν : Type u} [Fintype ι] [DecidableEq ι]
variable (a b : ι → ν) {S T : Scheme.{u}} (f : T ⟶ S)

theorem normalizedChartBaseMap_pivot :
    (ChartBaseChange.Grassmannian.normalizedChartBaseMap a f).appTop (Overlap.Grassmannian.normalizedPivotSection a b S) =
      Overlap.Grassmannian.normalizedPivotSection a b T := by
  let φ := (ChartBaseChange.Grassmannian.normalizedChartBaseMap a f).appTop.hom
  have hQ := ChartBaseChange.Grassmannian.normalizedChartBaseMap_matrix a f
  change (Chart.Grassmannian.universalNormalizedMatrix a S).map φ = Chart.Grassmannian.universalNormalizedMatrix a T at hQ
  change φ (Matrices.Grassmannian.selectedColumns b (Chart.Grassmannian.universalNormalizedMatrix a S)).det =
    (Matrices.Grassmannian.selectedColumns b (Chart.Grassmannian.universalNormalizedMatrix a T)).det
  rw [φ.map_det]
  change (Matrices.Grassmannian.selectedColumns b ((Chart.Grassmannian.universalNormalizedMatrix a S).map φ)).det = _
  rw [hQ]

theorem normalizedChartBaseMap_preimage_overlap :
    ChartBaseChange.Grassmannian.normalizedChartBaseMap a f ⁻¹ᵁ (Overlap.Grassmannian.normalizedOverlapInclusion a b S).left.opensRange =
      (Overlap.Grassmannian.normalizedOverlapInclusion a b T).left.opensRange := by
  change ChartBaseChange.Grassmannian.normalizedChartBaseMap a f ⁻¹ᵁ
    ((Chart.Grassmannian.normalizedChart a S).left.basicOpen (Overlap.Grassmannian.normalizedPivotSection a b S)).ι.opensRange =
    ((Chart.Grassmannian.normalizedChart a T).left.basicOpen (Overlap.Grassmannian.normalizedPivotSection a b T)).ι.opensRange
  rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι, Scheme.preimage_basicOpen_top,
    normalizedChartBaseMap_pivot]

theorem normalizedOverlapBaseMap_range :
    Set.range ((Overlap.Grassmannian.normalizedOverlapInclusion a b T).left ≫ ChartBaseChange.Grassmannian.normalizedChartBaseMap a f) ⊆
      Set.range (Overlap.Grassmannian.normalizedOverlapInclusion a b S).left := by
  rintro _ ⟨x, rfl⟩
  have h := congrArg (fun U : (Chart.Grassmannian.normalizedChart a T).left.Opens =>
    (Overlap.Grassmannian.normalizedOverlapInclusion a b T).left x ∈ U) (normalizedChartBaseMap_preimage_overlap a b f)
  exact h.to_iff.mpr ⟨x, rfl⟩

def normalizedOverlapBaseMap :
    (Overlap.Grassmannian.normalizedChartOverlap a b T).left ⟶ (Overlap.Grassmannian.normalizedChartOverlap a b S).left :=
  IsOpenImmersion.lift (Overlap.Grassmannian.normalizedOverlapInclusion a b S).left
    ((Overlap.Grassmannian.normalizedOverlapInclusion a b T).left ≫ ChartBaseChange.Grassmannian.normalizedChartBaseMap a f)
    (normalizedOverlapBaseMap_range a b f)

theorem normalizedOverlapBaseMap_inclusion :
    normalizedOverlapBaseMap a b f ≫ (Overlap.Grassmannian.normalizedOverlapInclusion a b S).left =
      (Overlap.Grassmannian.normalizedOverlapInclusion a b T).left ≫ ChartBaseChange.Grassmannian.normalizedChartBaseMap a f :=
  IsOpenImmersion.lift_fac _ _ _

theorem normalizedOverlapBaseMap_over :
    normalizedOverlapBaseMap a b f ≫ (Overlap.Grassmannian.normalizedChartOverlap a b S).hom =
      (Overlap.Grassmannian.normalizedChartOverlap a b T).hom ≫ f := by
  calc
    _ = normalizedOverlapBaseMap a b f ≫
        (Overlap.Grassmannian.normalizedOverlapInclusion a b S).left ≫ (Chart.Grassmannian.normalizedChart a S).hom :=
      congrArg (fun g => normalizedOverlapBaseMap a b f ≫ g) (Overlap.Grassmannian.normalizedOverlapInclusion a b S).w.symm
    _ = _ := by
      rw [← Category.assoc, normalizedOverlapBaseMap_inclusion, Category.assoc,
        ChartBaseChange.Grassmannian.normalizedChartBaseMap_over, ← Category.assoc, (Overlap.Grassmannian.normalizedOverlapInclusion a b T).w]

theorem normalizedOverlapBaseMap_isPullback :
    IsPullback (normalizedOverlapBaseMap a b f) (Overlap.Grassmannian.normalizedOverlapInclusion a b T).left
      (Overlap.Grassmannian.normalizedOverlapInclusion a b S).left (ChartBaseChange.Grassmannian.normalizedChartBaseMap a f) := by
  apply IsOpenImmersion.isPullback
  · exact (normalizedOverlapBaseMap_inclusion a b f).symm
  · exact normalizedChartBaseMap_preimage_overlap a b f

theorem chartHomMatrix_overlapTransition {X : Scheme.{u}}
    (g : X ⟶ (Overlap.Grassmannian.normalizedChartOverlap a b S).left) :
    ChartBaseChange.Grassmannian.chartHomMatrix b S (g ≫ (Overlap.Grassmannian.normalizedOverlapTransition a b S).hom.left ≫
      (Overlap.Grassmannian.normalizedOverlapInclusion b a S).left) =
    Matrices.Grassmannian.normalizeColumns b (ChartBaseChange.Grassmannian.chartHomMatrix a S (g ≫ (Overlap.Grassmannian.normalizedOverlapInclusion a b S).left)) := by
  let g' : Over.mk (g ≫ (Overlap.Grassmannian.normalizedChartOverlap a b S).hom) ⟶ Overlap.Grassmannian.normalizedChartOverlap a b S :=
    Over.homMk g
  have h := AtlasMaps.Grassmannian.overlapTransition_matrix a b S g'
  rw [AtlasMaps.Grassmannian.overlapMatrix_eq_chartMatrix, AtlasMaps.Grassmannian.overlapMatrix_eq_chartMatrix] at h
  change ((Chart.Grassmannian.normalizedChartRepresentation b S).hom.app _
    ((g' ≫ (Overlap.Grassmannian.normalizedOverlapTransition a b S).hom) ≫ Overlap.Grassmannian.normalizedOverlapInclusion b a S)).val =
    Matrices.Grassmannian.normalizeColumns b (((Chart.Grassmannian.normalizedChartRepresentation a S).hom.app _
      (g' ≫ Overlap.Grassmannian.normalizedOverlapInclusion a b S)).val) at h
  rw [Chart.Grassmannian.normalizedChartRepresentation_apply, Chart.Grassmannian.normalizedChartRepresentation_apply] at h
  exact h

theorem normalizedOverlapBaseMap_transition :
    normalizedOverlapBaseMap a b f ≫ (Overlap.Grassmannian.normalizedOverlapTransition a b S).hom.left =
      (Overlap.Grassmannian.normalizedOverlapTransition a b T).hom.left ≫ normalizedOverlapBaseMap b a f := by
  apply (cancel_mono (Overlap.Grassmannian.normalizedOverlapInclusion b a S).left).mp
  apply ChartBaseChange.Grassmannian.chartHom_ext b S
  · rw [Category.assoc, (Overlap.Grassmannian.normalizedOverlapInclusion b a S).w,
      Category.assoc, (Overlap.Grassmannian.normalizedOverlapTransition a b S).hom.w,
      normalizedOverlapBaseMap_over, Category.assoc, (Overlap.Grassmannian.normalizedOverlapInclusion b a S).w,
      Category.assoc, normalizedOverlapBaseMap_over, ← Category.assoc,
      (Overlap.Grassmannian.normalizedOverlapTransition a b T).hom.w]
  · rw [Category.assoc, chartHomMatrix_overlapTransition, normalizedOverlapBaseMap_inclusion]
    rw [ChartBaseChange.Grassmannian.chartHomMatrix_comp, ChartBaseChange.Grassmannian.normalizedChartBaseMap_matrix]
    rw [Category.assoc, normalizedOverlapBaseMap_inclusion,
      ← Category.assoc, ChartBaseChange.Grassmannian.chartHomMatrix_comp, ChartBaseChange.Grassmannian.normalizedChartBaseMap_matrix]
    exact (chartHomMatrix_overlapTransition a b (𝟙 (Overlap.Grassmannian.normalizedChartOverlap a b T).left)).symm

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.OverlapBaseChange.Grassmannian
