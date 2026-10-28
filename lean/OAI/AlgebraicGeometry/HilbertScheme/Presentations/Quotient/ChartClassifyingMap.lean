import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.GrassmannianProjectivity
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.SubmoduleExtension

/-! # Chart Classifying Map -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.ChartClassifyingMap.Grassmannian

noncomputable section

/-! Normalized quotient matrices determine Grassmannian maps through their kernels. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {ι ν : Type u} [Fintype ι] [DecidableEq ι]
variable {S : Scheme.{u}} (a b : ι → ν) {T : Over S}

theorem grassmannianChartOverlap_over :
    (Normalized.Overlap.Grassmannian.normalizedOverlapTransition a b S).hom ≫ Normalized.Overlap.Grassmannian.normalizedOverlapInclusion b a S ≫
        Grassmannian.Gluing.grassmannianChartOverMap b S =
      Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a b S ≫ Grassmannian.Gluing.grassmannianChartOverMap a S := by
  apply (Over.forget S).map_injective
  exact (Grassmannian.Gluing.normalizedGrassmannianGlueData (ι := ι) (ν := ν) S).glue_condition a b

theorem chartMaps_eq_of_transition (f : T ⟶ Normalized.Chart.Grassmannian.normalizedChart a S) (g : T ⟶ Normalized.Chart.Grassmannian.normalizedChart b S)
    (hu : IsUnit (Normalized.Matrices.Grassmannian.selectedColumns b (Normalized.AtlasMaps.Grassmannian.chartMatrix a S f)).det)
    (hQ : Normalized.AtlasMaps.Grassmannian.chartMatrix b S g = Normalized.Matrices.Grassmannian.normalizeColumns b (Normalized.AtlasMaps.Grassmannian.chartMatrix a S f)) :
    f ≫ Grassmannian.Gluing.grassmannianChartOverMap a S = g ≫ Grassmannian.Gluing.grassmannianChartOverMap b S := by
  let v := Normalized.AtlasMaps.Grassmannian.overlapLift a b S f hu
  have hv : v ≫ Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a b S = f := Normalized.AtlasMaps.Grassmannian.overlapLift_inclusion a b S f hu
  have hw : (v ≫ (Normalized.Overlap.Grassmannian.normalizedOverlapTransition a b S).hom) ≫ Normalized.Overlap.Grassmannian.normalizedOverlapInclusion b a S = g := by
    apply Normalized.AtlasMaps.Grassmannian.chartMatrix_injective b S T
    rw [← Normalized.AtlasMaps.Grassmannian.overlapMatrix_eq_chartMatrix, Normalized.AtlasMaps.Grassmannian.overlapTransition_matrix]
    change Normalized.Matrices.Grassmannian.normalizeColumns b (Normalized.AtlasMaps.Grassmannian.overlapMatrix a b S (Normalized.AtlasMaps.Grassmannian.overlapLift a b S f hu)) = _
    rw [Normalized.AtlasMaps.Grassmannian.overlapLift_matrix]
    exact hQ.symm
  rw [← hv, ← hw]
  simp only [Category.assoc, grassmannianChartOverlap_over]

theorem chartMaps_transition_of_eq (f : T ⟶ Normalized.Chart.Grassmannian.normalizedChart a S) (g : T ⟶ Normalized.Chart.Grassmannian.normalizedChart b S)
    (he : f ≫ Grassmannian.Gluing.grassmannianChartOverMap a S = g ≫ Grassmannian.Gluing.grassmannianChartOverMap b S) :
    IsUnit (Normalized.Matrices.Grassmannian.selectedColumns b (Normalized.AtlasMaps.Grassmannian.chartMatrix a S f)).det ∧
      Normalized.AtlasMaps.Grassmannian.chartMatrix b S g = Normalized.Matrices.Grassmannian.normalizeColumns b (Normalized.AtlasMaps.Grassmannian.chartMatrix a S f) := by
  let H := Grassmannian.Gluing.grassmannianChart_intersection_isPullback a b S
  have he' : f.left ≫ Grassmannian.Gluing.grassmannianChartMap a S = g.left ≫ Grassmannian.Gluing.grassmannianChartMap b S :=
    congrArg Over.Hom.left he
  let v := H.lift f.left g.left he'
  have hv : v ≫ (Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a b S).left = f.left := H.lift_fst _ _ _
  have hw : v ≫ ((Normalized.Overlap.Grassmannian.normalizedOverlapTransition a b S).hom.left ≫
      (Normalized.Overlap.Grassmannian.normalizedOverlapInclusion b a S).left) = g.left := H.lift_snd _ _ _
  let v' : T ⟶ Normalized.Overlap.Grassmannian.normalizedChartOverlap a b S := Over.homMk v (by
    calc
      _ = v ≫ (Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a b S).left ≫ (Normalized.Chart.Grassmannian.normalizedChart a S).hom :=
        congrArg (fun h => v ≫ h) (Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a b S).w.symm
      _ = T.hom := by rw [← Category.assoc, hv, f.w])
  have hv' : v' ≫ Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a b S = f := (Over.forget S).map_injective hv
  have hw' : (v' ≫ (Normalized.Overlap.Grassmannian.normalizedOverlapTransition a b S).hom) ≫ Normalized.Overlap.Grassmannian.normalizedOverlapInclusion b a S = g := by
    apply (Over.forget S).map_injective
    exact (Category.assoc _ _ _).trans hw
  constructor
  · rw [← hv', ← Normalized.AtlasMaps.Grassmannian.overlapMatrix_eq_chartMatrix]
    exact Normalized.AtlasMaps.Grassmannian.overlapMatrix_unit a b S v'
  · rw [← hw', ← Normalized.AtlasMaps.Grassmannian.overlapMatrix_eq_chartMatrix, Normalized.AtlasMaps.Grassmannian.overlapTransition_matrix,
      Normalized.AtlasMaps.Grassmannian.overlapMatrix_eq_chartMatrix, hv']

variable [Fintype ν] [DecidableEq ν]

theorem chartMaps_eq_iff_kernel_eq (f : T ⟶ Normalized.Chart.Grassmannian.normalizedChart a S) (g : T ⟶ Normalized.Chart.Grassmannian.normalizedChart b S) :
    f ≫ Grassmannian.Gluing.grassmannianChartOverMap a S = g ≫ Grassmannian.Gluing.grassmannianChartOverMap b S ↔
      (Matrix.toLin' (Normalized.AtlasMaps.Grassmannian.chartMatrix a S f)).ker = (Matrix.toLin' (Normalized.AtlasMaps.Grassmannian.chartMatrix b S g)).ker := by
  rw [← Normalized.OverlapEquations.Grassmannian.quotientCompatibility_iff_kernel_eq a b _ _ (Normalized.AtlasMaps.Grassmannian.chartMatrix_normalized a S f)
    (Normalized.AtlasMaps.Grassmannian.chartMatrix_normalized b S g), Normalized.OverlapEquations.Grassmannian.quotientCompatibility_iff_transition a b _ _ (Normalized.AtlasMaps.Grassmannian.chartMatrix_normalized a S f)]
  exact ⟨chartMaps_transition_of_eq a b f g, fun h => chartMaps_eq_of_transition a b f g h.1 h.2⟩

def normalizedMatrixClassifyingMap (Q : Matrix ι ν Γ(T.left, ⊤)) (hQ : Normalized.Matrices.Grassmannian.IsNormalized a Q) :
    T ⟶ Grassmannian.Gluing.grassmannianOver (ι := ι) (ν := ν) S :=
  ((Normalized.Chart.Grassmannian.normalizedChartRepresentation a S).app (.op T)).inv ⟨Q, hQ⟩ ≫ Grassmannian.Gluing.grassmannianChartOverMap a S

omit [Fintype ν] [DecidableEq ν] in
theorem normalizedMatrixClassifyingMap_natural {U : Over S} (f : U ⟶ T)
    (Q : Matrix ι ν Γ(T.left, ⊤)) (hQ : Normalized.Matrices.Grassmannian.IsNormalized a Q) :
    normalizedMatrixClassifyingMap a (Q.map f.left.appTop.hom) (hQ.map f.left.appTop.hom) =
      f ≫ normalizedMatrixClassifyingMap a Q hQ := by
  have h := ConcreteCategory.congr_hom
    ((Normalized.Chart.Grassmannian.normalizedChartRepresentation a S).inv.naturality f.op) ⟨Q, hQ⟩
  change ((Normalized.Chart.Grassmannian.normalizedChartRepresentation a S).app (.op U)).inv
      ⟨Q.map f.left.appTop.hom, hQ.map f.left.appTop.hom⟩ =
    f ≫ ((Normalized.Chart.Grassmannian.normalizedChartRepresentation a S).app (.op T)).inv ⟨Q, hQ⟩ at h
  exact (congrArg (fun g => g ≫ Grassmannian.Gluing.grassmannianChartOverMap a S) h).trans (Category.assoc _ _ _)

theorem normalizedMatrixClassifyingMap_eq_iff
    (Q K : Matrix ι ν Γ(T.left, ⊤)) (hQ : Normalized.Matrices.Grassmannian.IsNormalized a Q) (hK : Normalized.Matrices.Grassmannian.IsNormalized b K) :
    normalizedMatrixClassifyingMap a Q hQ = normalizedMatrixClassifyingMap b K hK ↔
      (Matrix.toLin' Q).ker = (Matrix.toLin' K).ker := by
  change ((Normalized.Chart.Grassmannian.normalizedChartRepresentation a S).app (.op T)).inv ⟨Q, hQ⟩ ≫ _ =
    ((Normalized.Chart.Grassmannian.normalizedChartRepresentation b S).app (.op T)).inv ⟨K, hK⟩ ≫ _ ↔ _
  rw [chartMaps_eq_iff_kernel_eq]
  have h (c : ι → ν) (L : Matrix ι ν Γ(T.left, ⊤)) (hL : Normalized.Matrices.Grassmannian.IsNormalized c L) :
      Normalized.AtlasMaps.Grassmannian.chartMatrix c S (((Normalized.Chart.Grassmannian.normalizedChartRepresentation c S).app (.op T)).inv ⟨L, hL⟩) = L :=
    congrArg Subtype.val (((Normalized.Chart.Grassmannian.normalizedChartRepresentation c S).app (.op T)).toEquiv.apply_symm_apply ⟨L, hL⟩)
  rw [h a Q hQ, h b K hK]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.ChartClassifyingMap.Grassmannian
