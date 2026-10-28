import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.Overlap
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! # Atlas Maps -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian

noncomputable section

/-! Pointwise formulas and lifting maps for the normalized Grassmannian atlas. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν : Type u} [Fintype ι] [DecidableEq ι]
variable (a b : ι → ν) (S : Scheme.{u})

def chartMatrix {T : Over S} (f : T ⟶ Chart.Grassmannian.normalizedChart a S) : Matrix ι ν Γ(T.left, ⊤) :=
  ((Chart.Grassmannian.normalizedChartRepresentation a S).hom.app (.op T) f).val

omit [Fintype ι] in
theorem chartMatrix_normalized {T : Over S} (f : T ⟶ Chart.Grassmannian.normalizedChart a S) :
    Matrices.Grassmannian.IsNormalized a (chartMatrix a S f) :=
  ((Chart.Grassmannian.normalizedChartRepresentation a S).hom.app (.op T) f).property

omit [Fintype ι] in
theorem chartMatrix_injective (T : Over S) : Function.Injective (chartMatrix a S (T := T)) := by
  intro f g h
  apply ((Chart.Grassmannian.normalizedChartRepresentation a S).app (.op T)).toEquiv.injective
  exact Subtype.ext h

def overlapMatrix {T : Over S} (f : T ⟶ Overlap.Grassmannian.normalizedChartOverlap a b S) : Matrix ι ν Γ(T.left, ⊤) :=
  (Overlap.Grassmannian.normalizedOverlapSchemePointEquiv a b S T f).val

theorem overlapMatrix_injective (T : Over S) :
    Function.Injective (overlapMatrix a b S (T := T)) := by
  intro f g h
  apply (Overlap.Grassmannian.normalizedOverlapSchemePointEquiv a b S T).injective
  exact Subtype.ext h

theorem overlapMatrix_normalized {T : Over S} (f : T ⟶ Overlap.Grassmannian.normalizedChartOverlap a b S) :
    Matrices.Grassmannian.IsNormalized a (overlapMatrix a b S f) :=
  (Overlap.Grassmannian.normalizedOverlapSchemePointEquiv a b S T f).property.1

theorem overlapMatrix_unit {T : Over S} (f : T ⟶ Overlap.Grassmannian.normalizedChartOverlap a b S) :
    IsUnit (Matrices.Grassmannian.selectedColumns b (overlapMatrix a b S f)).det :=
  (Overlap.Grassmannian.normalizedOverlapSchemePointEquiv a b S T f).property.2

theorem overlapMatrix_eq_chartMatrix {T : Over S} (f : T ⟶ Overlap.Grassmannian.normalizedChartOverlap a b S) :
    overlapMatrix a b S f = chartMatrix a S (f ≫ Overlap.Grassmannian.normalizedOverlapInclusion a b S) := rfl

def overlapLift {T : Over S} (f : T ⟶ Chart.Grassmannian.normalizedChart a S)
    (h : IsUnit (Matrices.Grassmannian.selectedColumns b (chartMatrix a S f)).det) :
    T ⟶ Overlap.Grassmannian.normalizedChartOverlap a b S :=
  (Relative.UnitOpen.relativeUnitOpenPointEquiv (Chart.Grassmannian.normalizedChart a S) (Overlap.Grassmannian.normalizedPivotSection a b S) T).symm
    ⟨f, (Overlap.Grassmannian.normalizedPivotSection_unit_iff a b S f).mpr h⟩

theorem overlapLift_inclusion {T : Over S} (f : T ⟶ Chart.Grassmannian.normalizedChart a S)
    (h : IsUnit (Matrices.Grassmannian.selectedColumns b (chartMatrix a S f)).det) :
    overlapLift a b S f h ≫ Overlap.Grassmannian.normalizedOverlapInclusion a b S = f :=
  congrArg Subtype.val
    ((Relative.UnitOpen.relativeUnitOpenPointEquiv (Chart.Grassmannian.normalizedChart a S) (Overlap.Grassmannian.normalizedPivotSection a b S) T).apply_symm_apply
      ⟨f, (Overlap.Grassmannian.normalizedPivotSection_unit_iff a b S f).mpr h⟩)

theorem overlapLift_matrix {T : Over S} (f : T ⟶ Chart.Grassmannian.normalizedChart a S)
    (h : IsUnit (Matrices.Grassmannian.selectedColumns b (chartMatrix a S f)).det) :
    overlapMatrix a b S (overlapLift a b S f h) = chartMatrix a S f := by
  rw [overlapMatrix_eq_chartMatrix, overlapLift_inclusion]

theorem overlapTransition_matrix {T : Over S} (f : T ⟶ Overlap.Grassmannian.normalizedChartOverlap a b S) :
    overlapMatrix b a S (f ≫ (Overlap.Grassmannian.normalizedOverlapTransition a b S).hom) =
      Matrices.Grassmannian.normalizeColumns b (overlapMatrix a b S f) := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (Overlap.Grassmannian.normalizedOverlapTransition_representation a b S) (.op T)) f
  exact congrArg Subtype.val h

theorem normalizedOverlapTransition_self :
    (Overlap.Grassmannian.normalizedOverlapTransition a a S).hom = 𝟙 _ := by
  apply yoneda.map_injective
  apply (cancel_mono (Overlap.Grassmannian.normalizedOverlapRepresentation a a S).hom).mp
  rw [Overlap.Grassmannian.normalizedOverlapTransition_representation, OverlapFunctor.Grassmannian.normalizedOverlapSwap_self]
  simp

instance normalizedOverlapInclusion_self_isIso : IsIso (Overlap.Grassmannian.normalizedOverlapInclusion a a S) := by
  have hs : IsUnit (Overlap.Grassmannian.normalizedPivotSection a a S) := by
    change IsUnit (Matrices.Grassmannian.selectedColumns a (Chart.Grassmannian.universalNormalizedMatrix a S)).det
    rw [Chart.Grassmannian.universalNormalizedMatrix_normalized a S, Matrix.det_one]
    exact isUnit_one
  apply (isIso_iff_of_reflects_iso _ (Over.forget S)).mp
  change IsIso (Overlap.Grassmannian.normalizedOverlapInclusion a a S).left
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  change ((Chart.Grassmannian.normalizedChart a S).left.basicOpen (Overlap.Grassmannian.normalizedPivotSection a a S)).ι.opensRange = ⊤
  rw [Scheme.Opens.opensRange_ι]
  exact (Chart.Grassmannian.normalizedChart a S).left.basicOpen_of_isUnit hs

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian
