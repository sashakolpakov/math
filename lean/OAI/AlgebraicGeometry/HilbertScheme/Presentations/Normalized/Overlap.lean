import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.OverlapFunctor
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.UnitOpen

/-! # Overlap -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.Overlap.Grassmannian

noncomputable section

/-!
Grassmannian chart overlaps as actual principal-open schemes, and the
scheme isomorphisms induced by their natural matrix coordinate changes.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν : Type u} [Fintype ι] [DecidableEq ι]
variable (a b : ι → ν) (S : Scheme.{u})

def normalizedPivotSection : Γ((Chart.Grassmannian.normalizedChart a S).left, ⊤) :=
  (Matrices.Grassmannian.selectedColumns b (Chart.Grassmannian.universalNormalizedMatrix a S)).det

theorem normalizedPivotSection_unit_iff {T : Over S} (f : T ⟶ Chart.Grassmannian.normalizedChart a S) :
    IsUnit (f.left.appTop (normalizedPivotSection a b S)) ↔
      IsUnit (Matrices.Grassmannian.selectedColumns b
        ((Chart.Grassmannian.normalizedChartRepresentation a S).hom.app (.op T) f).val).det := by
  rw [Chart.Grassmannian.normalizedChartRepresentation_apply, Matrices.Grassmannian.selectedColumns_map]
  exact (congrArg IsUnit (f.left.appTop.hom.map_det
    (Matrices.Grassmannian.selectedColumns b (Chart.Grassmannian.universalNormalizedMatrix a S)))).to_iff

def normalizedChartOverlap : Over S :=
  Relative.UnitOpen.relativeUnitOpen (Chart.Grassmannian.normalizedChart a S) (normalizedPivotSection a b S)

def normalizedOverlapInclusion : normalizedChartOverlap a b S ⟶ Chart.Grassmannian.normalizedChart a S :=
  Relative.UnitOpen.relativeUnitOpenInclusion (Chart.Grassmannian.normalizedChart a S) (normalizedPivotSection a b S)

instance normalizedOverlapInclusion_isOpenImmersion :
    IsOpenImmersion (normalizedOverlapInclusion a b S).left :=
  inferInstanceAs (IsOpenImmersion
    (Relative.UnitOpen.relativeUnitOpenInclusion (Chart.Grassmannian.normalizedChart a S) (normalizedPivotSection a b S)).left)

def normalizedOverlapSchemePointEquiv (T : Over S) :
    (T ⟶ normalizedChartOverlap a b S) ≃
      (OverlapFunctor.Grassmannian.normalizedOverlapSubfunctor a b S).obj (.op T) := by
  let e : (T ⟶ Chart.Grassmannian.normalizedChart a S) ≃
      {Q : Matrix ι ν Γ(T.left, ⊤) // Matrices.Grassmannian.IsNormalized a Q} :=
    ((Chart.Grassmannian.normalizedChartRepresentation a S).app (.op T)).toEquiv
  exact (Relative.UnitOpen.relativeUnitOpenPointEquiv (Chart.Grassmannian.normalizedChart a S) (normalizedPivotSection a b S) T).trans
    ((e.subtypeEquiv
      (p := fun f : T ⟶ Chart.Grassmannian.normalizedChart a S => IsUnit (f.left.appTop (normalizedPivotSection a b S)))
      (q := fun Q : {Q : Matrix ι ν Γ(T.left, ⊤) // Matrices.Grassmannian.IsNormalized a Q} =>
        IsUnit (Matrices.Grassmannian.selectedColumns b Q.val).det)
      (fun f => normalizedPivotSection_unit_iff a b S f)).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter (Matrices.Grassmannian.IsNormalized a)
        (fun Q : Matrix ι ν Γ(T.left, ⊤) => IsUnit (Matrices.Grassmannian.selectedColumns b Q).det)))

theorem normalizedOverlapSchemePointEquiv_val {T : Over S}
    (f : T ⟶ normalizedChartOverlap a b S) :
    (normalizedOverlapSchemePointEquiv a b S T f).val =
      ((Chart.Grassmannian.normalizedChartRepresentation a S).hom.app (.op T)
        (f ≫ normalizedOverlapInclusion a b S)).val := rfl

def normalizedOverlapRepresentation :
    yoneda.obj (normalizedChartOverlap a b S) ≅
      (OverlapFunctor.Grassmannian.normalizedOverlapSubfunctor a b S).toFunctor :=
  NatIso.ofComponents (fun T => (normalizedOverlapSchemePointEquiv a b S T.unop).toIso) (by
    intro T U f
    apply ConcreteCategory.hom_ext
    intro g
    apply Subtype.ext
    change (normalizedOverlapSchemePointEquiv a b S U.unop (f.unop ≫ g)).val =
      (normalizedOverlapSchemePointEquiv a b S T.unop g).val.map f.unop.left.appTop.hom
    rw [normalizedOverlapSchemePointEquiv_val, normalizedOverlapSchemePointEquiv_val,
      Chart.Grassmannian.normalizedChartRepresentation_apply, Chart.Grassmannian.normalizedChartRepresentation_apply]
    rfl)

theorem normalizedOverlapRepresentation_inclusion :
    (normalizedOverlapRepresentation a b S).hom ≫ OverlapFunctor.Grassmannian.normalizedOverlapForget a b S =
      yoneda.map (normalizedOverlapInclusion a b S) ≫
        (Chart.Grassmannian.normalizedChartRepresentation a S).hom := rfl

def normalizedOverlapTransition : normalizedChartOverlap a b S ≅ normalizedChartOverlap b a S :=
  yoneda.preimageIso (normalizedOverlapRepresentation a b S ≪≫ OverlapFunctor.Grassmannian.normalizedOverlapSwap a b S ≪≫
    (normalizedOverlapRepresentation b a S).symm)

theorem normalizedOverlapTransition_representation :
    yoneda.map (normalizedOverlapTransition a b S).hom ≫
        (normalizedOverlapRepresentation b a S).hom =
      (normalizedOverlapRepresentation a b S).hom ≫ (OverlapFunctor.Grassmannian.normalizedOverlapSwap a b S).hom := by
  simp [normalizedOverlapTransition]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.Overlap.Grassmannian
