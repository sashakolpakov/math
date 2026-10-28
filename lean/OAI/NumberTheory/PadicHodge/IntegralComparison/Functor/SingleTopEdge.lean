import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ColumnTopEdge
import OAI.NumberTheory.PadicHodge.IntegralComparison.TopRowEdgeNaturality

/-! # Single Top Edge -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleTopEdge

noncomputable section

/-! The original single-column comparison, followed by a map of double
complexes, is the target top-row edge with the actual total-flip sign. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w z
variable {C : Type u} [Category.{v} C] [Abelian C]
  {R : Type w} [CommRing R]
  (F : C ⥤ CochainComplex (ModuleCat.{z} R) ℕ) [F.Additive]
  (M : C) (c : ℕ)

theorem outgoing (q : ℕ) :
    ((SingleTotal.bicomplex F M c).d c (c+1)).f q = 0 :=
  (SingleTotal.off_degree F M c q (c+1) (by omega)).eq_of_tgt _ _

theorem inverse_coordinate (x : (F.obj M).homology c) :
    (SingleTotal.homologyIso F M c c).inv x =
      ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) c c •
        TopRowEdge.map (SingleTotal.bicomplex F M c) c
          (outgoing F M c) c
          (homologyMap (SingleTotal.rowIso F M c).inv c x) := by
  change (Single.ColumnCycleCoordinates.homologyIso
    (SingleTotal.bicomplex F M c) c
    (SingleTotal.off_degree F M c) c).inv
      (homologyMap (SingleTotal.rowIso F M c).inv c x) = _
  exact Single.ColumnTopEdge.inv_apply (SingleTotal.bicomplex F M c) c
    (SingleTotal.off_degree F M c) (outgoing F M c) _

variable (L : HomologicalComplex₂ (ModuleCat.{z} R) (.up ℕ) (.up ℕ))
  (hL : ∀ q, (L.d c (c+1)).f q = 0)
  (a : SingleTotal.bicomplex F M c ⟶ L)

theorem map_apply (x : (F.obj M).homology c) :
    homologyMap (HomologicalComplex₂.total.map a (.up ℕ)) (c+c)
      ((SingleTotal.homologyIso F M c c).inv x) =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) c c •
      TopRowEdge.map L c hL c
        (homologyMap ((SingleTotal.rowIso F M c).inv ≫ a.f c) c x) := by
  rw [inverse_coordinate F M c x]
  simp only [Units.smul_def, map_zsmul]
  rw [TopRowEdgeNaturality.naturality (SingleTotal.bicomplex F M c) L c
    (outgoing F M c) hL a c]
  rw [homologyMap_comp]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleTopEdge
