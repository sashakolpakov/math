import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ColumnTopEdgeDegree
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleTopEdge

/-! # Single Top Edge Degree -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleTopEdgeDegree

noncomputable section

/-! Functorial single-degree coordinates followed by a bicomplex map
are the original top-row edge with the sign in every bidegree. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w z
variable {C : Type u} [Category.{v} C] [Abelian C]
  {R : Type w} [CommRing R]
  (F : C ⥤ CochainComplex (ModuleCat.{z} R) ℕ) [F.Additive]
  (M : C) (c n : ℕ)

theorem inverse_coordinate (x : (F.obj M).homology n) :
    (SingleTotal.homologyIso F M c n).inv x =
      ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) c n •
        Single.ColumnTopEdgeDegree.Row.mapTo (SingleTotal.bicomplex F M c) c
          (SingleTopEdge.outgoing F M c) n (n+c) (Nat.add_comm c n)
          (homologyMap (SingleTotal.rowIso F M c).inv n x) := by
  change (Single.ColumnCycleCoordinates.homologyIso
    (SingleTotal.bicomplex F M c) c
    (SingleTotal.off_degree F M c) n).inv
      (homologyMap (SingleTotal.rowIso F M c).inv n x) = _
  exact Single.ColumnTopEdgeDegree.inv_apply (SingleTotal.bicomplex F M c) c
    (SingleTotal.off_degree F M c) (SingleTopEdge.outgoing F M c) n _

variable (L : HomologicalComplex₂ (ModuleCat.{z} R) (.up ℕ) (.up ℕ))
  (hL : ∀ q, (L.d c (c+1)).f q = 0)
  (a : SingleTotal.bicomplex F M c ⟶ L)

theorem map_apply (x : (F.obj M).homology n) :
    homologyMap (HomologicalComplex₂.total.map a (.up ℕ)) (n+c)
      ((SingleTotal.homologyIso F M c n).inv x) =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) c n •
      Single.ColumnTopEdgeDegree.Row.mapTo L c hL n (n+c) (Nat.add_comm c n)
        (homologyMap ((SingleTotal.rowIso F M c).inv ≫ a.f c) n x) := by
  rw [inverse_coordinate F M c n x]
  simp only [Units.smul_def, map_zsmul]
  rw [Single.ColumnTopEdgeDegree.Row.naturality (SingleTotal.bicomplex F M c) c
    (SingleTopEdge.outgoing F M c) L hL a n (n+c) (Nat.add_comm c n)]
  rw [homologyMap_comp]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleTopEdgeDegree
