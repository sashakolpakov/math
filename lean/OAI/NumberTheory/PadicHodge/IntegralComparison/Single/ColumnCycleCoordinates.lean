import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.RowCycleCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleTotal

/-! # Column Cycle Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ColumnCycleCoordinates

noncomputable section

/-! Cycle coordinates of the original one-column total comparison,
including the actual sign of the total flip in every bidegree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{0} C]
  (B : HomologicalComplex₂ C (.up ℕ) (.up ℕ))

theorem flip_projection (c n : ℕ) :
    (B.totalFlipIso (.up ℕ)).inv.f (n+c) ≫
      AbelianSingleRowTotal.projection B.flip n c (n+c) rfl =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) c n •
      AbelianSingleRowTotal.projection B c n (n+c) (by omega) := by
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  rw [← Category.assoc, B.ιTotal_totalFlipIso_f_inv]
  by_cases hp : p = c
  · subst p
    have hq : q = n := by change c+q=n+c at hpq; omega
    subst q
    simp [AbelianSingleRowTotal.projection]
  · simp [AbelianSingleRowTotal.projection, hp]

variable (c : ℕ) (hB : ∀ p q, q ≠ c → IsZero ((B.flip.X p).X q))

def homologyIso (n : ℕ) : (B.total (.up ℕ)).homology (n+c) ≅ (B.X c).homology n :=
  (homologyMapIso (B.totalFlipIso (.up ℕ)) (n+c)).symm ≪≫
    AbelianSingleRowTotal.homologyIso B.flip c hB n

def cycleProjection (n : ℕ) : (B.total (.up ℕ)).cycles (n+c) ⟶ (B.X c).cycles n :=
  cyclesMap (B.totalFlipIso (.up ℕ)).inv (n+c) ≫
    RowCycleCoordinates.cycleProjection B.flip c hB n

theorem homologyπ_coordinate (n : ℕ) :
    (B.total (.up ℕ)).homologyπ (n+c) ≫ (homologyIso B c hB n).hom =
      cycleProjection B c hB n ≫ (B.X c).homologyπ n := by
  dsimp only [homologyIso, Iso.trans_hom, Iso.symm_hom, homologyMapIso_inv, cycleProjection]
  rw [← Category.assoc, homologyπ_naturality, Category.assoc,
    RowCycleCoordinates.homologyπ_coordinate, Category.assoc]
  rfl

theorem cycleProjection_i (n : ℕ) :
    cycleProjection B c hB n ≫ (B.X c).iCycles n =
      (B.total (.up ℕ)).iCycles (n+c) ≫
        (ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) c n •
          AbelianSingleRowTotal.projection B c n (n+c) (by omega)) := by
  dsimp only [cycleProjection]
  erw [Category.assoc, RowCycleCoordinates.cycleProjection_i B.flip c hB n,
    ← Category.assoc, cyclesMap_i, Category.assoc, flip_projection]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ColumnCycleCoordinates
