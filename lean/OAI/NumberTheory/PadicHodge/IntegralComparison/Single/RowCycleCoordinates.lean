import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.ShiftZeroCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.AbelianSingleRowTotal

/-! # Row Cycle Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Single.RowCycleCoordinates

noncomputable section

/-! The original single-row total comparison preserves every cycle
coordinate, with the actual cohomological shift. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{0} C]
  (B : HomologicalComplex₂ C (.up ℕ) (.up ℕ))
  (c : ℕ) (hB : ∀ p q, q ≠ c → IsZero ((B.X p).X q))

def cycleProjection (n : ℕ) : (B.total (.up ℕ)).cycles (n+c) ⟶ (B.flip.X c).cycles n := by
  letI := AbelianSingleRowTotal.supported B c hB
  exact Supported.ShiftZeroCoordinates.cyclesCoordinate (B.total (.up ℕ)) c n ≫
    cyclesMap (AbelianSingleRowTotal.restrictionIso B c hB).inv n

theorem homologyπ_coordinate (n : ℕ) :
    (B.total (.up ℕ)).homologyπ (n+c) ≫ (AbelianSingleRowTotal.homologyIso B c hB n).hom =
      cycleProjection B c hB n ≫ (B.flip.X c).homologyπ n := by
  let := AbelianSingleRowTotal.supported B c hB
  dsimp only [AbelianSingleRowTotal.homologyIso, Iso.trans_hom, Iso.symm_hom,
    homologyMapIso_inv, cycleProjection]
  rw [← Category.assoc, Supported.ShiftZeroCoordinates.homologyπ_coordinate,
    Category.assoc, homologyπ_naturality, Category.assoc]

theorem cycleProjection_i (n : ℕ) :
    cycleProjection B c hB n ≫ (B.flip.X c).iCycles n =
      (B.total (.up ℕ)).iCycles (n+c) ≫ AbelianSingleRowTotal.projection B n c (n+c) rfl := by
  let := AbelianSingleRowTotal.supported B c hB
  dsimp only [cycleProjection]
  rw [Category.assoc, cyclesMap_i, ← Category.assoc,
    Supported.ShiftZeroCoordinates.cyclesCoordinate_i]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Single.RowCycleCoordinates
