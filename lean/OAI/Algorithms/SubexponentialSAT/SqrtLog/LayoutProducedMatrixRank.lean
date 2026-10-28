import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutZeroRows
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutRankCoordinates

namespace OAI.Algorithms

/-! Selecting columns in their physical order cannot increase the rational
rank. The map may omit or repeat columns; no runtime permutation is assumed. -/
namespace SubexponentialSAT.SqrtLog.LayoutRank
open Module LayoutExactBuckets LayoutRowSelection

variable {J K V W : Type*} [Fintype J] [Fintype K] [Fintype V] [Fintype W]

def columnSelection (e : W → V) : (V → ℚ) →ₗ[ℚ] (W → ℚ) where
  toFun := fun f w => f (e w)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

omit [Fintype J] [Fintype V] [Fintype W] in
theorem rowSpace_columns (C : J → V → ℤ) (e : W → V) :
    rowSpace (fun j w => C j (e w)) = (rowSpace C).map (columnSelection e) := by
  rw [rowSpace,rowSpace,LinearMap.map_span,←Set.range_comp]
  rfl

omit [Fintype J] [Fintype W] in
theorem rowRank_columns_le (C : J → V → ℤ) (e : W → V) :
    rowRank (fun j w => C j (e w)) ≤ rowRank C := by
  unfold rowRank
  rw [rowSpace_columns]
  exact Submodule.finrank_map_le _ _

omit [Fintype V] in
theorem rowRank_eq_of_mutual_span (C : J → V → ℤ) (A : K → V → ℤ)
    (hCA : RationalRowSpan C A) (hAC : RationalRowSpan A C) :
    rowRank C = rowRank A := by
  unfold rowRank
  rw [le_antisymm (rowSpace_le_of_rationalRowSpan C A hCA)
    (rowSpace_le_of_rationalRowSpan A C hAC)]

end SubexponentialSAT.SqrtLog.LayoutRank

end OAI.Algorithms
