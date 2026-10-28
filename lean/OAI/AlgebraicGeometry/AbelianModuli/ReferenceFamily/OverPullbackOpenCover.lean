import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.OverPullbackCartesianMap
import Mathlib.AlgebraicGeometry.Cover.Open

/-! # Over Pullback Open Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.OverPullbackOpenCover

noncomputable section

/-! Base change of an actual family of open immersions preserves its
covering property, with the same indices and the literal functor maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

local instance overPullbackOpenCover_mapOpen {B C : Scheme} (f : B ⟶ C)
    {X Y : Over C} (i : X ⟶ Y) [IsOpenImmersion i.left] :
    IsOpenImmersion ((Over.pullback f).map i).left := OverPullbackCartesianMap.overPullback_map_open f i

theorem overPullback_map_opensRange {B C : Scheme} (f : B ⟶ C)
    {X Y : Over C} (i : X ⟶ Y) [IsOpenImmersion i.left] :
    (((Over.pullback f).map i).left).opensRange = (pullback.fst Y.hom f) ⁻¹ᵁ i.left.opensRange := by
  have := OverPullbackCartesianMap.overPullback_map_open f i
  have h := OverPullbackCartesianMap.overPullback_map_isPullback f i
  apply TopologicalSpace.Opens.ext
  change Set.range (((Over.pullback f).map i).left) = _
  have hr : Set.range h.isoPullback.hom = Set.univ :=
    Set.range_eq_univ.mpr h.isoPullback.schemeIsoToHomeo.surjective
  rw [← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    hr, Set.image_univ]
  exact IsOpenImmersion.range_pullbackFst i.left (pullback.fst Y.hom f)

def overPullbackOpenCover {B C : Scheme} (f : B ⟶ C) {I : Type*} {Y : Over C}
    (A : I → Over C) (i : ∀ j, A j ⟶ Y) [∀ j, IsOpenImmersion (i j).left]
    (h : ∀ y : Y.left, ∃ j, y ∈ (i j).left.opensRange) : ((Over.pullback f).obj Y).left.OpenCover where
  I₀ := I
  X j := ((Over.pullback f).obj (A j)).left
  f j := ((Over.pullback f).map (i j)).left
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, ?_⟩
    · intro y
      obtain ⟨j, hj⟩ := h (pullback.fst Y.hom f y)
      refine ⟨j, ?_⟩
      change y ∈ (((Over.pullback f).map (i j)).left).opensRange
      rw [overPullback_map_opensRange]
      exact hj
    · intro j
      exact OverPullbackCartesianMap.overPullback_map_open f (i j)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.OverPullbackOpenCover
