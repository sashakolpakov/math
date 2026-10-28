import OAI.AlgebraicGeometry.CycleClass.Geometric.NormalChartPurity

/-! # Change Source -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.ChangeSource.Constructions

noncomputable section

/-! A normal pair depends on its actual embedded image in the
neighborhood. Replacing its source by a map with the same local image
retains the original coordinate map and normal orientation. -/

open _root_.TopologicalSpace

variable {M L N E F : Type} [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)
  (g : L → N) (y : L) (hy : g y = f x)
  (hfg : ∀ z ∈ P.neighborhood, z ∈ Set.range g ↔ z ∈ Set.range f)

def changeSource : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F g y where
  radius := P.radius
  radius_pos := P.radius_pos
  ambientChart := P.ambientChart
  product_subset_target := P.product_subset_target
  point_mem_source := hy.symm ▸ P.point_mem_source
  point_coordinates := hy.symm ▸ P.point_coordinates
  range_iff := fun z hz => (hfg z hz).trans (P.range_iff z hz)

theorem changeSource_normalCoordinate :
    (changeSource P g y hy hfg).normalCoordinate = P.normalCoordinate := rfl

theorem changeSource_complement :
    (changeSource P g y hy hfg).relativeComplement = P.relativeComplement := by
  ext z
  exact not_congr (hfg z.val z.property)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.ChangeSource.Constructions
