import OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.SupportedProduct
import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.SupportAnalyticImage

/-! # Analytic Image -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.AnalyticImage.Constructions

noncomputable section

/-! Diagonal images of cycles have their original analytic image and
singular boundary, without changing the reduced support. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.SupportedProduct.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Closed.SupportAnalyticImage.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) (Z : Geometric.DimensionCycles.DimensionCycleSupport V p)

local instance : LocallyOfFiniteType V.toOver.hom := inferInstanceAs (LocallyOfFiniteType V.structureMap)
local instance : Smooth (Ambient.Constructions.productVariety V V).toOver.hom := (Ambient.Constructions.productVariety V V).presentation.smooth
local instance : LocallyOfFiniteType (Ambient.Constructions.productVariety V V).toOver.hom :=
  inferInstance

theorem diagonalCycle_support :
    Scheme.ProperSupport.Constructions.imageSupport (Ambient.Constructions.diagonal V) Z.val = (Ambient.Constructions.diagonalSupport V p Z).val :=
  ProperImage.SupportMap.Constructions.Construction.supportMap_imageClosure (Ambient.Constructions.diagonal V) inferInstance Z

theorem diagonalCycle_range :
    Set.range (Ambient.Constructions.diagonalSupport V p Z).analyticInclusion = Set.range (SupportedProduct.Constructions.diagonalPointMap V ∘ Z.analyticInclusion) := by
  have h := Closed.SupportAnalyticImage.Constructions.supportImage_range (Ambient.Constructions.diagonal V) Z.val
  rw [diagonalCycle_support V p Z] at h
  exact h

theorem diagonalCycle_boundary :
    (Ambient.Constructions.diagonalSupport V p Z).analyticSingularBoundary = SupportedProduct.Constructions.diagonalPointMap V '' Z.analyticSingularBoundary := by
  have h := Closed.SupportAnalyticImage.Constructions.analyticBoundary_image (Ambient.Constructions.diagonal V) Z.val
  rw [diagonalCycle_support V p Z] at h
  exact h

theorem diagonalCycle_regular_preimage (x : V.analyticSpace)
    (hx : SupportedProduct.Constructions.diagonalPointMap V x ∈ (Ambient.Constructions.diagonalSupport V p Z).regularAmbientOpen) : x ∈ Z.regularAmbientOpen := by
  intro hb
  exact hx (diagonalCycle_boundary V p Z ▸ Set.mem_image_of_mem (SupportedProduct.Constructions.diagonalPointMap V) hb)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.AnalyticImage.Constructions
