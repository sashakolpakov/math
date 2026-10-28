import OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.AnalyticImage
import OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenProduct

/-! # Intersection Support -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.IntersectionSupport.Constructions

noncomputable section

/-! The original generic-point incidence supplies the analytic support
containments required by the local diagonal Serre formula. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.LocalIsolation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.SupportedProduct.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.AnalyticImage.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenProduct.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.Supports

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

theorem analyticSupport_subset_of_generic {p d : ℕ} (A : Geometric.DimensionCycles.DimensionCycleSupport V p)
    (Z : Geometric.DimensionCycles.DimensionCycleSupport V d) (hx : IntersectionGeometry.supportPoint Z.val ∈ (A.val : Set V.carrier)) :
    Set.range Z.analyticInclusion ⊆ Set.range A.analyticInclusion := by
  rw [Z.range_analyticInclusion, A.range_analyticInclusion]
  have h := (Intersection.Supports.supportPoint_mem_iff_subset (⟨A.val, A.val.isClosed⟩ : Closeds V.carrier) Z.val).mp hx
  exact fun _ hz => h hz

variable (p q : ℕ) (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport V q)
  (Z : Geometric.DimensionCycles.DimensionCycleSupport V (p + q))
  (hxA : IntersectionGeometry.supportPoint Z.val ∈ (A.val : Set V.carrier))
  (hxB : IntersectionGeometry.supportPoint Z.val ∈ (B.val : Set V.carrier))

include hxA hxB in
theorem diagonalCycle_subset_product :
    Set.range (Ambient.Constructions.diagonalSupport V (p + q) Z).analyticInclusion ⊆ Set.range (LocalIsolation.Constructions.pairedSupport V p q A B).analyticInclusion := by
  rw [AnalyticImage.Constructions.diagonalCycle_range]
  rintro _ ⟨z, rfl⟩
  apply (Set.ext_iff.mp (SupportedProduct.Constructions.diagonalProduct_support V p q A B) (Z.analyticInclusion z)).mpr
  exact ⟨analyticSupport_subset_of_generic V A Z hxA (Set.mem_range_self z),
    analyticSupport_subset_of_generic V B Z hxB (Set.mem_range_self z)⟩

include hxA hxB in
theorem diagonalCycle_pairedOpen_supported (U : Opens (Ambient.Constructions.productVariety V V).analyticSpace) :
    (Subtype.val : U → (Ambient.Constructions.productVariety V V).analyticSpace) ⁻¹' Set.range (Ambient.Constructions.diagonalSupport V (p + q) Z).analyticInclusion ⊆
      Set.range (OpenProduct.Constructions.Class.pairedOpenInclusion V p q A B U) := by
  rw [OpenProduct.Constructions.Class.pairedOpenInclusion_range]
  exact fun _ hz => diagonalCycle_subset_product V p q A B Z hxA hxB hz

theorem diagonalCycle_regular_iff (x : V.analyticSpace) :
    SupportedProduct.Constructions.diagonalPointMap V x ∈ (Ambient.Constructions.diagonalSupport V (p + q) Z).regularAmbientOpen ↔ x ∈ Z.regularAmbientOpen := by
  change SupportedProduct.Constructions.diagonalPointMap V x ∉ (Ambient.Constructions.diagonalSupport V (p + q) Z).analyticSingularBoundary ↔ x ∉ Z.analyticSingularBoundary
  rw [AnalyticImage.Constructions.diagonalCycle_boundary]
  constructor
  · exact fun h hx => h ⟨x, hx, rfl⟩
  · rintro h ⟨y, hy, he⟩
    exact h ((ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion (Ambient.Constructions.diagonal V)).injective he ▸ hy)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.IntersectionSupport.Constructions
