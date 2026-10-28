import OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.LocalIsolation
import OAI.AlgebraicGeometry.CycleClass.Thom.Integral.SupportedProduct
import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Intersection

/-! # Supported Product -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.SupportedProduct.Constructions

noncomputable section

/-! The actual product-support cycle class restricts along the actual
projective diagonal to the supported cup of the original factor classes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.LocalIsolation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Integral.SupportedProduct.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductPointRanges.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Intersection.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProductRestriction.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ThomOpenRestriction.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

def diagonalPointMap : TopCat.of V.analyticSpace ⟶ TopCat.of (Ambient.Constructions.productVariety V V).analyticSpace :=
  TopCat.ofHom ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Ambient.Constructions.diagonal V), ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map (Ambient.Constructions.diagonal V)⟩

theorem diagonalProduct_square :
    diagonalPointMap V ≫ Integral.SupportedProduct.Constructions.ambientProductMap V V (Ambient.Constructions.productVariety V V) (Ambient.Constructions.first V V) (Ambient.Constructions.second V V) (Ambient.Constructions.productLimit V V) =
      ImageIntersectionCup.Constructions.diagonalMap (TopCat.of V.analyticSpace) := by
  ext x : 1
  apply Prod.ext
  · change (x ≫ Ambient.Constructions.diagonal V) ≫ Ambient.Constructions.first V V = x
    rw [Category.assoc, Ambient.Constructions.diagonal_first, Category.comp_id]
  · change (x ≫ Ambient.Constructions.diagonal V) ≫ Ambient.Constructions.second V V = x
    rw [Category.assoc, Ambient.Constructions.diagonal_second, Category.comp_id]

variable (p q : ℕ) (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport V q)

theorem diagonalProduct_support :
    diagonalPointMap V ⁻¹' Set.range (LocalIsolation.Constructions.pairedSupport V p q A B).analyticInclusion =
      Set.range A.analyticInclusion ∩ Set.range B.analyticInclusion := by
  rw [LocalIsolation.Constructions.pairedSupport, Integral.ProductPointRanges.Constructions.integralProductSupport_range]
  ext x
  change ((x ≫ Ambient.Constructions.diagonal V) ≫ Ambient.Constructions.first V V ∈ Set.range A.analyticInclusion ∧
    (x ≫ Ambient.Constructions.diagonal V) ≫ Ambient.Constructions.second V V ∈ Set.range B.analyticInclusion) ↔ _
  rw [Category.assoc, Category.assoc, Ambient.Constructions.diagonal_first, Ambient.Constructions.diagonal_second, Category.comp_id]
  rfl

theorem diagonalProduct_mapsTo : Set.MapsTo (diagonalPointMap V)
    (Set.range A.analyticInclusion ∩ Set.range B.analyticInclusion)ᶜ
    (Set.range (LocalIsolation.Constructions.pairedSupport V p q A B).analyticInclusion)ᶜ := by
  intro x hx hy
  exact hx ((Set.ext_iff.mp (diagonalProduct_support V p q A B) x).mp hy)

theorem supportedProduct_diagonal :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (diagonalPointMap V)
      (diagonalProduct_mapsTo V p q A B) (2 * (p + q))
      (LocalIsolation.Constructions.pairedSupport V p q A B).rationalSupportedCycleClass = Supported.Intersection.Constructions.Class.supportedIntersectionClass A B := by
  rw [← Integral.SupportedProduct.Constructions.integralSupportedProductClass_eq_cycleClass V V (Ambient.Constructions.productVariety V V)
    (Ambient.Constructions.first V V) (Ambient.Constructions.second V V) (Ambient.Constructions.productLimit V V) p q A B]
  have h := ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
    (diagonalPointMap V) (Integral.SupportedProduct.Constructions.ambientProductMap V V (Ambient.Constructions.productVariety V V) (Ambient.Constructions.first V V) (Ambient.Constructions.second V V) (Ambient.Constructions.productLimit V V))
    (diagonalProduct_mapsTo V p q A B)
    (Integral.SupportedProduct.Constructions.ambientProductMap_mapsTo V V (Ambient.Constructions.productVariety V V) (Ambient.Constructions.first V V) (Ambient.Constructions.second V V) (Ambient.Constructions.productLimit V V) p q A B)
    (2 * (p + q))) (Supported.ProductRestriction.Constructions.supportedExteriorCycleClass A B)
  simp only [ConcreteCategory.comp_apply] at h
  exact h.trans (ConcreteCategory.congr_hom
    (ThomOpenRestriction.Constructions.pairMap_congr (diagonalProduct_square V) _ (ImageIntersectionCup.Constructions.diagonalMap_complement A.analyticInclusion B.analyticInclusion)
      (2 * (p + q))) (Supported.ProductRestriction.Constructions.supportedExteriorCycleClass A B))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.SupportedProduct.Constructions
