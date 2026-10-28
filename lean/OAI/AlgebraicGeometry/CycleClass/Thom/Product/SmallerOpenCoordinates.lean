import OAI.AlgebraicGeometry.CycleClass.Thom.Open.ProductHomeomorphAnalytic
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.SubsetHomeomorph
import OAI.AlgebraicTopology.Kunneth.ProductModelsAs

/-! # Smaller Open Coordinates -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Product.SmallerOpenCoordinates.Constructions

noncomputable section

/-! The actual product map of a nested ambient-open inclusion is the inverse coordinate map from the corresponding open subset of the larger product. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Open.ProductHomeomorphAnalytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.SubsetHomeomorph.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {N G F : Type} [TopologicalSpace N]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace G N]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  (U P : Opens N) (hP : P ≤ U)

local instance (priority := low) (V : Opens N) : ChartedSpace (G × F) (V × F) := prodChartedSpace G V F F
local instance (priority := low) : ChartedSpace (G × F) (Open.SubsetHomeomorph.Constructions.insideOpen U P × F) :=
  prodChartedSpace G (Open.SubsetHomeomorph.Constructions.insideOpen U P) F F

def smallerProductHomeomorph : Open.ProductHomeomorphAnalytic.Constructions.productBaseOpen (F := F) (Open.SubsetHomeomorph.Constructions.insideOpen U P) ≃ₜ (P × F) :=
  (Open.ProductHomeomorphAnalytic.Constructions.openBaseProductHomeomorph (Open.SubsetHomeomorph.Constructions.insideOpen U P)).trans
    ((Open.SubsetHomeomorph.Constructions.smallerOpenHomeomorph U P hP).prodCongr (Homeomorph.refl F))

theorem smallerProductHomeomorph_analytic :
    ContMDiff 𝓘(ℂ, G × F) 𝓘(ℂ, G × F) ω (smallerProductHomeomorph (F := F) U P hP) := by
  have hp : ContMDiff 𝓘(ℂ, G × F) 𝓘(ℂ, G × F) ω
      ((Open.SubsetHomeomorph.Constructions.smallerOpenHomeomorph U P hP).prodCongr (Homeomorph.refl F)) := by
    simp only [modelWithCornersSelf_prod]
    exact (Open.SubsetHomeomorph.Constructions.smallerOpenHomeomorph_analytic (G := G) U P hP).prodMap
      (show ContMDiff 𝓘(ℂ, F) 𝓘(ℂ, F) ω id from contMDiff_id)
  exact hp.comp (Open.ProductHomeomorphAnalytic.Constructions.baseProductHomeomorph_analytic (G := G) (F := F) (Open.SubsetHomeomorph.Constructions.insideOpen U P))

theorem smallerProductHomeomorph_symm_analytic :
    ContMDiff 𝓘(ℂ, G × F) 𝓘(ℂ, G × F) ω (smallerProductHomeomorph (F := F) U P hP).symm := by
  have hp : ContMDiff 𝓘(ℂ, G × F) 𝓘(ℂ, G × F) ω
      ((Open.SubsetHomeomorph.Constructions.smallerOpenHomeomorph U P hP).symm.prodCongr (Homeomorph.refl F)) := by
    simp only [modelWithCornersSelf_prod]
    exact (Open.SubsetHomeomorph.Constructions.smallerOpenHomeomorph_symm_analytic (G := G) U P hP).prodMap
      (show ContMDiff 𝓘(ℂ, F) 𝓘(ℂ, F) ω id from contMDiff_id)
  exact (Open.ProductHomeomorphAnalytic.Constructions.baseProductHomeomorph_symm_analytic (G := G) (F := F) (Open.SubsetHomeomorph.Constructions.insideOpen U P)).comp hp

def smallerProductMap : TopCat.of (P × F) ⟶ TopCat.of (U × F) :=
  AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((Open.SubsetHomeomorph.Constructions.smallerOpenMap U P hP, 𝟙 (TopCat.of F)) :
    (TopCat.of P, TopCat.of F) ⟶ (TopCat.of U, TopCat.of F))

omit [NormedSpace ℂ F] in
theorem smallerProductMap_eq_transported : smallerProductMap (F := F) U P hP =
    Open.ImageComplement.Constructions.ThomAmbientTransport.transportedOpenMap (Open.ProductHomeomorphAnalytic.Constructions.productBaseOpen (Open.SubsetHomeomorph.Constructions.insideOpen U P)) (smallerProductHomeomorph (F := F) U P hP) := rfl

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Product.SmallerOpenCoordinates.Constructions
