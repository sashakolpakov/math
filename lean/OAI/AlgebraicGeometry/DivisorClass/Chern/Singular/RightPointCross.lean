import OAI.AlgebraicGeometry.DivisorClass.Chern.TensorPoint
import OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.CrossBoundary

/-! # Right Point Cross -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.RightPointCross

noncomputable section

/-! The original singular cross product with an actual point in the right factor. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type) [Field k]

def singularRightPointCross (X Y : TopCat.{0}) (y : Y) :
    (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X ⟶ (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj (TopCat.of (X × Y)) :=
  TensorPoint.tensorRightPointChain ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X) ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y) (CrossBoundary.scalarPointChain k Y y) ≫
    HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.singularChainCross k X Y

theorem singularRightPointCross_naturality {X X' Y Y' : TopCat.{0}}
    (f : X ⟶ X') (g : Y ⟶ Y') (y : Y) :
    singularRightPointCross k X Y y ≫ (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map
        (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, g) : (X, Y) ⟶ (X', Y'))) =
      (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map f ≫ singularRightPointCross k X' Y' (g y) := by
  unfold singularRightPointCross
  rw [Category.assoc, ← HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.singularChainCross_naturality, ← Category.assoc,
    TensorPoint.tensorRightPointChain_naturality, CrossBoundary.scalarPointChain_map, Category.assoc]

def rightPointProductInclusion (X Y : TopCat.{0}) (y : Y) : X ⟶ TopCat.of (X × Y) :=
  TopCat.ofHom ⟨fun x => (x, y), continuous_id.prodMk continuous_const⟩

def unitRightPointProjection (X : TopCat.{0}) : (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X ⟶ (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X :=
  singularRightPointCross k X (TopCat.of Unit) () ≫ (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map TopCat.prodFst

theorem unitRightPointProjection_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) :
    (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map f ≫ unitRightPointProjection k Y =
      unitRightPointProjection k X ≫ (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map f := by
  have hn := singularRightPointCross_naturality k f (𝟙 (TopCat.of Unit)) ()
  change singularRightPointCross k X (TopCat.of Unit) () ≫ (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map
      (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, 𝟙 (TopCat.of Unit)) : (X, TopCat.of Unit) ⟶ (Y, TopCat.of Unit))) =
    (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map f ≫ singularRightPointCross k Y (TopCat.of Unit) () at hn
  unfold unitRightPointProjection
  rw [← Category.assoc, ← hn, Category.assoc, ← CategoryTheory.Functor.map_comp,
    Category.assoc, ← CategoryTheory.Functor.map_comp]
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.RightPointCross
