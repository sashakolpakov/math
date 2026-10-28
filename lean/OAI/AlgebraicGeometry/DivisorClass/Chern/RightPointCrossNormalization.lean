import OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.Models
import OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.RightPointCross

/-! # Right Point Cross Normalization -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.RightPointCrossNormalization

noncomputable section

/-! The original cross product with a right-hand point is chain homotopic
to the actual inclusion at that point, by native simplex-model uniqueness. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type) [Field k]

theorem unitRightPointProjection_zero (X : TopCat.{0}) :
    (Singular.RightPointCross.unitRightPointProjection k X).f 0 = 𝟙 (((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X).X 0) := by
  apply ModuleCat.hom_ext
  apply AlgebraicTopology.Cohomology.Singular.ChainDual.chainFunctional_ext (TopCat.toSSet.obj X) (((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X).X 0)
  intro s
  change ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map (TopCat.prodFst (X := X) (Y := TopCat.of Unit))).f 0
    (((AlgebraicTopology.Kunneth.ComparisonLow.Construction.EilenbergZilber.cross k).f 0).app (X, TopCat.of Unit)
      (ιTensorObj ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X) ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj (TopCat.of Unit))
        0 0 0 rfl (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X) s ⊗ₜ[k]
          Singular.CrossBoundary.scalarPointChain k (TopCat.of Unit) ()))) = AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X) s
  rw [AlgebraicTopology.Kunneth.ComparisonLow.Construction.EilenbergZilber.cross_f_zero, Singular.CrossBoundary.scalarPointChain,
    AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.zeroComparison_simplex]
  exact AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains_map_simplex k (TopCat.prodFst (X := X) (Y := TopCat.of Unit)) 0 _

def unitRightPointNaturalEndomorphism : Singular.Models.singularNaturalChains k ⟶ Singular.Models.singularNaturalChains k where
  f n :=
    { app X := (Singular.RightPointCross.unitRightPointProjection k X).f n
      naturality X Y f := congrArg (fun u => u.f n) (Singular.RightPointCross.unitRightPointProjection_naturality k f) }
  comm' i j _ := by
    apply NatTrans.ext
    funext X
    exact (Singular.RightPointCross.unitRightPointProjection k X).comm i j

def unitRightPointNaturalHomotopy :
    Homotopy (unitRightPointNaturalEndomorphism k) (𝟙 (Singular.Models.singularNaturalChains k)) :=
  Singular.Models.singularNaturalHomotopy k _ _ (by
    apply NatTrans.ext
    funext X
    exact unitRightPointProjection_zero k X)

def unitRightPointProjectionHomotopy (X : TopCat.{0}) :
    Homotopy (Singular.RightPointCross.unitRightPointProjection k X) (𝟙 ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X)) :=
  ((evaluation TopCat.{0} (ModuleCat.{0} k)).obj X).mapHomotopy (unitRightPointNaturalHomotopy k)

def unitRightPointCrossHomotopy (X : TopCat.{0}) :
    Homotopy (Singular.RightPointCross.singularRightPointCross k X (TopCat.of Unit) ())
      ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map (Singular.RightPointCross.rightPointProductInclusion X (TopCat.of Unit) ())) := by
  have hp : (TopCat.prodFst (X := X) (Y := TopCat.of Unit)) ≫
      Singular.RightPointCross.rightPointProductInclusion X (TopCat.of Unit) () = 𝟙 (TopCat.of (X × Unit)) := by
    apply TopCat.ext
    intro x
    exact Prod.ext rfl (Subsingleton.elim _ _)
  have h := (unitRightPointProjectionHomotopy k X).compRightId
    ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map (Singular.RightPointCross.rightPointProductInclusion X (TopCat.of Unit) ()))
  dsimp only [Singular.RightPointCross.unitRightPointProjection] at h
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, hp,
    CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact h

def singularRightPointCrossHomotopy (X Y : TopCat.{0}) (y : Y) :
    Homotopy (Singular.RightPointCross.singularRightPointCross k X Y y)
      ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map (Singular.RightPointCross.rightPointProductInclusion X Y y)) := by
  let f : TopCat.of Unit ⟶ Y := TopCat.ofHom ⟨fun _ => y, continuous_const⟩
  let g := AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((𝟙 X, f) : (X, TopCat.of Unit) ⟶ (X, Y))
  have h := (unitRightPointCrossHomotopy k X).compRight ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map g)
  have hn := Singular.RightPointCross.singularRightPointCross_naturality k (𝟙 X) f ()
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at hn
  change Singular.RightPointCross.singularRightPointCross k X (TopCat.of Unit) () ≫ (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map g =
    Singular.RightPointCross.singularRightPointCross k X Y y at hn
  rw [hn, ← CategoryTheory.Functor.map_comp] at h
  exact h

theorem singularRightPointCross_homology (X Y : TopCat.{0}) (y : Y) (n : ℕ) :
    homologyMap (Singular.RightPointCross.singularRightPointCross k X Y y) n =
      homologyMap ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map (Singular.RightPointCross.rightPointProductInclusion X Y y)) n :=
  (singularRightPointCrossHomotopy k X Y y).homologyMap_eq n

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.RightPointCrossNormalization
