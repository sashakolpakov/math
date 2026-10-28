import OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.Models
import OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.CrossBoundary

/-! # Point Cross Normalization -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.PointCrossNormalization

noncomputable section

/-!
# ChernClass: point normalization of the original singular cross product

Projection of the product with a point agrees with the identity on
vertices. The genuine simplex-model homotopy extends this equality
to homology in every degree.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type) [Field k]

theorem unitPointProjection_zero (Y : TopCat.{0}) :
    (Singular.CrossBoundary.unitPointProjection k Y).f 0 = 𝟙 (((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y).X 0) := by
  apply ModuleCat.hom_ext
  apply AlgebraicTopology.Cohomology.Singular.ChainDual.chainFunctional_ext (TopCat.toSSet.obj Y) (((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y).X 0)
  intro s
  change ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map (TopCat.prodSnd (X := TopCat.of Unit) (Y := Y))).f 0
    (((AlgebraicTopology.Kunneth.ComparisonLow.Construction.EilenbergZilber.cross k).f 0).app (TopCat.of Unit, Y)
      (ιTensorObj ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj (TopCat.of Unit)) ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y)
        0 0 0 rfl (Singular.CrossBoundary.scalarPointChain k (TopCat.of Unit) () ⊗ₜ[k]
          AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj Y) s))) =
    AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj Y) s
  rw [AlgebraicTopology.Kunneth.ComparisonLow.Construction.EilenbergZilber.cross_f_zero, Singular.CrossBoundary.scalarPointChain,
    AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.zeroComparison_simplex]
  exact AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains_map_simplex k (TopCat.prodSnd (X := TopCat.of Unit) (Y := Y)) 0 _

def unitPointNaturalEndomorphism : Singular.Models.singularNaturalChains k ⟶ Singular.Models.singularNaturalChains k where
  f n :=
    { app Y := (Singular.CrossBoundary.unitPointProjection k Y).f n
      naturality X Y f := congrArg (fun u => u.f n) (Singular.CrossBoundary.unitPointProjection_naturality k f) }
  comm' i j _ := by
    apply NatTrans.ext
    funext Y
    exact (Singular.CrossBoundary.unitPointProjection k Y).comm i j

def unitPointNaturalHomotopy :
    Homotopy (unitPointNaturalEndomorphism k) (𝟙 (Singular.Models.singularNaturalChains k)) :=
  Singular.Models.singularNaturalHomotopy k _ _ (by
    apply NatTrans.ext
    funext Y
    exact unitPointProjection_zero k Y)

def unitPointProjectionHomotopy (Y : TopCat.{0}) :
    Homotopy (Singular.CrossBoundary.unitPointProjection k Y) (𝟙 ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y)) :=
  ((evaluation TopCat.{0} (ModuleCat.{0} k)).obj Y).mapHomotopy (unitPointNaturalHomotopy k)

theorem unitPointProjection_homology (Y : TopCat.{0}) (n : ℕ) :
    homologyMap (Singular.CrossBoundary.unitPointProjection k Y) n = 𝟙 (((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y).homology n) := by
  have h := (unitPointProjectionHomotopy k Y).homologyMap_eq n
  simpa only [homologyMap_id] using h

def unitPointCrossHomotopy (Y : TopCat.{0}) :
    Homotopy (Singular.CrossBoundary.singularPointCross k (TopCat.of Unit) Y ())
      ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map (Singular.CrossBoundary.pointProductInclusion (TopCat.of Unit) Y ())) := by
  have hp : (TopCat.prodSnd (X := TopCat.of Unit) (Y := Y)) ≫
      Singular.CrossBoundary.pointProductInclusion (TopCat.of Unit) Y () = 𝟙 (TopCat.of (Unit × Y)) := by
    apply TopCat.ext
    intro y
    exact Prod.ext (Subsingleton.elim _ _) rfl
  have h := (unitPointProjectionHomotopy k Y).compRightId
    ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map (Singular.CrossBoundary.pointProductInclusion (TopCat.of Unit) Y ()))
  dsimp only [Singular.CrossBoundary.unitPointProjection] at h
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, hp,
    CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact h

/-- The original cross product with a point is chain homotopic to the
actual inclusion at that point, for every space and every degree. -/
def singularPointCrossHomotopy (X Y : TopCat.{0}) (x : X) :
    Homotopy (Singular.CrossBoundary.singularPointCross k X Y x)
      ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map (Singular.CrossBoundary.pointProductInclusion X Y x)) := by
  let f : TopCat.of Unit ⟶ X := TopCat.ofHom ⟨fun _ => x, continuous_const⟩
  let g := AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, 𝟙 Y) : (TopCat.of Unit, Y) ⟶ (X, Y))
  have h := (unitPointCrossHomotopy k Y).compRight ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map g)
  have hn := Singular.CrossBoundary.singularPointCross_naturality k f (𝟙 Y) ()
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at hn
  change Singular.CrossBoundary.singularPointCross k (TopCat.of Unit) Y () ≫ (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map g =
    Singular.CrossBoundary.singularPointCross k X Y x at hn
  rw [hn, ← Functor.map_comp] at h
  exact h

theorem singularPointCross_homology (X Y : TopCat.{0}) (x : X) (n : ℕ) :
    homologyMap (Singular.CrossBoundary.singularPointCross k X Y x) n =
      homologyMap ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map (Singular.CrossBoundary.pointProductInclusion X Y x)) n :=
  (singularPointCrossHomotopy k X Y x).homologyMap_eq n

theorem singularPointCross_cycleClass (X Y : TopCat.{0}) (x : X) (n : ℕ)
    (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y) n) :
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj (TopCat.of (X × Y))) n
      (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (Singular.CrossBoundary.singularPointCross k X Y x) n z) =
      homologyMap ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map (Singular.CrossBoundary.pointProductInclusion X Y x)) n
        (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y) n z) := by
  rw [← AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality, singularPointCross_homology]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.PointCrossNormalization
