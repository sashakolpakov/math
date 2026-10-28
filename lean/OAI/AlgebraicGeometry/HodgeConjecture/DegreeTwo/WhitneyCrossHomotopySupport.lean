import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ProductHomotopySupport
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CrossQuotientSupport

/-! # Whitney Cross Homotopy Support -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.WhitneyCrossHomotopySupport.Constructions

noncomputable section

/-! The reverse canonical product homotopy preserves both small product supports. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels OAI.AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.ProductAlexanderWhitney

set_option backward.isDefEq.respectTransparency false

variable (k : Type) [Field k]

def alexanderWhitneyCrossHomotopy (X Y : TopCat.{0}) :
    Homotopy (AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.ProductAlexanderWhitney.productAw k (X,Y) ≫ RelativeCrossSupport.Constructions.singularChainCross k X Y)
      (𝟙 (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := k) (TopCat.of (X×Y)))) :=
  ((evaluation AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.SpacePair (ModuleCat.{0} k)).obj (X,Y)).mapHomotopy
    (AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.ProductAlexanderWhitney.canonicalHomotopyEquiv k).homotopyHomInvId

theorem alexanderWhitneyCrossHomotopy_naturality {X X' Y Y' : TopCat.{0}}
    (f : X ⟶ X') (g : Y ⟶ Y') (a b : ℕ) :
    ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor k).map (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f,g) : (X,Y) ⟶ (X',Y')))).f a ≫
      (alexanderWhitneyCrossHomotopy k X' Y').hom a b =
    (alexanderWhitneyCrossHomotopy k X Y).hom a b ≫
      ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor k).map (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f,g) : (X,Y) ⟶ (X',Y')))).f b :=
  ((AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.ProductAlexanderWhitney.canonicalHomotopyEquiv k).homotopyHomInvId.hom a b).naturality
    ((f,g) : (X,Y) ⟶ (X',Y'))

theorem alexanderWhitneyCrossHomotopy_map_zero {X X' Y Y' : TopCat.{0}}
    (f : X ⟶ X') (g : Y ⟶ Y')
    {E : ChainComplex (ModuleCat.{0} k) ℕ}
    (q : AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := k) (TopCat.of (X'×Y')) ⟶ E)
    (hq : (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor k).map
      (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f,g) : (X,Y) ⟶ (X',Y'))) ≫ q = 0) (a b : ℕ) :
    ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor k).map (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f,g) : (X,Y) ⟶ (X',Y')))).f a ≫
      (alexanderWhitneyCrossHomotopy k X' Y').hom a b ≫ q.f b = 0 := by
  rw [← Category.assoc, alexanderWhitneyCrossHomotopy_naturality, Category.assoc]
  have hz : ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor k).map
      (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f,g) : (X,Y) ⟶ (X',Y')))).f b ≫ q.f b = 0 :=
    HomologicalComplex.congr_hom hq b
  rw [hz, comp_zero]

theorem alexanderWhitneyCrossHomotopy_left_zero (X Y : TopCat.{0}) (A : Set X)
    {E : ChainComplex (ModuleCat.{0} k) ℕ}
    (q : AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := k) (TopCat.of (X×Y)) ⟶ E)
    (hq : CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k (TopCat.of (X×Y)) (Prod.fst ⁻¹' A) ≫ q = 0)
    (a b : ℕ) :
    (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k (TopCat.of (X×Y)) (Prod.fst ⁻¹' A)).f a ≫
      (alexanderWhitneyCrossHomotopy k X Y).hom a b ≫ q.f b = 0 := by
  let l : TopCat.of (Prod.fst ⁻¹' A) ⟶ TopCat.of (A×Y) := TopCat.ofHom
    ⟨fun z => (⟨z.val.1,z.property⟩,z.val.2),
      ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
        (continuous_snd.comp continuous_subtype_val)⟩
  let p : TopCat.of (A×Y) ⟶ TopCat.of (X×Y) :=
    AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A,𝟙 Y) : (TopCat.of A,Y) ⟶ (X,Y))
  have hp := CrossQuotientSupport.Constructions.scalarChainMap_quotient_zero k p (Prod.fst ⁻¹' A)
    (by rintro _ ⟨z,rfl⟩; exact z.1.property) q hq
  have hn := alexanderWhitneyCrossHomotopy_map_zero k (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A) (𝟙 Y) q hp a b
  have he : (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k (TopCat.of (X×Y)) (Prod.fst ⁻¹' A)).f a =
      ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor k).map l).f a ≫ ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor k).map p).f a :=
    HomologicalComplex.congr_hom ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor k).map_comp l p) a
  rw [he, Category.assoc]
  exact (congrArg (fun h => ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor k).map l).f a ≫ h) hn).trans comp_zero

theorem alexanderWhitneyCrossHomotopy_right_zero (X Y : TopCat.{0}) (B : Set Y)
    {E : ChainComplex (ModuleCat.{0} k) ℕ}
    (q : AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := k) (TopCat.of (X×Y)) ⟶ E)
    (hq : CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k (TopCat.of (X×Y)) (Prod.snd ⁻¹' B) ≫ q = 0)
    (a b : ℕ) :
    (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k (TopCat.of (X×Y)) (Prod.snd ⁻¹' B)).f a ≫
      (alexanderWhitneyCrossHomotopy k X Y).hom a b ≫ q.f b = 0 := by
  let l : TopCat.of (Prod.snd ⁻¹' B) ⟶ TopCat.of (X×B) := TopCat.ofHom
    ⟨fun z => (z.val.1,⟨z.val.2,z.property⟩),
      (continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _)⟩
  let p : TopCat.of (X×B) ⟶ TopCat.of (X×Y) :=
    AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((𝟙 X,CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion Y B) : (X,TopCat.of B) ⟶ (X,Y))
  have hp := CrossQuotientSupport.Constructions.scalarChainMap_quotient_zero k p (Prod.snd ⁻¹' B)
    (by rintro _ ⟨z,rfl⟩; exact z.2.property) q hq
  have hn := alexanderWhitneyCrossHomotopy_map_zero k (𝟙 X) (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion Y B) q hp a b
  have he : (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k (TopCat.of (X×Y)) (Prod.snd ⁻¹' B)).f a =
      ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor k).map l).f a ≫ ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor k).map p).f a :=
    HomologicalComplex.congr_hom ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor k).map_comp l p) a
  rw [he, Category.assoc]
  exact (congrArg (fun h => ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor k).map l).f a ≫ h) hn).trans comp_zero

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.WhitneyCrossHomotopySupport.Constructions
