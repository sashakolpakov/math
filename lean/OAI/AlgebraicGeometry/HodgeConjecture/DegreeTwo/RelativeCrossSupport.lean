import OAI.AlgebraicTopology.Kunneth.ComparisonLow
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains

/-! # Relative Cross Support -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions

noncomputable section

/-!
# DegreeTwo: actual cross products preserve relative supports

The natural Eilenberg–Zilber cross product sends chains from either
factor's subspace into the corresponding product subspace. Consequently
both kinds of chains vanish in the relative product quotient.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type) [Field k]

/-- A map landing in the subspace is zero after the actual relative
chain projection. -/
theorem scalarChainMap_relativeProjection_zero {X Y : TopCat.{0}}
    (f : X ⟶ Y) (A : Set Y) (hf : Set.range f ⊆ A) :
    (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor k).map f ≫ CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k Y A = 0 := by
  let g : X ⟶ TopCat.of A := TopCat.ofHom
    ⟨fun x => ⟨f x, hf ⟨x, rfl⟩⟩, f.hom.continuous.subtype_mk _⟩
  have hfg : g ≫ CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion Y A = f := rfl
  rw [← hfg, Functor.map_comp, Category.assoc]
  change _ ≫ (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k Y A ≫ _) = 0
  rw [CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion_projection, comp_zero]

/-- The actual chain cross product evaluated at two spaces. -/
def singularChainCross (X Y : TopCat.{0}) :
    AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := k) X ⊗ AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := k) Y ⟶
      AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := k) (TopCat.of (X × Y)) :=
  (AlgebraicTopology.Kunneth.ComparisonLow.Construction.EilenbergZilber.homotopyEquiv k X Y).hom

theorem singularChainCross_naturality {X X' Y Y' : TopCat.{0}}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor k).map f ⊗ₘ (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor k).map g) ≫
        singularChainCross k X' Y' =
      singularChainCross k X Y ≫
        (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor k).map
          (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, g) : (X, Y) ⟶ (X', Y'))) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact ((AlgebraicTopology.Kunneth.ComparisonLow.Construction.EilenbergZilber.cross k).f n).naturality
    ((f, g) : (X, Y) ⟶ (X', Y'))

/-- Complement for the product of two supports. -/
def crossSupportComplement (X Y : TopCat.{0}) (A : Set X) (B : Set Y) :
    Set (X × Y) := Prod.fst ⁻¹' A ∪ Prod.snd ⁻¹' B

theorem singularChainCross_left_zero (X Y : TopCat.{0}) (A : Set X) (B : Set Y) :
    (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k X A ⊗ₘ 𝟙 (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := k) Y)) ≫
        singularChainCross k X Y ≫
        CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k (TopCat.of (X × Y)) (crossSupportComplement X Y A B) = 0 := by
  have hn := singularChainCross_naturality k (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A) (𝟙 Y)
  rw [CategoryTheory.Functor.map_id] at hn
  change (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k X A ⊗ₘ 𝟙 (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := k) Y)) ≫
    singularChainCross k X Y = _ at hn
  rw [← Category.assoc, hn, Category.assoc]
  have hz := scalarChainMap_relativeProjection_zero k
    (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A, 𝟙 Y) : (TopCat.of A, Y) ⟶ (X, Y)))
    (crossSupportComplement X Y A B) (by
      rintro _ ⟨x, rfl⟩
      exact Or.inl x.1.property)
  exact (congrArg (fun u => singularChainCross k (TopCat.of A) Y ≫ u) hz).trans
    comp_zero

theorem singularChainCross_right_zero (X Y : TopCat.{0}) (A : Set X) (B : Set Y) :
    (𝟙 (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := k) X) ⊗ₘ CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k Y B) ≫
        singularChainCross k X Y ≫
        CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k (TopCat.of (X × Y)) (crossSupportComplement X Y A B) = 0 := by
  have hn := singularChainCross_naturality k (𝟙 X) (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion Y B)
  rw [CategoryTheory.Functor.map_id] at hn
  change (𝟙 (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := k) X) ⊗ₘ CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k Y B) ≫
    singularChainCross k X Y = _ at hn
  rw [← Category.assoc, hn, Category.assoc]
  have hz := scalarChainMap_relativeProjection_zero k
    (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((𝟙 X, CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion Y B) : (X, TopCat.of B) ⟶ (X, Y)))
    (crossSupportComplement X Y A B) (by
      rintro _ ⟨x, rfl⟩
      exact Or.inr x.2.property)
  exact (congrArg (fun u => singularChainCross k X (TopCat.of B) ≫ u) hz).trans
    comp_zero

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions
