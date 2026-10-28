import OAI.AlgebraicGeometry.CycleClass.Thom.BinarySmallEndomorphism
import OAI.AlgebraicTopology.Products.RelativeReversal

/-! # Binary Small Reversal -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.BinarySmallReversal.Constructions

noncomputable section

/-! Signed vertex reversal acts on the actual binary-small cochains and induces the identity on their cohomology. -/

open _root_.CategoryTheory OAI.AlgebraicTopology.Products.RelativeReversal

open OAI.AlgebraicGeometry.CycleClass.Thom.BinarySmallEndomorphism.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : TopCat.{0}) (A B : Set X)

def binaryReversal : HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochains X A B ⟶ HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochains X A B :=
  BinarySmallEndomorphism.Constructions.binaryEndomorphism X A B (AlgebraicTopology.Products.SingularReversalHomotopy.singularReversalCochainMap (ModuleCat.of ℚ ℚ) X)
    (AlgebraicTopology.Products.SingularReversalHomotopy.singularReversalCochainMap (ModuleCat.of ℚ ℚ) (TopCat.of A))
    (AlgebraicTopology.Products.SingularReversalHomotopy.singularReversalCochainMap (ModuleCat.of ℚ ℚ) (TopCat.of B))
    (AlgebraicTopology.Products.SingularReversalHomotopy.singularReversalCochainMap_naturality (ModuleCat.of ℚ ℚ) (Geometric.LocalHomology.Cycles.subspaceInclusion X A)).symm
    (AlgebraicTopology.Products.SingularReversalHomotopy.singularReversalCochainMap_naturality (ModuleCat.of ℚ ℚ) (Geometric.LocalHomology.Cycles.subspaceInclusion X B)).symm

theorem binaryReversal_inclusion (n : ℕ) (c : (HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochains X A B).X n) :
    HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B n ((binaryReversal X A B).f n c) =
      (AlgebraicTopology.Products.SingularReversalHomotopy.singularReversalCochainMap (ModuleCat.of ℚ ℚ) X).f n
        (HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B n c) :=
  BinarySmallEndomorphism.Constructions.binaryEndomorphism_inclusion X A B _ _ _ _ _ n c

theorem binaryReversal_relative :
    HodgeConjecture.DegreeTwo.BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap X A B ≫ binaryReversal X A B =
      AlgebraicTopology.Products.RelativeReversal.relativeReversalCochainMap (ModuleCat.of ℚ ℚ) X (A ∪ B) ≫ HodgeConjecture.DegreeTwo.BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap X A B := by
  ext n : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  apply HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainInclusion_injective X A B n
  change HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B n
    ((binaryReversal X A B).f n ((HodgeConjecture.DegreeTwo.BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap X A B).f n c)) =
      HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B n ((HodgeConjecture.DegreeTwo.BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap X A B).f n
        ((AlgebraicTopology.Products.RelativeReversal.relativeReversalCochainMap (ModuleCat.of ℚ ℚ) X (A ∪ B)).f n c))
  rw [binaryReversal_inclusion, HodgeConjecture.DegreeTwo.BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap_inclusion,
    HodgeConjecture.DegreeTwo.BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap_inclusion, AlgebraicTopology.Products.RelativeReversal.relativeReversalCochainMap_inclusion_apply]

theorem binaryReversal_homologyMap (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    HomologicalComplex.homologyMap (binaryReversal X A B) n =
      𝟙 ((HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochains X A B).homology n) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  obtain ⟨a, rfl⟩ := (HodgeConjecture.DegreeTwo.BinarySmallRelativeComparison.Constructions.binarySmallRelativeCohomologyMap_bijective X A B hA hB n).surjective c
  have h := congrArg (fun f => HomologicalComplex.homologyMap f n) (binaryReversal_relative X A B)
  simp only [HomologicalComplex.homologyMap_comp, AlgebraicTopology.Products.RelativeReversal.relativeReversalCochainMap_homologyMap,
    Category.id_comp] at h
  exact ConcreteCategory.congr_hom h a

theorem binaryReversal_class (hA : IsOpen A) (hB : IsOpen B) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochains X A B) n) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ n (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (binaryReversal X A B) n c) = AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ n c := by
  rw [← AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality, binaryReversal_homologyMap X A B hA hB]
  rfl

end

end OAI.AlgebraicGeometry.CycleClass.Thom.BinarySmallReversal.Constructions
