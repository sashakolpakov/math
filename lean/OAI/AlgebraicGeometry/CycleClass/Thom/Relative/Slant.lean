import OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossNaturality
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeUniversalCoefficientNaturality

/-! # Slant -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Relative.Slant.Constructions

noncomputable section

/-! The relative slant product is defined by evaluation on the
actual relative homology cross product. It will supply integration
along compact projection fibers while retaining support information. -/

open _root_.CategoryTheory _root_.HomologicalComplex OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeUniversalCoefficientNaturality.Cycles
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossAssociateForward.Constructions.HomologyAssociativity OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossNaturality.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.HomologyProductAssociativity.Constructions.Products

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type) [Field k] (X Y : TopCat.{0}) (A : Set X) (B : Set Y)
  (p q n : ℕ) (hpq : p + q = n)

def crossWith (b : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology k Y B q) :
    Geometric.RelativeScalarChains.Cycles.relativeScalarHomology k X A p →ₗ[k]
      Geometric.RelativeScalarChains.Cycles.relativeScalarHomology k (TopCat.of (X × Y)) (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) n where
  toFun a := CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt k X Y A B p q n hpq a b
  map_add' a a' := by
    simp only [CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt, HomologyProductAssociativity.Constructions.Products.homologyProduct, TensorProduct.add_tmul, map_add]
  map_smul' r a := CrossNaturality.Constructions.relativeCrossClassAt_smul_left k p q n hpq r a b

def slant (b : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology k Y B q) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of k k) (TopCat.of (X × Y)) (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) n →ₗ[k]
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of k k) X A p :=
  (Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv k X A p).symm.toLinearMap.comp
    ((crossWith k X Y A B p q n hpq b).dualMap.comp
      (Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv k (TopCat.of (X × Y)) (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) n).toLinearMap)

theorem slant_evaluation (b : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology k Y B q)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of k k) (TopCat.of (X × Y)) (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) n)
    (a : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology k X A p) :
    Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv k X A p (slant k X Y A B p q n hpq b c) a =
      Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv k (TopCat.of (X × Y)) (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) n c
        (CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt k X Y A B p q n hpq a b) := by
  change (Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv k X A p)
    ((Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv k X A p).symm _) a = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Relative.Slant.Constructions
