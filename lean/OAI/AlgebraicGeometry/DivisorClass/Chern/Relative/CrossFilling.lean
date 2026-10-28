import OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.CrossRepresentatives
import OAI.AlgebraicGeometry.DivisorClass.Chern.DiskTensorCycle

/-! # Cross Filling -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.CrossFilling

noncomputable section

section

/-! The original relative homology cross class equals the class of any
displayed projected disk-cross-filling representative, including after
identifying its support with the actual puncture. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem relativeClass_transport_projection (X : TopCat.{0}) (A A' : Set X) (h : A = A')
    (n : ℕ) (B : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).X n)
    (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A) n)
    (z' : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A') n)
    (hz : z.val = (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X A).f n B)
    (hz' : z'.val = (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X A').f n B) :
    eqToHom (congrArg (fun U => CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ X U n) h)
      (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass _ n z) = AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass _ n z' := by
  subst A'
  have he : z = z' := Subtype.ext (hz.trans hz'.symm)
  subst z'
  rfl

theorem relativeDiskCrossClass_eq_filling (X Y : TopCat.{0}) (A : Set X) (B : Set Y)
    (U : Set (X × Y)) (hU : HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Y A B = U) (q : ℕ)
    (D : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).X 2)
    (E : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) Y).X q)
    (x : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A) 2)
    (y : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ Y B) q)
    (hx : x.val = (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X A).f 2 D)
    (hy : y.val = (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ Y B).f q E)
    (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ (TopCat.of (X × Y)) U) (2 + q))
    (hz : z.val = (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ (TopCat.of (X × Y)) U).f (2 + q)
      (Singular.CrossBoundary.singularCrossChain ℚ X Y 2 q (2 + q) rfl D E)) :
    eqToHom (congrArg (fun V => CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of (X × Y)) V (2 + q)) hU)
      (HodgeConjecture.DegreeTwo.RelativeCrossNonvanishing.Constructions.relativeHomologyCrossClass X Y A B 2 q (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass _ 2 x) (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass _ q y)) =
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass _ (2 + q) z := by
  let t := DiskTensorCycle.diskTensorCycle (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A) (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ Y B) q x y
  rw [CrossRepresentatives.relativeHomologyCrossClass_of_tensor_cycle X Y A B 2 q x y t rfl]
  apply relativeClass_transport_projection (TopCat.of (X × Y))
    (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) U hU (2 + q)
    (Singular.CrossBoundary.singularCrossChain ℚ X Y 2 q (2 + q) rfl D E) _ z _ hz
  change (HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.relativeSingularChainCross ℚ X Y A B).f (2 + q)
    (ιTensorObj (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A) (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ Y B) 2 q (2 + q) rfl
      (x.val ⊗ₜ[ℚ] y.val)) = _
  rw [hx, hy]
  exact CrossRepresentatives.relativeSingularCross_quotient_representatives X Y A B 2 q D E

end

/-! Explicit degree transport for the original relative cross-filling comparison. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem relativeDiskCrossClass_eq_filling_at (X Y : TopCat.{0}) (A : Set X) (B : Set Y)
    (U : Set (X × Y)) (hU : HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Y A B = U) (q n : ℕ) (hn : 2 + q = n)
    (D : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).X 2)
    (E : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) Y).X q)
    (x : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A) 2)
    (y : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ Y B) q)
    (hx : x.val = (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X A).f 2 D)
    (hy : y.val = (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ Y B).f q E)
    (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ (TopCat.of (X × Y)) U) n)
    (hz : z.val = (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ (TopCat.of (X × Y)) U).f n
      (Singular.CrossBoundary.singularCrossChain ℚ X Y 2 q n hn D E)) :
    eqToHom (congrArg (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of (X × Y)) U) hn)
      (eqToHom (congrArg (fun V => CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of (X × Y)) V (2 + q)) hU)
        (HodgeConjecture.DegreeTwo.RelativeCrossNonvanishing.Constructions.relativeHomologyCrossClass X Y A B 2 q (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass _ 2 x) (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass _ q y))) =
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass _ n z := by
  subst n
  exact relativeDiskCrossClass_eq_filling X Y A B U hU q D E x y hx hy z hz

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.CrossFilling
