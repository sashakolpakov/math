import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeTensorFunctional
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCrossNonvanishing

/-! # Relative Tensor Homology -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeTensorHomology.Constructions

noncomputable section

/-!
# DegreeTwo: relative tensor evaluation on actual homology classes

The canonical tensor functional associated to two relative cocycles
evaluates their algebraic tensor class as the product of the two genuine
relative evaluations. The proved cross-product retraction gives the same
formula after the relative Alexander–Whitney map.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open OAI.AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.TensorCocycles OAI.AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology
open scoped TensorProduct DirectSum

set_option backward.isDefEq.respectTransparency false

theorem relativeCocycleDual_closed (X : TopCat.{0}) (A : Set X) (p : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p) :
    (CycleClass.Geometric.RelativeChainD.Cycles.relativeDegreewiseChainDualEquiv (ModuleCat.of ℚ ℚ) X A p c.val).comp
      ((CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A).d (p+1) p).hom = 0 := by
  rw [← CycleClass.Geometric.RelativeChainD.Cycles.relativeDegreewiseChainDualEquiv_d,
    AlgebraicTopology.Cohomology.Singular.Evaluation.cochainCocycle_d_eq_zero _ p (p+1) c, map_zero]

theorem relativeCocycleDual_representatives (X : TopCat.{0}) (A : Set X) (p : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p)
    (u : CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ X A p) :
    CycleClass.Geometric.RelativeChainD.Cycles.relativeDegreewiseChainDualEquiv (ModuleCat.of ℚ ℚ) X A p c.val
      (AlgebraicTopology.Kunneth.ChainSplittingD.Construction.ChainSplitting.representatives (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A) p u).val =
    CycleClass.Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) X A p (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ p c) u := by
  have h := CycleClass.Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation_class_class (ModuleCat.of ℚ ℚ) X A p c
    (AlgebraicTopology.Kunneth.ChainSplittingD.Construction.ChainSplitting.representatives (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A) p u)
  rw [AlgebraicTopology.Kunneth.ChainSplittingD.Construction.ChainSplitting.class_representatives] at h
  exact h.symm

variable (X Y : TopCat.{0}) (A : Set X) (B : Set Y) (p q : ℕ)
variable (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p)
variable (d : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) Y B) q)

def relativeTensorHomologyFunctional :
    Module.Dual ℚ ((CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A ⊗ CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ Y B).homology (p+q)) :=
  AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.TensorCocycles.tensorHomologyFunctional (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A) (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ Y B) p q
    (CycleClass.Geometric.RelativeChainD.Cycles.relativeDegreewiseChainDualEquiv (ModuleCat.of ℚ ℚ) X A p c.val)
    (CycleClass.Geometric.RelativeChainD.Cycles.relativeDegreewiseChainDualEquiv (ModuleCat.of ℚ ℚ) Y B q d.val)
    (relativeCocycleDual_closed X A p c) (relativeCocycleDual_closed Y B q d)

theorem relativeTensorHomologyFunctional_class
    (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A ⊗ CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ Y B) (p+q)) :
    relativeTensorHomologyFunctional X Y A B p q c d (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass _ (p+q) z) =
      RelativeTensorFunctional.Constructions.relativeTensorFunctional X Y A B p q c.val d.val z.val :=
  AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.TensorCocycles.tensorHomologyFunctional_class _ _ _ _ _ _ _ _ z

theorem relativeTensorHomologyFunctional_algebraic
    (u : CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ X A p) (v : CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ Y B q) :
    relativeTensorHomologyFunctional X Y A B p q c d
      (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.algebraicKunneth (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A) (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ Y B) (p+q)
        (DirectSum.lof ℚ (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.DegreePairs (p+q))
          (fun ij => CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ X A ij.val.1 ⊗[ℚ]
            CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ Y B ij.val.2) ⟨(p,q),rfl⟩ (u ⊗ₜ[ℚ] v))) =
    CycleClass.Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) X A p (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ p c) u *
      CycleClass.Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) Y B q (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ q d) v := by
  rw [relativeTensorHomologyFunctional, AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.TensorCocycles.tensorHomologyFunctional_algebraic_self,
    relativeCocycleDual_representatives, relativeCocycleDual_representatives]

theorem relativeTensorHomologyFunctional_cross (hA : IsOpen A) (hB : IsOpen B)
    (u : CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ X A p) (v : CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ Y B q) :
    relativeTensorHomologyFunctional X Y A B p q c d
      (SmallProductComparison.Constructions.relativeAlexanderWhitneyHomology X Y A B hA hB (p+q)
        (RelativeCrossNonvanishing.Constructions.relativeHomologyCrossClass X Y A B p q u v)) =
    CycleClass.Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) X A p (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ p c) u *
      CycleClass.Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) Y B q (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ q d) v := by
  have h := ConcreteCategory.congr_hom (RelativeCrossNonvanishing.Constructions.relativeCrossWhitney_homology X Y A B hA hB (p+q))
    (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.algebraicKunneth (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A) (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ Y B) (p+q)
      (DirectSum.lof ℚ (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.DegreePairs (p+q))
        (fun ij => CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ X A ij.val.1 ⊗[ℚ]
          CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ Y B ij.val.2) ⟨(p,q),rfl⟩ (u ⊗ₜ[ℚ] v)))
  change SmallProductComparison.Constructions.relativeAlexanderWhitneyHomology X Y A B hA hB (p+q)
    (RelativeCrossNonvanishing.Constructions.relativeHomologyCrossClass X Y A B p q u v) = _ at h
  rw [h]
  exact relativeTensorHomologyFunctional_algebraic X Y A B p q c d u v

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeTensorHomology.Constructions
