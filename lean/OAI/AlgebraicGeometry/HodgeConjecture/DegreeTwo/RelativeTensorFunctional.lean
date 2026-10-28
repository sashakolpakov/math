import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmallProductComparison
import OAI.AlgebraicTopology.Kunneth.TensorAlexanderWhitney

/-! # Relative Tensor Functional -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeTensorFunctional.Constructions

noncomputable section

/-!
# DegreeTwo: actual tensor evaluation through relative quotients

Evaluation on the quotient tensor is exactly evaluation of the absolute
cochains on representatives. Through the canonical Alexander–Whitney
map it is the original exterior cup cochain, with both supports retained.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open OAI.AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.TensorCocycles

set_option backward.isDefEq.respectTransparency false

theorem tensorFunctional_map
    {k : Type} [Field k] {C D C' D' : ChainComplex (ModuleCat.{0} k) ℕ}
    (f : C ⟶ C') (g : D ⟶ D') (p q : ℕ)
    (a : Module.Dual k (C'.X p)) (b : Module.Dual k (D'.X q))
    (z : (C ⊗ D).X (p + q)) :
    AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.TensorCocycles.tensorFunctional C' D' p q a b ((f ⊗ₘ g).f (p+q) z) =
      AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.TensorCocycles.tensorFunctional C D p q (a.comp (f.f p).hom) (b.comp (g.f q).hom) z := by
  have h := ConcreteCategory.congr_hom
    (AlgebraicTopology.Kunneth.CohomologyTensorNe.Construction.TensorProjections.projection_tensorHom C D f g (p+q) ⟨(p,q),rfl⟩) z
  change AlgebraicTopology.Kunneth.CohomologyTensorNe.Construction.TensorProjections.projection C' D' (p+q) ⟨(p,q),rfl⟩
    ((f ⊗ₘ g).f (p+q) z) =
      TensorProduct.map (f.f p).hom (g.f q).hom
        (AlgebraicTopology.Kunneth.CohomologyTensorNe.Construction.TensorProjections.projection C D (p+q) ⟨(p,q),rfl⟩ z) at h
  change AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.TensorCocycles.pairing a b (AlgebraicTopology.Kunneth.CohomologyTensorNe.Construction.TensorProjections.projection C' D' (p+q)
    ⟨(p,q),rfl⟩ ((f ⊗ₘ g).f (p+q) z)) = _
  rw [h]
  exact LinearMap.congr_fun (AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.TensorCocycles.pairing_map a b (f.f p).hom (g.f q).hom) _

variable (X Y : TopCat.{0}) (A : Set X) (B : Set Y) (p q : ℕ)
variable (c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p)
variable (d : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) Y B).X q)

def relativeTensorFunctional :
    Module.Dual ℚ ((CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A ⊗ CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ Y B).X (p+q)) :=
  AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.TensorCocycles.tensorFunctional (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A) (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ Y B) p q
    (CycleClass.Geometric.RelativeChainD.Cycles.relativeDegreewiseChainDualEquiv (ModuleCat.of ℚ ℚ) X A p c)
    (CycleClass.Geometric.RelativeChainD.Cycles.relativeDegreewiseChainDualEquiv (ModuleCat.of ℚ ℚ) Y B q d)

theorem relativeTensorFunctional_projection
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X ⊗ AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) Y).X (p+q)) :
    relativeTensorFunctional X Y A B p q c d
      ((CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X A ⊗ₘ CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ Y B).f (p+q) z) =
    AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.TensorCocycles.tensorFunctional (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) Y) p q
      (AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv (ModuleCat.of ℚ ℚ) X p
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c))
      (AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv (ModuleCat.of ℚ ℚ) Y q
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) Y B).f q d)) z := by
  have hc : (CycleClass.Geometric.RelativeChainD.Cycles.relativeDegreewiseChainDualEquiv (ModuleCat.of ℚ ℚ) X A p c).comp
      ((CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X A).f p).hom =
    AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv (ModuleCat.of ℚ ℚ) X p
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c) :=
    LinearMap.ext (CycleClass.Geometric.RelativeChainD.Cycles.relativeDegreewiseChainDualEquiv_projection _ _ _ _ _)
  have hd : (CycleClass.Geometric.RelativeChainD.Cycles.relativeDegreewiseChainDualEquiv (ModuleCat.of ℚ ℚ) Y B q d).comp
      ((CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ Y B).f q).hom =
    AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv (ModuleCat.of ℚ ℚ) Y q
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) Y B).f q d) :=
    LinearMap.ext (CycleClass.Geometric.RelativeChainD.Cycles.relativeDegreewiseChainDualEquiv_projection _ _ _ _ _)
  rw [relativeTensorFunctional, tensorFunctional_map, hc, hd]

theorem relativeTensorFunctional_smallAW_projection
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (X × Y))).X (p+q)) :
    relativeTensorFunctional X Y A B p q c d
      ((SmallProductComparison.Constructions.smallRelativeAlexanderWhitney X Y A B).f (p+q)
        ((SmallProductComparison.Constructions.productSmallComplementProjection X Y A B).f (p+q) z)) =
    AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv (ModuleCat.of ℚ ℚ) (TopCat.of (X × Y)) (p+q)
      (AlgebraicTopology.Products.Cup.singularCup (TopCat.of (X × Y))
        ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) TopCat.prodFst).f p
          ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c))
        ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) TopCat.prodSnd).f q
          ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) Y B).f q d))) z := by
  have h := ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (SmallProductComparison.Constructions.smallRelativeAlexanderWhitney_projection X Y A B) (p+q)) z
  change (SmallProductComparison.Constructions.smallRelativeAlexanderWhitney X Y A B).f (p+q)
      ((SmallProductComparison.Constructions.productSmallComplementProjection X Y A B).f (p+q) z) =
    (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X A ⊗ₘ CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ Y B).f (p+q)
      ((AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.ProductAlexanderWhitney.productAw ℚ (X,Y)).f (p+q) z) at h
  rw [h, relativeTensorFunctional_projection]
  exact AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.CupTensorComparison.cup_tensor_chain ℚ (X,Y) p q _ _ z

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeTensorFunctional.Constructions
