import OAI.AlgebraicTopology.Duality.Poincare.CapMayerVietorisChains
import OAI.AlgebraicTopology.Duality.Poincare.SmallSupportCover
import OAI.AlgebraicTopology.Duality.Poincare.SmallSupportedCapClass

/-! # Cap Mayer Vietoris Sum -/

namespace OAI.AlgebraicTopology.Duality.Poincare.CapMayerVietorisSum

noncomputable section

/-!
# The local cap sum inside the actual open union

The two local caps add, with the cohomological Mayer--Vietoris difference
sign, to the cap of the union-supported cochain. This is an equality of
actual chains in the union, proved using its injective chain inclusion.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual scalar-chain maps for nested subspaces compose as their
literal topological inclusions. -/
theorem scalarSubsetInclusion_ambient (X : TopCat.{0}) (U W : Set X)
    (hUW : U ⊆ W) (n : ℕ)
    (z : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)).X n) :
    (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X W)).f n
        ((Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion X hUW)).f n z) =
      (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U)).f n z := by
  have hcomp :
      Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion X hUW) ≫
        Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X W) =
      Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) := by
    change (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map _ ≫
      (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map _ = (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map _
    rw [← Functor.map_comp]
    rfl
  exact ConcreteCategory.congr_hom (HomologicalComplex.congr_hom hcomp n) z

/-- The union cap, obtained from the genuine four-cover refinement. -/
def smallSupportUnionCap (X : TopCat.{0}) (U V K L : Set X) (p q : ℕ)
    (a : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (K ∪ L)ᶜ).X p)
    (z : (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X (p + q)) :
    (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (U ∪ V : Set X))).X q :=
  SmallSupportedCap.smallSupportedCap X (U ∪ V) (K ∪ L)ᶜ p q a
    ((SmallSupportCover.smallSupportChainToUnion ℤ X U V K L).f (p + q) z)

/-- The ambient value of the union cap is the actual ordinary mixed cap. -/
theorem smallSupportUnionCap_inclusion (X : TopCat.{0}) (U V K L : Set X) (p q : ℕ)
    (a : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (K ∪ L)ᶜ).X p)
    (z : (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X (p + q)) :
    (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X (U ∪ V))).f q
        (smallSupportUnionCap X U V K L p q a z) =
      IntegralCapCoefficients.mixedSingularCap X p q
        ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (K ∪ L)ᶜ).f p a)
        ((AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion X (SmallSupportCover.smallSupportCover X U V K L)).f (p + q) z) := by
  rw [smallSupportUnionCap, SmallSupportedCap.smallSupportedCap_inclusion]
  exact congrArg (IntegralCapCoefficients.mixedSingularCap X p q
    ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (K ∪ L)ᶜ).f p a))
    (ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
      (SmallSupportCover.smallSupportChainToUnion_integral_inclusion X U V K L) (p + q)) z)

/-- The local difference equals the union cap inside the actual union
chain group, whenever the cochains satisfy the actual difference equation. -/
theorem smallSupportCap_union_eq_sub
    (X : TopCat.{0}) (U V K L : Set X) (p q : ℕ)
    (a : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (K ∪ L)ᶜ).X p)
    (bK : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X Kᶜ).X p)
    (bL : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X Lᶜ).X p)
    (z : (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X (p + q))
    (hab : (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X Kᶜ).f p bK -
        (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X Lᶜ).f p bL =
      (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (K ∪ L)ᶜ).f p a) :
    (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ)
        (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion X (Set.subset_union_left : U ⊆ U ∪ V))).f q
        (CapMayerVietorisChains.smallSupportLeftCap X U V K L p q bK z) -
      (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ)
        (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion X (Set.subset_union_right : V ⊆ U ∪ V))).f q
        (CapMayerVietorisChains.smallSupportRightCap X U V K L p q bL z) =
      smallSupportUnionCap X U V K L p q a z := by
  apply SmallSupportedCap.rationalSubspaceChainInclusion_injective X (U ∪ V) q
  rw [map_sub, scalarSubsetInclusion_ambient, scalarSubsetInclusion_ambient,
    CapMayerVietorisChains.smallSupportLeftCap_inclusion, CapMayerVietorisChains.smallSupportRightCap_inclusion,
    smallSupportUnionCap_inclusion]
  have h := congrArg (fun c => IntegralCapCoefficients.mixedSingularCap X p q c
    ((AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion X (SmallSupportCover.smallSupportCover X U V K L)).f (p + q) z)) hab
  simpa only [map_sub, LinearMap.sub_apply] using h

/-- The union cap is an actual cycle when its union-relative chain is a
cycle and its cochain is a cocycle. -/
theorem smallSupportUnionCap_mem_chainCycles
    (X : TopCat.{0}) (U V K L : Set X) (p q : ℕ)
    (a : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (K ∪ L)ᶜ) p)
    (z : (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X (p + q))
    (hz : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X (K ∪ L)ᶜ).f (p + q)
      ((AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion X (SmallSupportCover.smallSupportCover X U V K L)).f (p + q) z) ∈
        Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X (K ∪ L)ᶜ) (p + q)) :
    smallSupportUnionCap X U V K L p q a.val z ∈
      Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (U ∪ V : Set X))) q := by
  apply SmallSupportedCapClass.smallSupportedCap_mem_chainCycles_of_relative X (U ∪ V) (K ∪ L)ᶜ p q a
  have hi := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (SmallSupportCover.smallSupportChainToUnion_integral_inclusion X U V K L) (p + q)) z
  change (AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X (U ∪ V) (K ∪ L)ᶜ).f (p + q)
      ((SmallSupportCover.smallSupportChainToUnion ℤ X U V K L).f (p + q) z) =
    (AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion X (SmallSupportCover.smallSupportCover X U V K L)).f (p + q) z at hi
  rw [hi]
  exact hz

/-- The actual union cycle represented by the supported cap. -/
def smallSupportUnionCapCycle
    (X : TopCat.{0}) (U V K L : Set X) (p q : ℕ)
    (a : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (K ∪ L)ᶜ) p)
    (z : (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X (p + q))
    (hz : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X (K ∪ L)ᶜ).f (p + q)
      ((AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion X (SmallSupportCover.smallSupportCover X U V K L)).f (p + q) z) ∈
        Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X (K ∪ L)ᶜ) (p + q)) :
    Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (U ∪ V : Set X))) q :=
  ⟨smallSupportUnionCap X U V K L p q a.val z,
    smallSupportUnionCap_mem_chainCycles X U V K L p q a z hz⟩

end

end OAI.AlgebraicTopology.Duality.Poincare.CapMayerVietorisSum
