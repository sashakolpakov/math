import OAI.AlgebraicTopology.Duality.Poincare.TwoSupportRelativeCap
import OAI.AlgebraicTopology.Duality.Poincare.BinarySmallComplementFunctoriality
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCochainFunctoriality

/-! # Support Relative Cap Naturality -/

namespace OAI.AlgebraicTopology.Duality.Poincare.SupportRelativeCapNaturality

noncomputable section

/-!
# Naturality of the chain cap with two relative supports

The native small-chain quotient and rational relative target are functorial
under any continuous map preserving their two subspaces. The cap identity
follows on actual ambient representatives from Alexander--Whitney naturality.
-/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCochainFunctoriality.Cohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem relativeCochainMap_inclusion_apply
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A : Set X} {A' : Set Y}
    (h : Set.MapsTo f A A') (p : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) Y A').X p) :
    (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p
        ((Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) f h).f p c) =
      (Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) f).f p
        ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) Y A').f p c) :=
  ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (Cohomology.Singular.RelativeSequence.relativeCochainInclusion_naturality (ModuleCat.of ℚ ℚ) f h) p) c

private theorem smallComplementPairMap_projection_apply
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A B : Set X} {A' B' : Set Y}
    (hA : Set.MapsTo f A A') (hB : Set.MapsTo f B B') (n : ℕ)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n) :
    (BinarySmallComplementFunctoriality.binarySmallComplementPairMap f hA hB).f n
        ((AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B).f n z) =
      (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection Y A' B').f n
        ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map f).f n z) :=
  ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (BinarySmallComplementFunctoriality.binarySmallComplementPairMap_projection f hA hB) n) z

private theorem scalarRelativeMap_projection_apply
    {X Y : TopCat.{0}} (f : X ⟶ Y) {B : Set X} {B' : Set Y}
    (hB : Set.MapsTo f B B') (q : ℕ)
    (z : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).X q) :
    (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f hB).f q
        ((AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X B).f q z) =
      (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ Y B').f q
        ((Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) f).f q z) :=
  ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection_naturality ℚ f hB) q) z

/-- Two-support cap naturality for every continuous map of the two pairs.
Openness is only needed later when replacing the small quotient on homology. -/
theorem twoSupportSmallCap_naturality
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A B : Set X} {A' B' : Set Y}
    (hA : Set.MapsTo f A A') (hB : Set.MapsTo f B B') (p q : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) Y A').X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B).X (p + q)) :
    (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f hB).f q
        (TwoSupportRelativeCap.twoSupportSmallCap X A B p q
          ((Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) f hA).f p c) z) =
      TwoSupportRelativeCap.twoSupportSmallCap Y A' B' p q c
        ((BinarySmallComplementFunctoriality.binarySmallComplementPairMap f hA hB).f (p + q) z) := by
  obtain ⟨z, rfl⟩ := TwoSupportRelativeCap.binarySmallComplementProjection_surjective X A B (p + q) z
  rw [TwoSupportRelativeCap.twoSupportSmallCap_projection, smallComplementPairMap_projection_apply,
    TwoSupportRelativeCap.twoSupportSmallCap_projection, scalarRelativeMap_projection_apply,
    relativeCochainMap_inclusion_apply, IntegralCapCoefficients.mixedSingularCap_naturality]

end

end OAI.AlgebraicTopology.Duality.Poincare.SupportRelativeCapNaturality
