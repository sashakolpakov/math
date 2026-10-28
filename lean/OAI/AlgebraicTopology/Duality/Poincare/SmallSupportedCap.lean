import OAI.AlgebraicTopology.Duality.Poincare.SupportRelativeCap
import OAI.AlgebraicGeometry.CycleClass.Geometric.BinarySmallUnion
import OAI.AlgebraicGeometry.CycleClass.Geometric.RationalSingularChains

/-! # Small Supported Cap -/

namespace OAI.AlgebraicTopology.Duality.Poincare.SmallSupportedCap

noncomputable section

/-!
# Cap products landing in an actual open-cover piece

If a cochain vanishes on `A`, capping chains subordinate to `{U, A}` gives
chains on `U`. This is constructed with the genuine binary small-chain
pushout: use the ordinary cap on `U` and the zero map on `A`. The resulting
map has the required equality after inclusion in the ambient chains.
Neither openness nor an excision assertion is needed for this construction.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

/-- The actual scalar-chain inclusion of a subspace is injective degreewise. -/
theorem rationalSubspaceChainInclusion_injective (X : TopCat.{0}) (U : Set X) (n : ℕ) :
    Function.Injective ((Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U)).f n) := by
  have hm : Mono (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U)) := by
    change Mono ((AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U))
    exact Functor.map_mono (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ) _
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

private theorem binarySmallChainDegreePushout (X : TopCat.{0}) (U A : Set X) (n : ℕ) :
    IsPushout
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map
        (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion X (Set.inter_subset_left : U ∩ A ⊆ U))).f n)
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map
        (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion X (Set.inter_subset_right : U ∩ A ⊆ A))).f n)
      ((AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularLeft X U A)).f n)
      ((AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularRight X U A)).f n) :=
  (HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).map_isPushout
    (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallChain_isPushout X U A)

private def capOnFirstPiece (X : TopCat.{0}) (U A : Set X) (p q : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p) :
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of U)).X (p + q) ⟶
      ModuleCat.of ℤ ((Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)).X q) :=
  ModuleCat.ofHom (IntegralCapCoefficients.mixedSingularCap (TopCat.of U) p q
    ((Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U)).f p
      ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c)))

private theorem capOnFirstPiece_intersection (X : TopCat.{0}) (U A : Set X) (p q : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p) :
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map
        (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion X (Set.inter_subset_left : U ∩ A ⊆ U))).f (p + q) ≫
      capOnFirstPiece X U A p q c =
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map
        (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion X (Set.inter_subset_right : U ∩ A ⊆ A))).f (p + q) ≫
      (0 : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of A)).X (p + q) ⟶
        ModuleCat.of ℤ ((Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)).X q)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply rationalSubspaceChainInclusion_injective X U q
  change (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U)).f q
    (IntegralCapCoefficients.mixedSingularCap (TopCat.of U) p q
      ((Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U)).f p
        ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c))
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map
        (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion X (Set.inter_subset_left : U ∩ A ⊆ U))).f (p + q) z)) =
    (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U)).f q 0
  rw [IntegralCapCoefficients.mixedSingularCap_naturality, map_zero]
  have hcomp :
      AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map
          (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion X (Set.inter_subset_left : U ∩ A ⊆ U)) ≫
        AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X U =
      AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map
          (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion X (Set.inter_subset_right : U ∩ A ⊆ A)) ≫
        AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X A := by
    change AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map _ ≫ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map _ =
      AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map _ ≫ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  have heq := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom hcomp (p + q)) z
  change (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X U).f (p + q)
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map
        (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion X (Set.inter_subset_left : U ∩ A ⊆ U))).f (p + q) z) =
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X A).f (p + q)
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map
        (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion X (Set.inter_subset_right : U ∩ A ⊆ A))).f (p + q) z) at heq
  rw [heq]
  exact SupportRelativeCap.relativeCochain_cap_subspace_eq_zero X A p q c _

private def smallCapForCochain (X : TopCat.{0}) (U A : Set X) (p q : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p) :
    (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A).X (p + q) →ₗ[ℤ]
      (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)).X q :=
  ((binarySmallChainDegreePushout X U A (p + q)).desc
    (capOnFirstPiece X U A p q c) 0
    (capOnFirstPiece_intersection X U A p q c)).hom

private theorem smallCapForCochain_left (X : TopCat.{0}) (U A : Set X) (p q : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of U)).X (p + q)) :
    smallCapForCochain X U A p q c
      ((AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularLeft X U A)).f (p + q) z) =
    IntegralCapCoefficients.mixedSingularCap (TopCat.of U) p q
      ((Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U)).f p
        ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c)) z :=
  ConcreteCategory.congr_hom
    ((binarySmallChainDegreePushout X U A (p + q)).inl_desc
      (capOnFirstPiece X U A p q c) 0
      (capOnFirstPiece_intersection X U A p q c)) z

private theorem smallCapForCochain_right (X : TopCat.{0}) (U A : Set X) (p q : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of A)).X (p + q)) :
    smallCapForCochain X U A p q c
      ((AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularRight X U A)).f (p + q) z) = 0 :=
  ConcreteCategory.congr_hom
    ((binarySmallChainDegreePushout X U A (p + q)).inr_desc
      (capOnFirstPiece X U A p q c) 0
      (capOnFirstPiece_intersection X U A p q c)) z

private theorem smallCapForCochain_inclusion (X : TopCat.{0}) (U A : Set X) (p q : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A).X (p + q)) :
    (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U)).f q
      (smallCapForCochain X U A p q c z) =
    IntegralCapCoefficients.mixedSingularCap X p q
      ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c)
      ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A).f (p + q) z) := by
  let f : (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A).X (p + q) ⟶
      ModuleCat.of ℤ ((Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).X q) :=
    ModuleCat.ofHom
      ((((Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U)).f q).hom.restrictScalars ℤ).comp
        (smallCapForCochain X U A p q c))
  let g : (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A).X (p + q) ⟶
      ModuleCat.of ℤ ((Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).X q) :=
    ModuleCat.ofHom
      ((IntegralCapCoefficients.mixedSingularCap X p q
        ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c)).comp
        ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A).f (p + q)).hom)
  have heq : f = g := by
    apply (binarySmallChainDegreePushout X U A (p + q)).hom_ext
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro w
      change (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U)).f q
        (smallCapForCochain X U A p q c
          ((AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularLeft X U A)).f (p + q) w)) =
        IntegralCapCoefficients.mixedSingularCap X p q
          ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c)
          ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A).f (p + q)
            ((AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularLeft X U A)).f (p + q) w))
      rw [smallCapForCochain_left, IntegralCapCoefficients.mixedSingularCap_naturality]
      exact congrArg
        (IntegralCapCoefficients.mixedSingularCap X p q ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c))
        (ConcreteCategory.congr_hom
          (HomologicalComplex.congr_hom (AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion_left X U A) (p + q)) w).symm
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro w
      change (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U)).f q
        (smallCapForCochain X U A p q c
          ((AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularRight X U A)).f (p + q) w)) =
        IntegralCapCoefficients.mixedSingularCap X p q
          ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c)
          ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A).f (p + q)
            ((AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularRight X U A)).f (p + q) w))
      rw [smallCapForCochain_right, map_zero]
      have hw := ConcreteCategory.congr_hom
        (HomologicalComplex.congr_hom (AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion_right X U A) (p + q)) w
      change (AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A).f (p + q)
        ((AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularRight X U A)).f (p + q) w) =
          (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X A).f (p + q) w at hw
      rw [hw]
      exact (SupportRelativeCap.relativeCochain_cap_subspace_eq_zero X A p q c w).symm
  exact ConcreteCategory.congr_hom heq z

/-- Cap a cochain vanishing on `A` with actual `{U,A}`-small integral chains,
obtaining actual rational chains in `U`. -/
def smallSupportedCap (X : TopCat.{0}) (U A : Set X) (p q : ℕ) :
    (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p →ₗ[ℚ]
      ((AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A).X (p + q) →ₗ[ℤ]
        (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)).X q) where
  toFun := smallCapForCochain X U A p q
  map_add' c d := by
    apply LinearMap.ext
    intro z
    apply rationalSubspaceChainInclusion_injective X U q
    simp only [LinearMap.add_apply, map_add, smallCapForCochain_inclusion]
  map_smul' r c := by
    apply LinearMap.ext
    intro z
    apply rationalSubspaceChainInclusion_injective X U q
    simp only [LinearMap.smul_apply, map_smul, smallCapForCochain_inclusion, RingHom.id_apply]

/-- The constructed local cap is exactly the ordinary cap after ambient inclusion. -/
theorem smallSupportedCap_inclusion (X : TopCat.{0}) (U A : Set X) (p q : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A).X (p + q)) :
    (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U)).f q
      (smallSupportedCap X U A p q c z) =
    IntegralCapCoefficients.mixedSingularCap X p q
      ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c)
      ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A).f (p + q) z) :=
  smallCapForCochain_inclusion X U A p q c z

@[simp]
theorem smallSupportedCap_left (X : TopCat.{0}) (U A : Set X) (p q : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of U)).X (p + q)) :
    smallSupportedCap X U A p q c
      ((AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularLeft X U A)).f (p + q) z) =
    IntegralCapCoefficients.mixedSingularCap (TopCat.of U) p q
      ((Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U)).f p
        ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c)) z :=
  smallCapForCochain_left X U A p q c z

@[simp]
theorem smallSupportedCap_right (X : TopCat.{0}) (U A : Set X) (p q : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of A)).X (p + q)) :
    smallSupportedCap X U A p q c
      ((AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularRight X U A)).f (p + q) z) = 0 :=
  smallCapForCochain_right X U A p q c z

end

end OAI.AlgebraicTopology.Duality.Poincare.SmallSupportedCap
