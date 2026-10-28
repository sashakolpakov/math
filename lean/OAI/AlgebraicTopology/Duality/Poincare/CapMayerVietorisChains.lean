import OAI.AlgebraicTopology.Duality.Poincare.SmallSupportedCapBoundary
import OAI.AlgebraicTopology.Duality.Poincare.SmallSupportCover
import OAI.AlgebraicTopology.Duality.Poincare.CapMayerVietorisConnecting

/-! # Cap Mayer Vietoris Chains -/

namespace OAI.AlgebraicTopology.Duality.Poincare.CapMayerVietorisChains

noncomputable section

/-!
# Actual supported cap chains for Mayer--Vietoris

These identities use one integral chain subordinate to the simultaneous
four-open cover. The two local caps and their intersection cap are actual
chains in the indicated subspaces. A relative-cycle condition, rather than
an absolute-cycle assumption, kills the unwanted boundary term.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A local supported cap vanishes when its actual ambient relative chain
projection vanishes. No assertion about supports of homology classes is used. -/
theorem smallSupportedCap_eq_zero_of_projection
    (X : TopCat.{0}) (U A : Set X) (p q : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A).X (p + q))
    (hz : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f (p + q)
      ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A).f (p + q) z) = 0) :
    SmallSupportedCap.smallSupportedCap X U A p q c z = 0 := by
  apply SmallSupportedCap.rationalSubspaceChainInclusion_injective X U q
  rw [map_zero, SmallSupportedCap.smallSupportedCap_inclusion]
  rw [← SupportRelativeCap.relativeCap_projection, hz, map_zero]

/-- The cap boundary law on a relative-cycle representative. The ordinary
chain may have a nonzero boundary, provided that boundary projects to zero. -/
theorem smallSupportedCap_boundary_of_relativeCycle
    (X : TopCat.{0}) (U A : Set X) (p q : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A).X (p + q + 1))
    (hz : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f (p + q)
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d (p + q + 1) (p + q)
        ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A).f (p + q + 1) z)) = 0) :
    (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)).d (q + 1) q
        (SmallSupportedCap.smallSupportedCap X U A p (q + 1) c z) =
      ((-1 : ℤ) ^ (p + 1)) • SmallSupportedCap.smallSupportedCap X U A (p + 1) q
        ((Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).d p (p + 1) c)
        (SmallSupportedCapBoundary.binarySmallChainCast X U A (by omega : p + q + 1 = (p + 1) + q) z) := by
  rw [SmallSupportedCapBoundary.boundary_smallSupportedCap]
  have hd := ConcreteCategory.congr_hom
    ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A).comm (p + q + 1) (p + q)) z
  change (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d (p + q + 1) (p + q)
      ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A).f (p + q + 1) z) =
    (AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A).f (p + q)
      ((AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A).d (p + q + 1) (p + q) z) at hd
  have hzero := smallSupportedCap_eq_zero_of_projection X U A p q c
    ((AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A).d (p + q + 1) (p + q) z) (by
      rw [← hd]
      exact hz)
  rw [hzero, zero_sub, pow_succ, mul_smul, neg_one_smul]

/-- Changing the local target and relative presentation preserves the
actual cap chain whenever both underlying cochain and chain agree. -/
theorem smallSupportedCap_subset
    (X : TopCat.{0}) (U W A B : Set X) (hWU : W ⊆ U) (p q : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p)
    (b : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B).X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A).X (p + q))
    (w : (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X W B).X (p + q))
    (hc : (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c =
      (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X B).f p b)
    (hz : (AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A).f (p + q) z =
      (AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X W B).f (p + q) w) :
    SmallSupportedCap.smallSupportedCap X U A p q c z =
      (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion X hWU)).f q
        (SmallSupportedCap.smallSupportedCap X W B p q b w) := by
  apply SmallSupportedCap.rationalSubspaceChainInclusion_injective X U q
  rw [SmallSupportedCap.smallSupportedCap_inclusion]
  have hcomp :
      Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion X hWU) ≫
        Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) =
      Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X W) := by
    change (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map _ ≫
      (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map _ = (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map _
    rw [← Functor.map_comp]
    rfl
  have he := ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom hcomp q) (SmallSupportedCap.smallSupportedCap X W B p q b w)
  change (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U)).f q
      ((Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion X hWU)).f q
        (SmallSupportedCap.smallSupportedCap X W B p q b w)) =
    (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X W)).f q
      (SmallSupportedCap.smallSupportedCap X W B p q b w) at he
  rw [he, SmallSupportedCap.smallSupportedCap_inclusion, hc, hz]

/-- The relative-cycle cap boundary in a smaller subspace, when the actual
coboundary is represented by a cochain supported in that subspace. -/
theorem smallSupportedCap_boundary_to_subset
    (X : TopCat.{0}) (U W A B : Set X) (hWU : W ⊆ U) (p q : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p)
    (b : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B).X (p + 1))
    (z : (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A).X (p + q + 1))
    (w : (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X W B).X ((p + 1) + q))
    (hz : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f (p + q)
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d (p + q + 1) (p + q)
        ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A).f (p + q + 1) z)) = 0)
    (hc : (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f (p + 1)
        ((Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).d p (p + 1) c) =
      (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X B).f (p + 1) b)
    (hw : (AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A).f ((p + 1) + q)
        (SmallSupportedCapBoundary.binarySmallChainCast X U A (by omega : p + q + 1 = (p + 1) + q) z) =
      (AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X W B).f ((p + 1) + q) w) :
    (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)).d (q + 1) q
        (SmallSupportedCap.smallSupportedCap X U A p (q + 1) c z) =
      ((-1 : ℤ) ^ (p + 1)) •
        (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion X hWU)).f q
          (SmallSupportedCap.smallSupportedCap X W B (p + 1) q b w) := by
  rw [smallSupportedCap_boundary_of_relativeCycle X U A p q c z hz]
  exact congrArg (fun x => ((-1 : ℤ) ^ (p + 1)) • x)
    (smallSupportedCap_subset X U W A B hWU (p + 1) q _ b _ w hc hw)

/-- Degree transport on the genuine simultaneous small-chain complex. -/
abbrev smallSupportChainCast (X : TopCat.{0}) (U V K L : Set X)
    {m n : ℕ} (h : m = n) :
    (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X m →ₗ[ℤ]
      (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X n :=
  Products.Cap.chainCast (R := ℤ) (SmallSupportCover.smallSupportSubcomplex X U V K L : SSet) h

/-- The actual ambient inclusion commutes with transport of degree. -/
theorem smallSupportChainInclusion_cast (X : TopCat.{0}) (U V K L : Set X)
    {m n : ℕ} (h : m = n) (z : (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X m) :
    (AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion X (SmallSupportCover.smallSupportCover X U V K L)).f n
        (smallSupportChainCast X U V K L h z) =
      Products.Cap.chainCast (R := ℤ) (TopCat.toSSet.obj X) h
        ((AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion X (SmallSupportCover.smallSupportCover X U V K L)).f m z) := by
  subst n
  rfl

/-- The left cap of the common, genuinely small integral chain. -/
def smallSupportLeftCap (X : TopCat.{0}) (U V K L : Set X) (p q : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X Kᶜ).X p)
    (z : (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X (p + q)) :
    (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)).X q :=
  SmallSupportedCap.smallSupportedCap X U Kᶜ p q c ((SmallSupportCover.smallSupportChainToLeft ℤ X U V K L).f (p + q) z)

/-- The right cap of the same integral chain. -/
def smallSupportRightCap (X : TopCat.{0}) (U V K L : Set X) (p q : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X Lᶜ).X p)
    (z : (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X (p + q)) :
    (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of V)).X q :=
  SmallSupportedCap.smallSupportedCap X V Lᶜ p q c ((SmallSupportCover.smallSupportChainToRight ℤ X U V K L).f (p + q) z)

/-- The intersection cap of the same integral chain. -/
def smallSupportIntersectionCap (X : TopCat.{0}) (U V K L : Set X) (p q : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (K ∩ L)ᶜ).X p)
    (z : (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X (p + q)) :
    (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (U ∩ V : Set X))).X q :=
  SmallSupportedCap.smallSupportedCap X (U ∩ V) (K ∩ L)ᶜ p q c
    ((SmallSupportCover.smallSupportChainToIntersection ℤ X U V K L).f (p + q) z)

/-- The ambient value of the left local cap is the ordinary mixed cap. -/
theorem smallSupportLeftCap_inclusion (X : TopCat.{0}) (U V K L : Set X) (p q : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X Kᶜ).X p)
    (z : (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X (p + q)) :
    (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U)).f q
        (smallSupportLeftCap X U V K L p q c z) =
      IntegralCapCoefficients.mixedSingularCap X p q
        ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X Kᶜ).f p c)
        ((AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion X (SmallSupportCover.smallSupportCover X U V K L)).f (p + q) z) := by
  rw [smallSupportLeftCap, SmallSupportedCap.smallSupportedCap_inclusion]
  exact congrArg (IntegralCapCoefficients.mixedSingularCap X p q
    ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X Kᶜ).f p c))
    (ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
      (SmallSupportCover.smallSupportChainToLeft_integral_inclusion X U V K L) (p + q)) z)

/-- The ambient value of the right local cap is the ordinary mixed cap. -/
theorem smallSupportRightCap_inclusion (X : TopCat.{0}) (U V K L : Set X) (p q : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X Lᶜ).X p)
    (z : (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X (p + q)) :
    (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X V)).f q
        (smallSupportRightCap X U V K L p q c z) =
      IntegralCapCoefficients.mixedSingularCap X p q
        ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X Lᶜ).f p c)
        ((AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion X (SmallSupportCover.smallSupportCover X U V K L)).f (p + q) z) := by
  rw [smallSupportRightCap, SmallSupportedCap.smallSupportedCap_inclusion]
  exact congrArg (IntegralCapCoefficients.mixedSingularCap X p q
    ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X Lᶜ).f p c))
    (ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
      (SmallSupportCover.smallSupportChainToRight_integral_inclusion X U V K L) (p + q)) z)

/-- The ambient value of the intersection local cap is the ordinary mixed cap. -/
theorem smallSupportIntersectionCap_inclusion (X : TopCat.{0}) (U V K L : Set X) (p q : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (K ∩ L)ᶜ).X p)
    (z : (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X (p + q)) :
    (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X (U ∩ V))).f q
        (smallSupportIntersectionCap X U V K L p q c z) =
      IntegralCapCoefficients.mixedSingularCap X p q
        ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (K ∩ L)ᶜ).f p c)
        ((AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion X (SmallSupportCover.smallSupportCover X U V K L)).f (p + q) z) := by
  rw [smallSupportIntersectionCap, SmallSupportedCap.smallSupportedCap_inclusion]
  exact congrArg (IntegralCapCoefficients.mixedSingularCap X p q
    ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (K ∩ L)ᶜ).f p c))
    (ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
      (SmallSupportCover.smallSupportChainToIntersection_integral_inclusion X U V K L) (p + q)) z)

/-- The left and intersection refinements have exactly the same ambient
chain, including after transport to an equal degree. -/
theorem smallSupportLeft_intersection_cast (X : TopCat.{0}) (U V K L : Set X)
    {m n : ℕ} (h : m = n) (z : (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X m) :
    (AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U Kᶜ).f n
        (SmallSupportedCapBoundary.binarySmallChainCast X U Kᶜ h
          ((SmallSupportCover.smallSupportChainToLeft ℤ X U V K L).f m z)) =
      (AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X (U ∩ V) (K ∩ L)ᶜ).f n
        ((SmallSupportCover.smallSupportChainToIntersection ℤ X U V K L).f n
          (smallSupportChainCast X U V K L h z)) := by
  subst n
  exact (ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (SmallSupportCover.smallSupportChainToLeft_integral_inclusion X U V K L) m) z).trans
    (ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
      (SmallSupportCover.smallSupportChainToIntersection_integral_inclusion X U V K L) m) z).symm

/-- The same actual-chain agreement for the right refinement. -/
theorem smallSupportRight_intersection_cast (X : TopCat.{0}) (U V K L : Set X)
    {m n : ℕ} (h : m = n) (z : (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X m) :
    (AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X V Lᶜ).f n
        (SmallSupportedCapBoundary.binarySmallChainCast X V Lᶜ h
          ((SmallSupportCover.smallSupportChainToRight ℤ X U V K L).f m z)) =
      (AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X (U ∩ V) (K ∩ L)ᶜ).f n
        ((SmallSupportCover.smallSupportChainToIntersection ℤ X U V K L).f n
          (smallSupportChainCast X U V K L h z)) := by
  subst n
  exact (ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (SmallSupportCover.smallSupportChainToRight_integral_inclusion X U V K L) m) z).trans
    (ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
      (SmallSupportCover.smallSupportChainToIntersection_integral_inclusion X U V K L) m) z).symm

/-- The boundary of the actual left cap is the signed inclusion of the
intersection cap, when its cochain is the prescribed coboundary. -/
theorem smallSupportLeftCap_boundary (X : TopCat.{0}) (U V K L : Set X) (p q : ℕ)
    (b : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X Kᶜ).X p)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (K ∩ L)ᶜ).X (p + 1))
    (z : (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X (p + q + 1))
    (hz : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X Kᶜ).f (p + q)
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d (p + q + 1) (p + q)
        ((AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion X (SmallSupportCover.smallSupportCover X U V K L)).f (p + q + 1) z)) = 0)
    (hc : (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X Kᶜ).f (p + 1)
        ((Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X Kᶜ).d p (p + 1) b) =
      (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (K ∩ L)ᶜ).f (p + 1) c) :
    (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)).d (q + 1) q
        (smallSupportLeftCap X U V K L p (q + 1) b z) =
      ((-1 : ℤ) ^ (p + 1)) •
        (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ)
          (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion X (Set.inter_subset_left : U ∩ V ⊆ U))).f q
          (smallSupportIntersectionCap X U V K L (p + 1) q c
            (smallSupportChainCast X U V K L (by omega : p + q + 1 = (p + 1) + q) z)) := by
  apply smallSupportedCap_boundary_to_subset X U (U ∩ V) Kᶜ (K ∩ L)ᶜ
    Set.inter_subset_left p q b c _ _ ?_ hc
    (smallSupportLeft_intersection_cast X U V K L _ z)
  have hi := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (SmallSupportCover.smallSupportChainToLeft_integral_inclusion X U V K L) (p + q + 1)) z
  change (AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U Kᶜ).f (p + q + 1)
      ((SmallSupportCover.smallSupportChainToLeft ℤ X U V K L).f (p + q + 1) z) =
    (AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion X (SmallSupportCover.smallSupportCover X U V K L)).f (p + q + 1) z at hi
  rw [hi]
  exact hz

/-- The matching signed boundary identity for the right cap. -/
theorem smallSupportRightCap_boundary (X : TopCat.{0}) (U V K L : Set X) (p q : ℕ)
    (b : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X Lᶜ).X p)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (K ∩ L)ᶜ).X (p + 1))
    (z : (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X (p + q + 1))
    (hz : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X Lᶜ).f (p + q)
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d (p + q + 1) (p + q)
        ((AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion X (SmallSupportCover.smallSupportCover X U V K L)).f (p + q + 1) z)) = 0)
    (hc : (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X Lᶜ).f (p + 1)
        ((Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X Lᶜ).d p (p + 1) b) =
      (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (K ∩ L)ᶜ).f (p + 1) c) :
    (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of V)).d (q + 1) q
        (smallSupportRightCap X U V K L p (q + 1) b z) =
      ((-1 : ℤ) ^ (p + 1)) •
        (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ)
          (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion X (Set.inter_subset_right : U ∩ V ⊆ V))).f q
          (smallSupportIntersectionCap X U V K L (p + 1) q c
            (smallSupportChainCast X U V K L (by omega : p + q + 1 = (p + 1) + q) z)) := by
  apply smallSupportedCap_boundary_to_subset X V (U ∩ V) Lᶜ (K ∩ L)ᶜ
    Set.inter_subset_right p q b c _ _ ?_ hc
    (smallSupportRight_intersection_cast X U V K L _ z)
  have hi := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (SmallSupportCover.smallSupportChainToRight_integral_inclusion X U V K L) (p + q + 1)) z
  change (AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X V Lᶜ).f (p + q + 1)
      ((SmallSupportCover.smallSupportChainToRight ℤ X U V K L).f (p + q + 1) z) =
    (AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion X (SmallSupportCover.smallSupportCover X U V K L)).f (p + q + 1) z at hi
  rw [hi]
  exact hz

end

end OAI.AlgebraicTopology.Duality.Poincare.CapMayerVietorisChains
