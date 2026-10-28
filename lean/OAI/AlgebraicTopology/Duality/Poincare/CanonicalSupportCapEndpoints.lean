import OAI.AlgebraicTopology.Duality.Poincare.SupportedCapMayerVietoris
import OAI.AlgebraicTopology.Duality.Poincare.CanonicalSmallCapClass

/-! # Canonical Support Cap Endpoints -/

namespace OAI.AlgebraicTopology.Duality.Poincare.CanonicalSupportCapEndpoints

noncomputable section

/-!
# Canonical cap classes at the two Mayer--Vietoris endpoints

Refinement from the common four-open small-chain complex preserves the
actual projected relative class. The union and intersection cap cycles
therefore compute the existing canonical compact-stage cap maps in their
respective open submanifolds.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

/-- The actual union small-cap cycle represents the canonical stage cap
in the union open submanifold. -/
theorem smallSupportUnionCapCycle_class_eq_stage
    (U V : Opens M) (K : U.compactsInside × V.compactsInside)
    (p q : ℕ) (hpq : p + q = 2 * d)
    (a : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
      (TopCat.of M) ((CompactSupportDecomposition.compactPairUnion (X := TopCat.of M) U V K).val : Set M)ᶜ) p)
    (s : (SmallSupportCover.smallSupportScalarChains ℤ (TopCat.of M) (U : Set M) (V : Set M)
      (K.1.val : Set M) (K.2.val : Set M)).X (p + q))
    (hs : (SmallSupportRepresentatives.smallSupportRelativeProjection (TopCat.of M) (U : Set M) (V : Set M)
      (K.1.val : Set M) (K.2.val : Set M)
      ((CompactSupportDecomposition.compactPairUnion (X := TopCat.of M) U V K).val : Set M)ᶜ).f (p + q) s ∈
      Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains (TopCat.of M)
        ((CompactSupportDecomposition.compactPairUnion (X := TopCat.of M) U V K).val : Set M)ᶜ) (p + q))
    (hclass : Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains (TopCat.of M)
        ((CompactSupportDecomposition.compactPairUnion (X := TopCat.of M) U V K).val : Set M)ᶜ) (p + q)
      ⟨(SmallSupportRepresentatives.smallSupportRelativeProjection (TopCat.of M) (U : Set M) (V : Set M)
        (K.1.val : Set M) (K.2.val : Set M)
        ((CompactSupportDecomposition.compactPairUnion (X := TopCat.of M) U V K).val : Set M)ᶜ).f (p + q) s, hs⟩ =
      ComplexManifoldCap.complexCompactClassInDegree d (M := M) (p + q) hpq
        (CompactSupportDecomposition.compactPairUnion (X := TopCat.of M) U V K).val) :
    Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of ↥(U ⊔ V))) q
      (CapMayerVietorisSum.smallSupportUnionCapCycle (TopCat.of M) (U : Set M) (V : Set M)
        (K.1.val : Set M) (K.2.val : Set M) p q a s hs) =
      CapMayerVietorisColimit.complexManifoldOpenStageCap d (M := M) (U ⊔ V)
        (CompactSupportDecomposition.compactPairUnion (X := TopCat.of M) U V K) p q hpq
        (Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of M)
          ((CompactSupportDecomposition.compactPairUnion (X := TopCat.of M) U V K).val : Set M)ᶜ) p a) := by
  let X : TopCat.{0} := TopCat.of M
  let K₁ : Set M := K.1.val
  let K₂ : Set M := K.2.val
  let KS := CompactSupportDecomposition.compactPairUnion (X := X) U V K
  let r := (SmallSupportCover.smallSupportChainToUnion ℤ X U V K₁ K₂).f (p + q) s
  have hr := SupportedCapMayerVietoris.smallSupportUnionRefinement_mem X U V K₁ K₂ (p + q) s hs
  have hproj : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X (KS.val : Set M)ᶜ).f (p + q)
      ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X (U ⊔ V : Opens M) (KS.val : Set M)ᶜ).f
        (p + q) r) =
      (SmallSupportRepresentatives.smallSupportRelativeProjection X U V K₁ K₂ (KS.val : Set M)ᶜ).f (p + q) s :=
    congrArg ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X (KS.val : Set M)ᶜ).f (p + q))
      (ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
        (SmallSupportCover.smallSupportChainToUnion_integral_inclusion X U V K₁ K₂) (p + q)) s)
  have hclass' : Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X (KS.val : Set M)ᶜ) (p + q)
      ⟨(AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X (KS.val : Set M)ᶜ).f (p + q)
        ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X (U ⊔ V : Opens M) (KS.val : Set M)ᶜ).f
          (p + q) r), hr⟩ =
      ComplexManifoldCap.complexCompactClassInDegree d (M := M) (p + q) hpq KS.val :=
    (congrArg (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X (KS.val : Set M)ᶜ) (p + q))
      (Subtype.ext hproj)).trans hclass
  exact CanonicalSmallCapClass.smallSupportedRelativeCapCycle_class_eq_openStageCap d (M := M)
    (U ⊔ V) KS p q hpq a r hr hclass'

/-- The actual intersection small-cap cycle represents the canonical stage cap
in the intersection open submanifold. -/
theorem smallSupportIntersectionCapCycle_class_eq_stage
    (U V : Opens M) (K : U.compactsInside × V.compactsInside)
    (p q : ℕ) (hpq : p + q = 2 * d)
    (a : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
      (TopCat.of M) ((CompactSupportPairIndex.compactPairIntersection (X := TopCat.of M) U V K).val : Set M)ᶜ) p)
    (s : (SmallSupportCover.smallSupportScalarChains ℤ (TopCat.of M) (U : Set M) (V : Set M)
      (K.1.val : Set M) (K.2.val : Set M)).X (p + q))
    (hs : (SmallSupportRepresentatives.smallSupportRelativeProjection (TopCat.of M) (U : Set M) (V : Set M)
      (K.1.val : Set M) (K.2.val : Set M)
      ((CompactSupportPairIndex.compactPairIntersection (X := TopCat.of M) U V K).val : Set M)ᶜ).f (p + q) s ∈
      Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains (TopCat.of M)
        ((CompactSupportPairIndex.compactPairIntersection (X := TopCat.of M) U V K).val : Set M)ᶜ) (p + q))
    (hclass : Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains (TopCat.of M)
        ((CompactSupportPairIndex.compactPairIntersection (X := TopCat.of M) U V K).val : Set M)ᶜ) (p + q)
      ⟨(SmallSupportRepresentatives.smallSupportRelativeProjection (TopCat.of M) (U : Set M) (V : Set M)
        (K.1.val : Set M) (K.2.val : Set M)
        ((CompactSupportPairIndex.compactPairIntersection (X := TopCat.of M) U V K).val : Set M)ᶜ).f (p + q) s, hs⟩ =
      ComplexManifoldCap.complexCompactClassInDegree d (M := M) (p + q) hpq
        (CompactSupportPairIndex.compactPairIntersection (X := TopCat.of M) U V K).val) :
    Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of ↥(U ⊓ V))) q
      (SupportedCapMayerVietoris.smallSupportIntersectionCapCycle (TopCat.of M) (U : Set M) (V : Set M)
        (K.1.val : Set M) (K.2.val : Set M) p q a s hs) =
      CapMayerVietorisColimit.complexManifoldOpenStageCap d (M := M) (U ⊓ V)
        (CompactSupportPairIndex.compactPairIntersection (X := TopCat.of M) U V K) p q hpq
        (Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of M)
          ((CompactSupportPairIndex.compactPairIntersection (X := TopCat.of M) U V K).val : Set M)ᶜ) p a) := by
  let X : TopCat.{0} := TopCat.of M
  let K₁ : Set M := K.1.val
  let K₂ : Set M := K.2.val
  let KS := CompactSupportPairIndex.compactPairIntersection (X := X) U V K
  let r := (SmallSupportCover.smallSupportChainToIntersection ℤ X U V K₁ K₂).f (p + q) s
  have hr := SupportedCapMayerVietoris.smallSupportIntersectionRefinement_mem X U V K₁ K₂ (p + q) s hs
  have hproj : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X (KS.val : Set M)ᶜ).f (p + q)
      ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X (U ⊓ V : Opens M) (KS.val : Set M)ᶜ).f
        (p + q) r) =
      (SmallSupportRepresentatives.smallSupportRelativeProjection X U V K₁ K₂ (KS.val : Set M)ᶜ).f (p + q) s :=
    congrArg ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X (KS.val : Set M)ᶜ).f (p + q))
      (ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
        (SmallSupportCover.smallSupportChainToIntersection_integral_inclusion X U V K₁ K₂) (p + q)) s)
  have hclass' : Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X (KS.val : Set M)ᶜ) (p + q)
      ⟨(AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X (KS.val : Set M)ᶜ).f (p + q)
        ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X (U ⊓ V : Opens M) (KS.val : Set M)ᶜ).f
          (p + q) r), hr⟩ =
      ComplexManifoldCap.complexCompactClassInDegree d (M := M) (p + q) hpq KS.val :=
    (congrArg (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X (KS.val : Set M)ᶜ) (p + q))
      (Subtype.ext hproj)).trans hclass
  exact CanonicalSmallCapClass.smallSupportedRelativeCapCycle_class_eq_openStageCap d (M := M)
    (U ⊓ V) KS p q hpq a r hr hclass'

end

end OAI.AlgebraicTopology.Duality.Poincare.CanonicalSupportCapEndpoints
