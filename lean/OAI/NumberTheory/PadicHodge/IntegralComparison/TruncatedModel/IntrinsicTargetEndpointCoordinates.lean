import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicPresheafTargetComposite
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTargetEdge
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSourceHomologyCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismIntrinsicBase
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCoefficientMapCoordinates

/-! # Intrinsic Target Endpoint Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicTargetEndpointCoordinates.MorphismIntrinsic

noncomputable section

/-! Carry the native target endpoint obligations through the original
frame maps, homology comparisons, and coefficient isomorphisms. -/

section
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private abbrev domainOf {C : Type*} [Category* C] {X Y : C} (_f : X ⟶ Y) : C := X
private abbrev codomainOf {C : Type*} [Category* C] {X Y : C} (_f : X ⟶ Y) : C := Y

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of k))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (sq : f₁ ≫ u.left = v.left ≫ f₂)
  (I₁ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₁) n))
  (I₂ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₂) n))

attribute [local instance] MorphismGlobalSourceCohomology.targetTypedEdgeEpi

abbrev targetCoefficientCore :=
  IntrinsicPresheafTargetComposite.MorphismIntrinsicEndpoints.target p k n u _
    (MorphismGlobalRefinementBase.Maps.targetSections p k n f₂ I₂)
    (FrameInjective.Comparison.map p k n X₂ Y₂ f₂ hp₂ I₂)
    (MorphismFrameInjectiveHomotopy.targetComparison p k n u f₂ hp₂ I₂)
    (MorphismFrameRefinementCoordinates.Comparison.target_coordinates p k n u f₂ hp₂ I₂)

abbrev targetSourceCoefficients :=
  targetCoefficientCore p k n u f₂ hp₂ I₂
    (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ)
      ((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left).op ⋙
        FrameDiagonalMap.source p k n X₁ Y₁ f₁ hp₁))
    (MorphismCommonGlobal.sourceSections p k n u f₁ I₁)

abbrev targetFrameMap :=
  targetSourceCoefficients p k n u f₁ f₂ hp₁ hp₂ I₁ I₂
    (MorphismFrameDiagonal.map p k n u v f₁ f₂ hp₁ hp₂ sq)

abbrev targetSectionMap :=
  targetFrameMap p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂
    (MorphismSectionHomotopy.injectiveMap p k n u v f₁ f₂ sq I₁ I₂)

abbrev targetComparisonMap :=
  targetSectionMap p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂
    (MorphismFrameInjectiveHomotopy.sourceComparison p k n u f₁ hp₁ I₁)

abbrev targetCore :=
  targetComparisonMap p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂
    (MorphismFrameInjectiveHomotopy.homotopy p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂)

abbrev targetData :=
  targetCore p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂
    (MorphismGlobalCone.targetGlobal p k n I₂)
    (MorphismGlobalTypedEdges.targetCone p k n f₂ I₂)
    (MorphismGlobalTypedEdges.targetOld p k n f₂ I₂)
    (MorphismGlobalTypedEdges.targetNew p k n u f₂ I₂)
    (MorphismGlobalTypedEdges.target_old p k n f₂ I₂)
    (MorphismGlobalTypedEdges.target_new p k n u f₂ I₂)

end

section
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)

def output (Y : Over (Spec (CommRingCat.of k))) (q : ℕ) :
    ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) :=
  ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
    (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
      (J := Ideal.span {(p : WittVector p k)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
      (Witt.Crystalline.wittStructureMap p k Y) n q)

variable
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of k))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (sq : f₁ ≫ u.left = v.left ≫ f₂)
  (I₁ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₁) n))
  (I₂ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₂) n))

variable (q : ℕ)
attribute [local instance] MorphismGlobalSourceCohomology.targetTypedEdgeEpi
attribute [local irreducible] HomologicalComplex.homology HomologicalComplex.homologyMap

abbrev targetGroups :=
  targetData p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂ q
    ((MorphismGlobalCone.sourceGlobal p k n I₁).homology q)
    (codomainOf (GlobalTypedGeometricHomology.Morphism.pullback p k n v q))
    (domainOf (GlobalTypedGeometricHomology.Morphism.pullback p k n v q))

abbrev targetGlobalMap :=
  targetGroups p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂ q
    (GlobalTypedGeometricHomology.Morphism.global p k n v I₁ I₂ q)

abbrev targetSourceEdge :=
  targetGlobalMap p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂ q
    (HomologicalComplex.homologyMap
      (MorphismCommonGlobal.sourceEdge p k n u f₁ I₁) q)

abbrev targetNewComparison :=
  targetSourceEdge p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂ q
    (MorphismSourceHomology.Raw.comparison p k n u f₁ I₁ q)

abbrev targetPullback :=
  targetNewComparison p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂ q
    (GlobalTypedGeometricHomology.Morphism.pullback p k n v q)

abbrev targetOldComparison :=
  targetPullback p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂ q
    (GlobalTypedGeometricHomology.Morphism.targetOldAtPullback p k n v f₂ I₂ q)

abbrev targetGlobalComparisons :=
  targetOldComparison p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂ q
    (GlobalTypedGeometricHomology.Morphism.sourceGlobalAtPullback p k n v I₁ q)

abbrev targetCohomology :=
  targetGlobalComparisons p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂ q
    (GlobalTypedGeometricHomology.Morphism.targetGlobalAtPullback p k n v I₂ q)

abbrev targetEdge :=
  targetCohomology p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂ q
    (MorphismTargetEdge.edge p k n u v f₁ f₂ sq I₁ I₂ q)

abbrev targetSource :=
  targetEdge p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂ q
    (MorphismSourceHomologyCoordinates.Raw.source_new p k n u f₁ I₁ q)

abbrev targetGlobal :=
  targetSource p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂ q
    (GlobalTypedGeometricHomology.Morphism.comparison p k n v I₁ I₂ q)

abbrev frame :=
  targetGlobal p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂ q
    (MorphismGlobalTypedHomology.target_old p k n f₂ I₂ q)

end

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of k))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (sq : f₁ ≫ u.left = v.left ≫ f₂)
  (I₁ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₁) n))
  (I₂ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₂) n))

variable (i : ℕ)

abbrev targetIsos :=
  frame p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂ i _ _ _
    (MorphismIntrinsicCoordinates.Intrinsic.targetIso p k n f₂ hp₂)
    (MorphismCoefficientCech.ordinaryTargetIso p k n u f₂ hp₂)
    (MorphismCoefficientCech.ordinarySourceIso p k n u f₁ hp₁)

abbrev targetMap :=
  targetIsos p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂ i
    (MorphismIntrinsicCoordinates.Intrinsic.targetMap p k n u)

abbrev targetGeometricMap :=
  targetMap p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂ i
    (MorphismOrdinaryCech.Ordinary.ordinaryMap p k n u)

abbrev targetRefinementSquare :=
  targetGeometricMap p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂ i
    (MorphismIntrinsicCoordinates.Intrinsic.target p k n u f₂ hp₂).symm

abbrev target :=
  targetRefinementSquare p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂ i
    (MorphismCoefficientMapCoordinates.ordinary_natural
      p k n u v f₁ f₂ hp₁ hp₂ sq)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicTargetEndpointCoordinates.MorphismIntrinsic
