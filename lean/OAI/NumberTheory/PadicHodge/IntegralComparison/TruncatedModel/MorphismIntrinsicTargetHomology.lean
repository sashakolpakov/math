import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismIntrinsicTarget
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSourceHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismPresheafIntrinsicTarget
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalCohomology

/-! # Morphism Intrinsic Target Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismIntrinsicTargetHomology.IntrinsicStages

noncomputable section

/-! The native bounded crystalline frame comparison commutes with
actual model pullback through its original common affine cover. -/

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

variable (q : ℕ)
attribute [local instance] MorphismGlobalSourceCohomology.targetTypedEdgeEpi

private abbrev sourceBounded : ModuleCat.{2}
    (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) :=
  ModuleCat.of _ (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
    (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₁) n q)

private abbrev targetBounded : ModuleCat.{2}
    (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) :=
  ModuleCat.of _ (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
    (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₂) n q)

abbrev targetGroups :=
  MorphismIntrinsicTarget.IntrinsicStages.targetData p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂ q
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

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismIntrinsicTargetHomology.IntrinsicStages
