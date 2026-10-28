import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismPresheafIntrinsicTarget
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalCohomology

/-! # Morphism Intrinsic Target -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismIntrinsicTarget.IntrinsicStages

noncomputable section

section

/-! The native bounded crystalline frame comparison commutes with
actual model pullback through its original common affine cover. -/

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

attribute [local instance] MorphismGlobalSourceCohomology.targetTypedEdgeEpi

abbrev targetCoefficientCore :=
  MorphismPresheafIntrinsicTarget.Intrinsic.target.{1,2} p k n u
    (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) _
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

end

/-! The native bounded crystalline frame comparison commutes with
actual model pullback through its original common affine cover. -/

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

variable (q : ℕ)
attribute [local instance] MorphismGlobalSourceCohomology.targetTypedEdgeEpi

abbrev targetData :=
  targetCore p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂
    (MorphismGlobalCone.targetGlobal p k n I₂)
    (MorphismGlobalTypedEdges.targetCone p k n f₂ I₂)
    (MorphismGlobalTypedEdges.targetOld p k n f₂ I₂)
    (MorphismGlobalTypedEdges.targetNew p k n u f₂ I₂)
    (MorphismGlobalTypedEdges.target_old p k n f₂ I₂)
    (MorphismGlobalTypedEdges.target_new p k n u f₂ I₂)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismIntrinsicTarget.IntrinsicStages
