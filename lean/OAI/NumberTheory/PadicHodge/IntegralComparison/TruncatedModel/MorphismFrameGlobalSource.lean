import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalSourceCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismPresheafFrameGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GlobalFrame

/-! # Morphism Frame Global Source -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameGlobalSource.Stages

noncomputable section

section

/-! Original frame-to-global comparison under source-cover refinement. -/

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
  (sq : f₁ ≫ u.left = v.left ≫ f₂)
  (I₁ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₁) n))
  (I₂ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₂) n))

attribute [local instance] MorphismGlobalSourceCohomology.sourceTypedEdgeEpi

abbrev sourceCore :=
  MorphismPresheafFrameGlobal.Comparison.source.{1,2} p k n u
    (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) _
    (MorphismGlobalRefinementBase.Maps.sourceSections p k n f₁ I₁)
    (FrameInjective.Comparison.map p k n X₁ Y₁ f₁ hp₁ I₁)
    (MorphismFrameInjectiveHomotopy.sourceComparison p k n u f₁ hp₁ I₁)
    (MorphismFrameRefinementCoordinates.Comparison.source_coordinates p k n u f₁ hp₁ I₁)

end

/-! Original frame-to-global comparison under source-cover refinement. -/

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
  (sq : f₁ ≫ u.left = v.left ≫ f₂)
  (I₁ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₁) n))
  (I₂ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₂) n))

variable (q : ℕ)
attribute [local instance] MorphismGlobalSourceCohomology.sourceTypedEdgeEpi

abbrev sourceData :=
  sourceCore p k n u f₁ hp₁ I₁
    (MorphismGlobalCone.sourceGlobal p k n I₁)
    (MorphismGlobalTypedEdges.sourceCone p k n f₁ I₁)
    (MorphismGlobalTypedEdges.sourceOld p k n f₁ I₁)
    (MorphismGlobalTypedEdges.sourceNew p k n u f₁ I₁)
    (MorphismGlobalTypedEdges.source_old p k n f₁ I₁)
    (MorphismGlobalTypedEdges.source_new p k n u f₁ I₁)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameGlobalSource.Stages
