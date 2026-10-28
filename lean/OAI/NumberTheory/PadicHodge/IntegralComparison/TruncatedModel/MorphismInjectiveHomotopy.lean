import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismRefinedResolution
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactInjective
import OAI.NumberTheory.PadicHodge.GeometricComparison.AugmentedNaturality

/-! # Morphism Injective Homotopy -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismInjectiveHomotopy

noncomputable section

/-! The original model Cech-to-injective comparisons agree up to cochain homotopy through the common geometric source resolution. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))} [Smooth X₁.hom] [Smooth X₂.hom] [IsProper X₁.hom] [IsProper X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of k))}
  [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom
    (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom
    (Truncated.Witt.reduction p k n))))
  (sq : f₁ ≫ u.left = v.left ≫ f₂)

variable
  (I₁ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₁) n))
  (I₂ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₂) n))

open OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismData.Frames
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Over.Hom.left v) (MorphismData.Frames.ambient_over p k v) n
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Sheaves.structureTransport (Over.Hom.left v) (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismData.Frames.ambient_over p k v) n
local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSourceResolution.complex p k n u Y₁ f₁ hp₁
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSourceResolution.augmentation p k n u Y₁ f₁ hp₁
local notation "h" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSourceResolution.augmentation_quasiIso p k n u Y₁ f₁ hp₁

def comparison : L ⟶ I₁.cocomplex := GeometricComparison.AugmentedInjective.AugmentedInjectiveComparison.map L a h I₁

omit [IsSeparated Y₂.hom] in
theorem augmentation : a ≫ comparison p k n u f₁ hp₁ I₁ = I₁.ι :=
  GeometricComparison.AugmentedInjective.AugmentedInjectiveComparison.augmentation L a h I₁

def sourceHomotopy : Homotopy (CechInjective.Comparison.map p k n X₁ Y₁ f₁ hp₁ I₁)
    (MorphismRefinedResolution.sourceMap p k n u f₁ hp₁ ≫ comparison p k n u f₁ hp₁ I₁) :=
  CechInjective.Comparison.homotopy p k n X₁ Y₁ f₁ hp₁ I₁ _
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ comparison p k n u f₁ hp₁ I₁)
        (MorphismRefinedResolution.source_augmentation p k n u f₁ hp₁)).trans
          (augmentation p k n u f₁ hp₁ I₁)))

def targetHomotopy : Homotopy
    (((T).mapHomologicalComplex (.up ℕ)).map (CechInjective.Comparison.map p k n X₂ Y₂ f₂ hp₂ I₂) ≫
      GeometricComparison.ExactInjective.ExactInjectivePullback.map T e I₂ I₁)
    (MorphismRefinedResolution.targetMap p k n u v f₁ f₂ hp₁ hp₂ sq ≫ comparison p k n u f₁ hp₁ I₁) :=
  GeometricComparison.AugmentedNaturality.AugmentedComparisonNaturality.homotopy T e
    (CechSheafResolution.complex p k n X₂ Y₂ f₂ hp₂)
    (CechSheafResolution.augmentation p k n X₂ Y₂ f₂ hp₂)
    (CechSheafResolution.augmentation_quasiIso p k n X₂ Y₂ f₂ hp₂)
    L a h I₂ I₁
    (MorphismRefinedResolution.targetMap p k n u v f₁ f₂ hp₁ hp₂ sq)
    (GeometricComparison.ExactInjective.ExactInjectivePullback.map T e I₂ I₁)
    (MorphismRefinedResolution.target_augmentation p k n u v f₁ f₂ hp₁ hp₂ sq)
    (GeometricComparison.ExactInjective.ExactInjectivePullback.augmentation_map T e I₂ I₁)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismInjectiveHomotopy
