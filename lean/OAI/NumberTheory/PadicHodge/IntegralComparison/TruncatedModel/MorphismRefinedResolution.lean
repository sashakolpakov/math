import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSourceResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCech
import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ComplexTransportNaturality

/-! # Morphism Refined Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismRefinedResolution

noncomputable section

/-! The original model resolutions map, with their original augmentations, into one common geometric source resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

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

open OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismData.Frames
local notation "W" => WittVector p k
local notation "w₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y₁
local notation "w₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y₂
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p)
  (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Over.Hom.left v) (MorphismData.Frames.ambient_over p k v) n
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionDiagram.diagram p k n X₂ Y₂ f₂ hp₂
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionDiagram.diagram p k n X₁ Y₁ f₁ hp₁
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCover.pairs p k n u
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Sheaves.structureTransport (Over.Hom.left v) (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismData.Frames.ambient_over p k v) n
local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSourceResolution.complex p k n u Y₁ f₁ hp₁
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSourceResolution.augmentation p k n u Y₁ f₁ hp₁

local instance sourceSeparated : IsSeparated w₁ := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance
local instance targetSeparated : IsSeparated w₂ := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance
local instance sourceCoproducts : HasCoproducts.{0}
    (BoundedCrystalline.Site.ModuleSheaf (p := p) (J := Ideal.span {(p : W)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) w₁ n) :=
  GeometricComparison.Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts (Crystalline.ExactRestriction.Coeff (B := W))
    (BoundedCrystalline.Site.topology w₁ n)
local instance targetCoproducts : HasCoproducts.{0}
    (BoundedCrystalline.Site.ModuleSheaf (p := p) (J := Ideal.span {(p : W)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) w₂ n) :=
  GeometricComparison.Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts (Crystalline.ExactRestriction.Coeff (B := W))
    (BoundedCrystalline.Site.topology w₂ n)

def sourceMap : CechSheafResolution.complex p k n X₁ Y₁ f₁ hp₁ ⟶ L :=
  (DiagonalCech.Comparison.totalIso p k n X₁ Y₁ f₁ hp₁).hom ≫
    MorphismRefinement.sourceMap p k n u Q

def targetRefinement : CechSheafResolution.complex p k n X₂ Y₂ f₂ hp₂ ⟶
    GeometricComparison.CechCone.Total.CechConeTotal.total U ((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left).op ⋙ P) :=
  (DiagonalCech.Comparison.totalIso p k n X₂ Y₂ f₂ hp₂).hom ≫
    MorphismRefinement.targetMap p k n u P

def targetMap : ((T).mapHomologicalComplex (.up ℕ)).obj
    (CechSheafResolution.complex p k n X₂ Y₂ f₂ hp₂) ⟶ L :=
  ((T).mapHomologicalComplex (.up ℕ)).map (targetRefinement p k n u f₂ hp₂) ≫
    MorphismCech.map p k n u v f₁ f₂ hp₁ hp₂ sq U

omit [IsSeparated Y₂.hom] in
theorem source_augmentation : CechSheafResolution.augmentation p k n X₁ Y₁ f₁ hp₁ ≫
    sourceMap p k n u f₁ hp₁ = a :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun b => b ≫ MorphismRefinement.sourceMap p k n u Q)
      (CechSheafAugmentationCoordinates.augmentation p k n X₁ Y₁ f₁ hp₁)).trans
        (MorphismRefinement.source_augmentation p k n u Q _
          (ResolutionDiagram.augmentation p k n X₁ Y₁ f₁ hp₁)))

omit [IsSeparated Y₁.hom] in
theorem target_refinement_augmentation : CechSheafResolution.augmentation p k n X₂ Y₂ f₂ hp₂ ≫
    targetRefinement p k n u f₂ hp₂ =
      GeometricComparison.CechCone.Total.CechConeTotal.augmentation U ((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left).op ⋙ P) _
        (MorphismCech.targetCone p k n u f₂ hp₂) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun b => b ≫ MorphismRefinement.targetMap p k n u P)
      (CechSheafAugmentationCoordinates.augmentation p k n X₂ Y₂ f₂ hp₂)).trans
        (MorphismRefinement.target_augmentation p k n u P _
          (ResolutionDiagram.augmentation p k n X₂ Y₂ f₂ hp₂)))

theorem target_augmentation : Single.ComplexTransport.map T e
    (CechSheafResolution.augmentation p k n X₂ Y₂ f₂ hp₂) ≫ targetMap p k n u v f₁ f₂ hp₁ hp₂ sq = a := by
  have h₁ := (Single.ComplexTransportNaturality.comp T e
    (CechSheafResolution.augmentation p k n X₂ Y₂ f₂ hp₂)
    (targetRefinement p k n u f₂ hp₂)).trans
      (congrArg (Single.ComplexTransport.map T e) (target_refinement_augmentation p k n u f₂ hp₂))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun b => b ≫ MorphismCech.map p k n u v f₁ f₂ hp₁ hp₂ sq U) h₁).trans
      (MorphismCech.augmentation p k n u v f₁ f₂ hp₁ hp₂ sq U))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismRefinedResolution
