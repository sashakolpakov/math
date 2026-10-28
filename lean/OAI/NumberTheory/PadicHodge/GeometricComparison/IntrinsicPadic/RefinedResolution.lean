import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SourceResolution
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechDiagram
import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ComplexTransportNaturality

/-! # Refined Resolution -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.RefinedResolution.IntrinsicPadicGeometricRefinedResolution

noncomputable section

/-! The original chosen source and target Cech resolutions map, with
their actual augmentations, into one common geometric source resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of (ZMod p)))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hsquare : f₁ ≫ u.left = v.left ≫ f₂) (n : ℕ)

open OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameData.IntrinsicPadicFrameGeometricData
local notation "W" => WittVector p (ZMod p)
local notation "w₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₁
local notation "w₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₂
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p)
  (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (Over.Hom.left v) (FrameData.IntrinsicPadicFrameGeometricData.global_over_witt p v) n
local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.diagram p X₂ Y₂ f₂ hp₂ n
local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.diagram p X₁ Y₁ f₁ hp₁ n
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Cover.IntrinsicPadicGeometricCover.pairs p u
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Sheaves.structureTransport (Over.Hom.left v) (OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameData.IntrinsicPadicFrameGeometricData.global_over_witt p v) n
local notation "L" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SourceResolution.IntrinsicPadicGeometricSourceResolution.complex p u Y₁ f₁ hp₁ n
local notation "a" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SourceResolution.IntrinsicPadicGeometricSourceResolution.augmentation p u Y₁ f₁ hp₁ n

local instance sourceSeparated : IsSeparated w₁ := by
  dsimp only [IntegralComparison.Witt.Crystalline.wittStructureMap]
  infer_instance
local instance targetSeparated : IsSeparated w₂ := by
  dsimp only [IntegralComparison.Witt.Crystalline.wittStructureMap]
  infer_instance
local instance sourceCoproducts : HasCoproducts.{0}
    (IntegralComparison.BoundedCrystalline.Site.ModuleSheaf (p := p) (J := Ideal.span {(p : W)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w₁ n) :=
  Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W))
    (IntegralComparison.BoundedCrystalline.Site.topology w₁ n)
local instance targetCoproducts : HasCoproducts.{0}
    (IntegralComparison.BoundedCrystalline.Site.ModuleSheaf (p := p) (J := Ideal.span {(p : W)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w₂ n) :=
  Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W))
    (IntegralComparison.BoundedCrystalline.Site.topology w₂ n)

def sourceMap : CechSheafResolution.IntrinsicPadicCechSheafResolution.complex p X₁ Y₁ f₁ hp₁ n ⟶ L :=
  (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalIso p X₁ Y₁ f₁ hp₁ n).hom ≫
    CoverCech.IntrinsicPadicGeometricCoverCech.sourceMap p u Q

def targetRefinement : CechSheafResolution.IntrinsicPadicCechSheafResolution.complex p X₂ Y₂ f₂ hp₂ n ⟶
    CechCone.Total.CechConeTotal.total U ((Affine.MapPairs.AffineMapPairs.target u.left).op ⋙ P) :=
  (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalIso p X₂ Y₂ f₂ hp₂ n).hom ≫
    CoverCech.IntrinsicPadicGeometricCoverCech.targetMap p u P

def targetMap : ((T).mapHomologicalComplex (.up ℕ)).obj
    (CechSheafResolution.IntrinsicPadicCechSheafResolution.complex p X₂ Y₂ f₂ hp₂ n) ⟶ L :=
  ((T).mapHomologicalComplex (.up ℕ)).map (targetRefinement p u f₂ hp₂ n) ≫
    CechDiagram.IntrinsicPadicGeometricCechDiagram.map p u v f₁ f₂ hp₁ hp₂ hsquare n U

omit [IsSeparated Y₂.hom] in
theorem source_augmentation : CechSheafResolution.IntrinsicPadicCechSheafResolution.augmentation p X₁ Y₁ f₁ hp₁ n ≫
    sourceMap p u f₁ hp₁ n = a :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun b => b ≫ CoverCech.IntrinsicPadicGeometricCoverCech.sourceMap p u Q)
      (CechSheafAugmentationCoordinates.IntrinsicPadicCechSheafAugmentationCoordinates.augmentation p X₁ Y₁ f₁ hp₁ n)).trans
        (CoverCech.IntrinsicPadicGeometricCoverCech.source_augmentation p u Q _
          (PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.augmentation p X₁ Y₁ f₁ hp₁ n)))

omit [IsSeparated Y₁.hom] in
theorem target_refinement_augmentation : CechSheafResolution.IntrinsicPadicCechSheafResolution.augmentation p X₂ Y₂ f₂ hp₂ n ≫
    targetRefinement p u f₂ hp₂ n =
      CechCone.Total.CechConeTotal.augmentation U ((Affine.MapPairs.AffineMapPairs.target u.left).op ⋙ P) _
        (CechDiagram.IntrinsicPadicGeometricCechDiagram.targetCone p u f₂ hp₂ n) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun b => b ≫ CoverCech.IntrinsicPadicGeometricCoverCech.targetMap p u P)
      (CechSheafAugmentationCoordinates.IntrinsicPadicCechSheafAugmentationCoordinates.augmentation p X₂ Y₂ f₂ hp₂ n)).trans
        (CoverCech.IntrinsicPadicGeometricCoverCech.target_augmentation p u P _
          (PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.augmentation p X₂ Y₂ f₂ hp₂ n)))

theorem target_augmentation : IntegralComparison.Single.ComplexTransport.map T e
    (CechSheafResolution.IntrinsicPadicCechSheafResolution.augmentation p X₂ Y₂ f₂ hp₂ n) ≫ targetMap p u v f₁ f₂ hp₁ hp₂ hsquare n = a := by
  have h₁ := (IntegralComparison.Single.ComplexTransportNaturality.comp T e
    (CechSheafResolution.IntrinsicPadicCechSheafResolution.augmentation p X₂ Y₂ f₂ hp₂ n)
    (targetRefinement p u f₂ hp₂ n)).trans
      (congrArg (IntegralComparison.Single.ComplexTransport.map T e) (target_refinement_augmentation p u f₂ hp₂ n))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun b => b ≫ CechDiagram.IntrinsicPadicGeometricCechDiagram.map p u v f₁ f₂ hp₁ hp₂ hsquare n U) h₁).trans
      (CechDiagram.IntrinsicPadicGeometricCechDiagram.augmentation p u v f₁ f₂ hp₁ hp₂ hsquare n U))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.RefinedResolution.IntrinsicPadicGeometricRefinedResolution
