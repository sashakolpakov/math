import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ResolutionDiagram
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicResolutionDiagram
import OAI.NumberTheory.PadicHodge.GeometricComparison.Module.SheafCoproducts
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalLevelMap

/-! # Cech Diagram -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechDiagram.IntrinsicPadicGeometricCechDiagram

noncomputable section

/-! The actual geometric frame maps induce augmented Cech resolution
maps over each finite family of compatible affine pairs. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))}
  [Smooth X₁.hom] [Smooth X₂.hom] [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of (ZMod p)))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hsquare : f₁ ≫ u.left = v.left ≫ f₂) (n : ℕ)
  {ι : Type} [Finite ι] (U : ι → Affine.MapPairs.AffineMapPairs.Charts u.left)

open OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameData.IntrinsicPadicFrameGeometricData
local notation "W" => WittVector p (ZMod p)
local notation "w₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₁
local notation "w₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₂
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p)
  (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (Over.Hom.left v) (FrameData.IntrinsicPadicFrameGeometricData.global_over_witt p v) n
local notation "P" => Functor.op (OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.target (Over.Hom.left u)) ⋙ OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.diagram p X₂ Y₂ f₂ hp₂ n
local notation "Q" => Functor.op (OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.source (Over.Hom.left u)) ⋙ OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.diagram p X₁ Y₁ f₁ hp₁ n
local notation "a" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ResolutionDiagram.IntrinsicPadicGeometricResolutionDiagram.transformation p u v f₁ f₂ hp₁ hp₂ hsquare n
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Sheaves.structureTransport (Over.Hom.left v) (OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameData.IntrinsicPadicFrameGeometricData.global_over_witt p v) n

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

def sourceCone := Functor.whiskerLeft (Affine.MapPairs.AffineMapPairs.source u.left).op
  (PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.augmentation p X₁ Y₁ f₁ hp₁ n)
def targetCone := Functor.whiskerLeft (Affine.MapPairs.AffineMapPairs.target u.left).op
  (PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.augmentation p X₂ Y₂ f₂ hp₂ n)

def map : ((T).mapHomologicalComplex (.up ℕ)).obj (CechCone.Total.CechConeTotal.total U P) ⟶ CechCone.Total.CechConeTotal.total U Q :=
  CechCone.TotalLevelMap.CechConeTotalLevelMap.map T U P Q a

theorem augmentation : IntegralComparison.Single.ComplexTransport.map T e
    (CechCone.Total.CechConeTotal.augmentation U P _ (targetCone p u f₂ hp₂ n)) ≫ IntrinsicPadicGeometricCechDiagram.map p u v f₁ f₂ hp₁ hp₂ hsquare n U =
      CechCone.Total.CechConeTotal.augmentation U Q _ (sourceCone p u f₁ hp₁ n) :=
  CechCone.TotalLevelMap.CechConeTotalLevelMap.augmentation T U P Q a e
    (targetCone p u f₂ hp₂ n) (sourceCone p u f₁ hp₁ n)
    (fun V => ResolutionDiagram.IntrinsicPadicGeometricResolutionDiagram.augmentation p u v f₁ f₂ hp₁ hp₂ hsquare n V.unop)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechDiagram.IntrinsicPadicGeometricCechDiagram
