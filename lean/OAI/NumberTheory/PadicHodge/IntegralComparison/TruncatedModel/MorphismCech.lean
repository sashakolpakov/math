import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismResolution
import OAI.NumberTheory.PadicHodge.GeometricComparison.Module.SheafCoproducts
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalLevelMap

/-! # Morphism Cech -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCech

noncomputable section

/-! Actual model morphisms induce augmented maps of the full Cech resolution complexes on any finite family of compatible affine pairs. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))} [Smooth X₁.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of k))}
  [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom
    (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom
    (Truncated.Witt.reduction p k n))))
  (sq : f₁ ≫ u.left = v.left ≫ f₂)

variable {ι : Type} [Finite ι] (U : ι → AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left)
local notation "w₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y₁
local notation "w₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y₂
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Over.Hom.left v) (MorphismData.Frames.ambient_over p k v) n
local notation "P" => Functor.op (OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target (Over.Hom.left u)) ⋙ OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionDiagram.diagram p k n X₂ Y₂ f₂ hp₂
local notation "Q" => Functor.op (OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source (Over.Hom.left u)) ⋙ OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionDiagram.diagram p k n X₁ Y₁ f₁ hp₁
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismResolution.transformation p k n u v f₁ f₂ hp₁ hp₂ sq
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Sheaves.structureTransport (Over.Hom.left v) (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismData.Frames.ambient_over p k v) n

local instance sourceSeparated : IsSeparated w₁ := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance
local instance targetSeparated : IsSeparated w₂ := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance
local instance sourceCoproducts : HasCoproducts.{0}
    (BoundedCrystalline.Site.ModuleSheaf (p := p) (J := Ideal.span {(p : WittVector p k)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) w₁ n) :=
  GeometricComparison.Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
    (BoundedCrystalline.Site.topology w₁ n)
local instance targetCoproducts : HasCoproducts.{0}
    (BoundedCrystalline.Site.ModuleSheaf (p := p) (J := Ideal.span {(p : WittVector p k)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) w₂ n) :=
  GeometricComparison.Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
    (BoundedCrystalline.Site.topology w₂ n)

def sourceCone := Functor.whiskerLeft (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left).op
  (ResolutionDiagram.augmentation p k n X₁ Y₁ f₁ hp₁)
def targetCone := Functor.whiskerLeft (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left).op
  (ResolutionDiagram.augmentation p k n X₂ Y₂ f₂ hp₂)

def map : ((R).mapHomologicalComplex (.up ℕ)).obj (GeometricComparison.CechCone.Total.CechConeTotal.total U P) ⟶ GeometricComparison.CechCone.Total.CechConeTotal.total U Q :=
  GeometricComparison.CechCone.TotalLevelMap.CechConeTotalLevelMap.map R U P Q a

theorem augmentation : Single.ComplexTransport.map R e
    (GeometricComparison.CechCone.Total.CechConeTotal.augmentation U P _ (targetCone p k n u f₂ hp₂)) ≫ MorphismCech.map p k n u v f₁ f₂ hp₁ hp₂ sq U =
      GeometricComparison.CechCone.Total.CechConeTotal.augmentation U Q _ (sourceCone p k n u f₁ hp₁) :=
  GeometricComparison.CechCone.TotalLevelMap.CechConeTotalLevelMap.augmentation R U P Q a e
    (targetCone p k n u f₂ hp₂) (sourceCone p k n u f₁ hp₁)
    (fun V => MorphismResolution.augmentation p k n u v f₁ f₂ hp₁ hp₂ sq V.unop)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCech
