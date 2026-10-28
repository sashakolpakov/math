import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.RefinedResolution
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactInjective
import OAI.NumberTheory.PadicHodge.GeometricComparison.AugmentedNaturality

/-! # Injective Homotopy -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveHomotopy.IntrinsicPadicGeometricInjectiveHomotopy

noncomputable section

/-! The original chosen Cech-to-injective comparisons agree, up to
actual cochain homotopies, through the common geometric source resolution. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of (ZMod p)))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hsquare : f₁ ≫ u.left = v.left ≫ f₂) (n : ℕ)
  (I₁ : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₁) n))
  (I₂ : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₂) n))

open OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameData.IntrinsicPadicFrameGeometricData
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (Over.Hom.left v) (FrameData.IntrinsicPadicFrameGeometricData.global_over_witt p v) n
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Sheaves.structureTransport (Over.Hom.left v) (OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameData.IntrinsicPadicFrameGeometricData.global_over_witt p v) n
local notation "L" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SourceResolution.IntrinsicPadicGeometricSourceResolution.complex p u Y₁ f₁ hp₁ n
local notation "a" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SourceResolution.IntrinsicPadicGeometricSourceResolution.augmentation p u Y₁ f₁ hp₁ n
local notation "h" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SourceResolution.IntrinsicPadicGeometricSourceResolution.augmentation_quasiIso p u Y₁ f₁ hp₁ n

def comparison : L ⟶ I₁.cocomplex := AugmentedInjective.AugmentedInjectiveComparison.map L a h I₁

omit [IsSeparated Y₂.hom] in
theorem augmentation : a ≫ comparison p u f₁ hp₁ n I₁ = I₁.ι :=
  AugmentedInjective.AugmentedInjectiveComparison.augmentation L a h I₁

def sourceHomotopy : Homotopy (CechInjective.IntrinsicPadicCechInjectiveComparison.map p X₁ Y₁ f₁ hp₁ n I₁)
    (RefinedResolution.IntrinsicPadicGeometricRefinedResolution.sourceMap p u f₁ hp₁ n ≫ comparison p u f₁ hp₁ n I₁) :=
  CechInjective.IntrinsicPadicCechInjectiveComparison.homotopy p X₁ Y₁ f₁ hp₁ n I₁ _
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ comparison p u f₁ hp₁ n I₁)
        (RefinedResolution.IntrinsicPadicGeometricRefinedResolution.source_augmentation p u f₁ hp₁ n)).trans
          (augmentation p u f₁ hp₁ n I₁)))

def targetHomotopy : Homotopy
    (((T).mapHomologicalComplex (.up ℕ)).map (CechInjective.IntrinsicPadicCechInjectiveComparison.map p X₂ Y₂ f₂ hp₂ n I₂) ≫
      ExactInjective.ExactInjectivePullback.map T e I₂ I₁)
    (RefinedResolution.IntrinsicPadicGeometricRefinedResolution.targetMap p u v f₁ f₂ hp₁ hp₂ hsquare n ≫ comparison p u f₁ hp₁ n I₁) :=
  AugmentedNaturality.AugmentedComparisonNaturality.homotopy T e
    (CechSheafResolution.IntrinsicPadicCechSheafResolution.complex p X₂ Y₂ f₂ hp₂ n)
    (CechSheafResolution.IntrinsicPadicCechSheafResolution.augmentation p X₂ Y₂ f₂ hp₂ n)
    (CechSheafResolution.IntrinsicPadicCechSheafResolution.augmentation_quasiIso p X₂ Y₂ f₂ hp₂ n)
    L a h I₂ I₁
    (RefinedResolution.IntrinsicPadicGeometricRefinedResolution.targetMap p u v f₁ f₂ hp₁ hp₂ hsquare n)
    (ExactInjective.ExactInjectivePullback.map T e I₂ I₁)
    (RefinedResolution.IntrinsicPadicGeometricRefinedResolution.target_augmentation p u v f₁ f₂ hp₁ hp₂ hsquare n)
    (ExactInjective.ExactInjectivePullback.augmentation_map T e I₂ I₁)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveHomotopy.IntrinsicPadicGeometricInjectiveHomotopy
