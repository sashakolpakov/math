import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismInjectiveHomotopy
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSectionMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.PullbackHomotopy

/-! # Morphism Section Homotopy -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSectionHomotopy

noncomputable section

/-! The common-resolution homotopies induce actual homotopies of the
original section complexes under geometric inverse-image restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

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

open OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismData.Frames
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Over.Hom.left v) (MorphismData.Frames.ambient_over p k v) n
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Sheaves.structureTransport (Over.Hom.left v) (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismData.Frames.ambient_over p k v) n
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSectionMap.targetSections p k n u f₂
local notation "S'" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSectionMap.sourceSections p k n u f₁
local notation "b" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSectionMap.transformation p k n u v f₁ f₂ sq
local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSourceResolution.complex p k n u Y₁ f₁ hp₁
local notation "c" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismInjectiveHomotopy.comparison p k n u f₁ hp₁ I₁

def injectiveMap : ((S).mapHomologicalComplex (.up ℕ)).obj I₂.cocomplex ⟶
    ((S').mapHomologicalComplex (.up ℕ)).obj I₁.cocomplex :=
  GeometricComparison.Section.CochainPullback.SectionCochainPullback.map T S S' b (GeometricComparison.ExactInjective.ExactInjectivePullback.map T e I₂ I₁)

def sourceMap : ((S').mapHomologicalComplex (.up ℕ)).obj (CechSheafResolution.complex p k n X₁ Y₁ f₁ hp₁) ⟶
    ((S').mapHomologicalComplex (.up ℕ)).obj L :=
  ((S').mapHomologicalComplex (.up ℕ)).map (MorphismRefinedResolution.sourceMap p k n u f₁ hp₁)

def targetMap : ((S).mapHomologicalComplex (.up ℕ)).obj (CechSheafResolution.complex p k n X₂ Y₂ f₂ hp₂) ⟶
    ((S').mapHomologicalComplex (.up ℕ)).obj L :=
  GeometricComparison.Section.CochainPullback.SectionCochainPullback.map T S S' b (MorphismRefinedResolution.targetMap p k n u v f₁ f₂ hp₁ hp₂ sq)

def source : Homotopy
    (((S').mapHomologicalComplex (.up ℕ)).map (CechInjective.Comparison.map p k n X₁ Y₁ f₁ hp₁ I₁))
    (sourceMap p k n u f₁ hp₁ ≫ ((S').mapHomologicalComplex (.up ℕ)).map c) :=
  ((S').mapHomotopy (MorphismInjectiveHomotopy.sourceHomotopy p k n u f₁ hp₁ I₁)).trans
    (Homotopy.ofEq (((S').mapHomologicalComplex (.up ℕ)).map_comp
      (MorphismRefinedResolution.sourceMap p k n u f₁ hp₁) c))

def target : Homotopy
    (((S).mapHomologicalComplex (.up ℕ)).map (CechInjective.Comparison.map p k n X₂ Y₂ f₂ hp₂ I₂) ≫
      injectiveMap p k n u v f₁ f₂ sq I₁ I₂)
    (targetMap p k n u v f₁ f₂ hp₁ hp₂ sq ≫ ((S').mapHomologicalComplex (.up ℕ)).map c) :=
  GeometricComparison.Section.PullbackHomotopy.SectionPullbackHomotopy.homotopy T S S' b
    (CechInjective.Comparison.map p k n X₂ Y₂ f₂ hp₂ I₂) c
    (MorphismRefinedResolution.targetMap p k n u v f₁ f₂ hp₁ hp₂ sq)
    (GeometricComparison.ExactInjective.ExactInjectivePullback.map T e I₂ I₁)
    (MorphismInjectiveHomotopy.targetHomotopy p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSectionHomotopy
