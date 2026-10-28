import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveHomotopy
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.PullbackHomotopy

/-! # Section Homotopy -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionHomotopy.IntrinsicPadicGeometricSectionHomotopy

noncomputable section

/-! The common-resolution homotopies induce actual homotopies of the
original section complexes under geometric inverse-image restriction. -/

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
local notation "S" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionMap.IntrinsicPadicGeometricSectionMap.targetSections p u f₂ n
local notation "S'" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionMap.IntrinsicPadicGeometricSectionMap.sourceSections p u f₁ n
local notation "b" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionMap.IntrinsicPadicGeometricSectionMap.transformation p u v f₁ f₂ hsquare n
local notation "L" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SourceResolution.IntrinsicPadicGeometricSourceResolution.complex p u Y₁ f₁ hp₁ n
local notation "c" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveHomotopy.IntrinsicPadicGeometricInjectiveHomotopy.comparison p u f₁ hp₁ n I₁

def injectiveMap : ((S).mapHomologicalComplex (.up ℕ)).obj I₂.cocomplex ⟶
    ((S').mapHomologicalComplex (.up ℕ)).obj I₁.cocomplex :=
  Section.CochainPullback.SectionCochainPullback.map T S S' b (ExactInjective.ExactInjectivePullback.map T e I₂ I₁)

def sourceMap : ((S').mapHomologicalComplex (.up ℕ)).obj (CechSheafResolution.IntrinsicPadicCechSheafResolution.complex p X₁ Y₁ f₁ hp₁ n) ⟶
    ((S').mapHomologicalComplex (.up ℕ)).obj L :=
  ((S').mapHomologicalComplex (.up ℕ)).map (RefinedResolution.IntrinsicPadicGeometricRefinedResolution.sourceMap p u f₁ hp₁ n)

def targetMap : ((S).mapHomologicalComplex (.up ℕ)).obj (CechSheafResolution.IntrinsicPadicCechSheafResolution.complex p X₂ Y₂ f₂ hp₂ n) ⟶
    ((S').mapHomologicalComplex (.up ℕ)).obj L :=
  Section.CochainPullback.SectionCochainPullback.map T S S' b (RefinedResolution.IntrinsicPadicGeometricRefinedResolution.targetMap p u v f₁ f₂ hp₁ hp₂ hsquare n)

def source : Homotopy
    (((S').mapHomologicalComplex (.up ℕ)).map (CechInjective.IntrinsicPadicCechInjectiveComparison.map p X₁ Y₁ f₁ hp₁ n I₁))
    (sourceMap p u f₁ hp₁ n ≫ ((S').mapHomologicalComplex (.up ℕ)).map c) :=
  ((S').mapHomotopy (InjectiveHomotopy.IntrinsicPadicGeometricInjectiveHomotopy.sourceHomotopy p u f₁ hp₁ n I₁)).trans
    (Homotopy.ofEq (((S').mapHomologicalComplex (.up ℕ)).map_comp
      (RefinedResolution.IntrinsicPadicGeometricRefinedResolution.sourceMap p u f₁ hp₁ n) c))

def target : Homotopy
    (((S).mapHomologicalComplex (.up ℕ)).map (CechInjective.IntrinsicPadicCechInjectiveComparison.map p X₂ Y₂ f₂ hp₂ n I₂) ≫
      injectiveMap p u v f₁ f₂ hsquare n I₁ I₂)
    (targetMap p u v f₁ f₂ hp₁ hp₂ hsquare n ≫ ((S').mapHomologicalComplex (.up ℕ)).map c) :=
  Section.PullbackHomotopy.SectionPullbackHomotopy.homotopy T S S' b
    (CechInjective.IntrinsicPadicCechInjectiveComparison.map p X₂ Y₂ f₂ hp₂ n I₂) c
    (RefinedResolution.IntrinsicPadicGeometricRefinedResolution.targetMap p u v f₁ f₂ hp₁ hp₂ hsquare n)
    (ExactInjective.ExactInjectivePullback.map T e I₂ I₁)
    (InjectiveHomotopy.IntrinsicPadicGeometricInjectiveHomotopy.targetHomotopy p u v f₁ f₂ hp₁ hp₂ hsquare n I₁ I₂)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionHomotopy.IntrinsicPadicGeometricSectionHomotopy
