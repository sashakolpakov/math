import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.GeometricCone
import OAI.NumberTheory.PadicHodge.GeometricComparison.HomologicalComponent

/-! # Common Homology Maps -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CommonHomologyMaps.IntrinsicPadicGeometricConeHomologyMaps

/-! Cohomology maps with the original typed complexes fixed before
composing the native refinement square. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

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

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Cover.IntrinsicPadicGeometricCover.pairs p u

local instance limits : HasLimitsOfSize.{0, 0} (ModuleCat.{2} R) := ModuleCat.hasLimitsOfSize.{0, 0, 2, 1}
local instance colimits : HasColimitsOfSize.{0, 0} (ModuleCat.{2} R) := ModuleCat.hasColimitsOfSize.{2, 1, 0, 0} R

open OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.GeometricCone.IntrinsicPadicGeometricConeTotalMaps

def source_original : (ConeSectionData.IntrinsicPadicGeometricConeSectionData.sourceGlobal p n I₁).homology 1 ⟶ (GeometricCone.IntrinsicPadicGeometricConeTotalMaps.sourceOld p f₁ n I₁).homology 1 :=
  HomologicalComplex.homologyMap (GeometricCone.IntrinsicPadicGeometricConeTotalMaps.sourceOriginalEdge p f₁ n I₁) 1

def source_refinement : (GeometricCone.IntrinsicPadicGeometricConeTotalMaps.sourceOld p f₁ n I₁).homology 1 ⟶ (GeometricCone.IntrinsicPadicGeometricConeTotalMaps.sourceNew p u f₁ n I₁).homology 1 :=
  HomologicalComplex.homologyMap (GeometricCone.IntrinsicPadicGeometricConeTotalMaps.sourceRefinement p u f₁ n I₁) 1

def source_edge : (ConeSectionData.IntrinsicPadicGeometricConeSectionData.sourceGlobal p n I₁).homology 1 ⟶ (GeometricCone.IntrinsicPadicGeometricConeTotalMaps.sourceNew p u f₁ n I₁).homology 1 :=
  HomologicalComplex.homologyMap (GeometricCone.IntrinsicPadicGeometricConeTotalMaps.sourceNewEdge p u f₁ n I₁) 1

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem source_square : source_original p f₁ n I₁ ≫ source_refinement p u f₁ n I₁ =
    source_edge p u f₁ n I₁ :=
  HomologicalComponent.HomologicalComponentHeterogeneous.composite
    (GeometricCone.IntrinsicPadicGeometricConeTotalMaps.sourceOriginalEdge p f₁ n I₁) (GeometricCone.IntrinsicPadicGeometricConeTotalMaps.sourceRefinement p u f₁ n I₁)
    (GeometricCone.IntrinsicPadicGeometricConeTotalMaps.sourceNewEdge p u f₁ n I₁) 1
    (GeometricCone.IntrinsicPadicGeometricConeTypedSquare.source_square p u f₁ n I₁)

def target_original : (ConeSectionData.IntrinsicPadicGeometricConeSectionData.targetGlobal p n I₂).homology 1 ⟶ (GeometricCone.IntrinsicPadicGeometricConeTotalMaps.targetOld p f₂ n I₂).homology 1 :=
  HomologicalComplex.homologyMap (GeometricCone.IntrinsicPadicGeometricConeTotalMaps.targetOriginalEdge p f₂ n I₂) 1

def target_refinement : (GeometricCone.IntrinsicPadicGeometricConeTotalMaps.targetOld p f₂ n I₂).homology 1 ⟶ (GeometricCone.IntrinsicPadicGeometricConeTotalMaps.targetNew p u f₂ n I₂).homology 1 :=
  HomologicalComplex.homologyMap (GeometricCone.IntrinsicPadicGeometricConeTotalMaps.targetRefinement p u f₂ n I₂) 1

def target_edge : (ConeSectionData.IntrinsicPadicGeometricConeSectionData.targetGlobal p n I₂).homology 1 ⟶ (GeometricCone.IntrinsicPadicGeometricConeTotalMaps.targetNew p u f₂ n I₂).homology 1 :=
  HomologicalComplex.homologyMap (GeometricCone.IntrinsicPadicGeometricConeTotalMaps.targetNewEdge p u f₂ n I₂) 1

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem target_square : target_original p f₂ n I₂ ≫ target_refinement p u f₂ n I₂ =
    target_edge p u f₂ n I₂ :=
  HomologicalComponent.HomologicalComponentHeterogeneous.composite
    (GeometricCone.IntrinsicPadicGeometricConeTotalMaps.targetOriginalEdge p f₂ n I₂) (GeometricCone.IntrinsicPadicGeometricConeTotalMaps.targetRefinement p u f₂ n I₂)
    (GeometricCone.IntrinsicPadicGeometricConeTotalMaps.targetNewEdge p u f₂ n I₂) 1
    (GeometricCone.IntrinsicPadicGeometricConeTypedSquare.target_square p u f₂ n I₂)

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CommonHomologyMaps.IntrinsicPadicGeometricConeHomologyMaps

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CommonHomologyMaps.IntrinsicPadicGeometricCommonHomologyMaps

/-! Cohomology maps with the original typed complexes fixed before
composing the native refinement square. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

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

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Cover.IntrinsicPadicGeometricCover.pairs p u

local instance limits : HasLimitsOfSize.{0, 0} (ModuleCat.{2} R) := ModuleCat.hasLimitsOfSize.{0, 0, 2, 1}
local instance colimits : HasColimitsOfSize.{0, 0} (ModuleCat.{2} R) := ModuleCat.hasColimitsOfSize.{2, 1, 0, 0} R

open OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.GeometricCone.IntrinsicPadicGeometricConeTotalMaps

def source_common : (ConeSectionData.IntrinsicPadicGeometricConeSectionData.sourceGlobal p n I₁).homology 1 ⟶
    (GeometricCone.IntrinsicPadicGeometricConeTotalMaps.sourceNew p u f₁ n I₁).homology 1 :=
  HomologicalComplex.homologyMap (CommonGlobal.IntrinsicPadicGeometricCommonGlobal.sourceEdge p u f₁ n I₁) 1

def target_common : (ConeSectionData.IntrinsicPadicGeometricConeSectionData.targetGlobal p n I₂).homology 1 ⟶
    (GeometricCone.IntrinsicPadicGeometricConeTotalMaps.targetNew p u f₂ n I₂).homology 1 :=
  HomologicalComplex.homologyMap (CommonGlobal.IntrinsicPadicGeometricCommonGlobal.targetEdge p u f₂ n I₂) 1

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CommonHomologyMaps.IntrinsicPadicGeometricCommonHomologyMaps

end

end OAI
