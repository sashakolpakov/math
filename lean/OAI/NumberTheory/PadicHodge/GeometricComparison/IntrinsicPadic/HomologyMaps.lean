import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.GeometricCone
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Refinement

/-! # Homology Maps -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.HomologyMaps.IntrinsicPadicGeometricRawHomologyMaps

noncomputable section

/-! The original common global comparison and geometric map with
the raw refinement cohomology objects explicitly fixed. -/
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

def sourceRawRefinement : (GeometricCone.IntrinsicPadicGeometricConeTotalMaps.sourceOld p f₁ n I₁).homology 1 ⟶ (GeometricCone.IntrinsicPadicGeometricConeTotalMaps.sourceNew p u f₁ n I₁).homology 1 :=
  Refinement.IntrinsicPadicGeometricComparisonRefinement.sourceInjectiveHOne p u f₁ n I₁

def targetRawRefinement : (GeometricCone.IntrinsicPadicGeometricConeTotalMaps.targetOld p f₂ n I₂).homology 1 ⟶ (GeometricCone.IntrinsicPadicGeometricConeTotalMaps.targetNew p u f₂ n I₂).homology 1 :=
  Refinement.IntrinsicPadicGeometricComparisonRefinement.targetInjectiveHOne p u f₂ n I₂

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.HomologyMaps.IntrinsicPadicGeometricRawHomologyMaps
