import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CommonHomologyMaps
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.HomologyMaps

/-! # Refinement One Aliases -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.RefinementOneAliases.IntrinsicPadicGeometricRefinementHOneAliases

noncomputable section

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

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem source : CommonHomologyMaps.IntrinsicPadicGeometricConeHomologyMaps.source_refinement p u f₁ n I₁ =
    HomologyMaps.IntrinsicPadicGeometricRawHomologyMaps.sourceRawRefinement p u f₁ n I₁ := rfl

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem target : CommonHomologyMaps.IntrinsicPadicGeometricConeHomologyMaps.target_refinement p u f₂ n I₂ =
    HomologyMaps.IntrinsicPadicGeometricRawHomologyMaps.targetRawRefinement p u f₂ n I₂ := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.RefinementOneAliases.IntrinsicPadicGeometricRefinementHOneAliases
