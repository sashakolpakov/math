import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.GlobalConeCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Cover
import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairProducts
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinedReindex

/-! # Global Refinement Maps -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.GlobalRefinementMaps.IntrinsicPadicGeometricGlobalRefinementMaps

noncomputable section

/-! The original chosen-cover injective section complexes map to
actual projected refinements on the common affine-pair cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of (ZMod p)))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hsquare : f₁ ≫ u.left = v.left ≫ f₂) (n : ℕ)
  (I₁ : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₁) n))
  (I₂ : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₂) n))

local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Cover.IntrinsicPadicGeometricCover.pairs p u

def sourceMap := CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map (Affine.MapPairs.AffineMapPairs.source u.left) U
  (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₁) (Cover.IntrinsicPadicGeometricCoverRefinements.source p u)
  (GlobalConeCoordinates.IntrinsicPadicGlobalConeCoordinates.sections p X₁ Y₁ f₁ n I₁)

def targetMap := CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map (Affine.MapPairs.AffineMapPairs.target u.left) U
  (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₂) (Cover.IntrinsicPadicGeometricCoverRefinements.target p u)
  (GlobalConeCoordinates.IntrinsicPadicGlobalConeCoordinates.sections p X₂ Y₂ f₂ n I₂)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.GlobalRefinementMaps.IntrinsicPadicGeometricGlobalRefinementMaps
