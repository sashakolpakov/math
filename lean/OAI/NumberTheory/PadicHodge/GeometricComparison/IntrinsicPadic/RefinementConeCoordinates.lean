import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.GlobalConeCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CommonGlobal
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.GlobalRefinementMaps
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeRefinementComponents
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeComponentCongr

/-! # Refinement Cone Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.RefinementConeCoordinates.IntrinsicPadicGeometricRefinementConeCoordinates

noncomputable section

/-! The actual native projected refinement preserves the global edge
in degree one, directly in the original section presentation. -/

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
local notation "w₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₁
local notation "w₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₂

def sourceMap := GlobalRefinementMaps.IntrinsicPadicGeometricGlobalRefinementMaps.sourceMap p u f₁ n I₁
def sourceOldEdge := CechPresheaf.ConeTotal.CechPresheafConeTotal.map (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₁)
  (GlobalConeCoordinates.IntrinsicPadicGlobalConeCoordinates.sections p X₁ Y₁ f₁ n I₁)
  (GlobalCone.IntrinsicPadicGeometricGlobalCone.sourceGlobal p n I₁)
  (GlobalConeCoordinates.IntrinsicPadicGlobalConeCoordinates.cone p X₁ Y₁ f₁ n I₁)

def sourcePulledCone : (CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := Affine.MapPairs.AffineMapPairs.Charts u.left)).obj
    (GlobalCone.IntrinsicPadicGeometricGlobalCone.sourceGlobal p n I₁) ⟶
      CommonGlobal.IntrinsicPadicGeometricCommonGlobal.sourceSections p u f₁ n I₁ :=
  CechPresheaf.ConeRefinement.CechPresheafConeRefinement.cone (Affine.MapPairs.AffineMapPairs.source u.left)
    (GlobalConeCoordinates.IntrinsicPadicGlobalConeCoordinates.sections p X₁ Y₁ f₁ n I₁)
    (GlobalCone.IntrinsicPadicGeometricGlobalCone.sourceGlobal p n I₁)
    (GlobalConeCoordinates.IntrinsicPadicGlobalConeCoordinates.cone p X₁ Y₁ f₁ n I₁)

def sourcePulledEdge := CechPresheaf.ConeTotal.CechPresheafConeTotal.map U
  (CommonGlobal.IntrinsicPadicGeometricCommonGlobal.sourceSections p u f₁ n I₁)
  (GlobalCone.IntrinsicPadicGeometricGlobalCone.sourceGlobal p n I₁) (sourcePulledCone p u f₁ n I₁)

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem source_old_component (q : ℕ) : (GlobalConeCoordinates.IntrinsicPadicGlobalConeCoordinates.edge p X₁ Y₁ f₁ n I₁).f q =
    (sourceOldEdge p f₁ n I₁).f q := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] in
theorem source_cone_component (q : ℕ) (W : (Affine.MapPairs.AffineMapPairs.Charts u.left)ᵒᵖ) :
    ((sourcePulledCone p u f₁ n I₁).f q).app W =
      ((GlobalCone.IntrinsicPadicGeometricGlobalCone.sourceCone p u f₁ n I₁).f q).app W := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

def targetMap := GlobalRefinementMaps.IntrinsicPadicGeometricGlobalRefinementMaps.targetMap p u f₂ n I₂
def targetOldEdge := CechPresheaf.ConeTotal.CechPresheafConeTotal.map (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₂)
  (GlobalConeCoordinates.IntrinsicPadicGlobalConeCoordinates.sections p X₂ Y₂ f₂ n I₂)
  (GlobalCone.IntrinsicPadicGeometricGlobalCone.targetGlobal p n I₂)
  (GlobalConeCoordinates.IntrinsicPadicGlobalConeCoordinates.cone p X₂ Y₂ f₂ n I₂)

def targetPulledCone : (CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := Affine.MapPairs.AffineMapPairs.Charts u.left)).obj
    (GlobalCone.IntrinsicPadicGeometricGlobalCone.targetGlobal p n I₂) ⟶
      CommonGlobal.IntrinsicPadicGeometricCommonGlobal.targetSections p u f₂ n I₂ :=
  CechPresheaf.ConeRefinement.CechPresheafConeRefinement.cone (Affine.MapPairs.AffineMapPairs.target u.left)
    (GlobalConeCoordinates.IntrinsicPadicGlobalConeCoordinates.sections p X₂ Y₂ f₂ n I₂)
    (GlobalCone.IntrinsicPadicGeometricGlobalCone.targetGlobal p n I₂)
    (GlobalConeCoordinates.IntrinsicPadicGlobalConeCoordinates.cone p X₂ Y₂ f₂ n I₂)

def targetPulledEdge := CechPresheaf.ConeTotal.CechPresheafConeTotal.map U
  (CommonGlobal.IntrinsicPadicGeometricCommonGlobal.targetSections p u f₂ n I₂)
  (GlobalCone.IntrinsicPadicGeometricGlobalCone.targetGlobal p n I₂) (targetPulledCone p u f₂ n I₂)

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem target_old_component (q : ℕ) : (GlobalConeCoordinates.IntrinsicPadicGlobalConeCoordinates.edge p X₂ Y₂ f₂ n I₂).f q =
    (targetOldEdge p f₂ n I₂).f q := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] in
theorem target_cone_component (q : ℕ) (W : (Affine.MapPairs.AffineMapPairs.Charts u.left)ᵒᵖ) :
    ((targetPulledCone p u f₂ n I₂).f q).app W =
      ((GlobalCone.IntrinsicPadicGeometricGlobalCone.targetCone p u f₂ n I₂).f q).app W := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.RefinementConeCoordinates.IntrinsicPadicGeometricRefinementConeCoordinates
