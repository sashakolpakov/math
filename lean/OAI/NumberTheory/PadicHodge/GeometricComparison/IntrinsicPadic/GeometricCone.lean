import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ConeSectionData
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.RefinementConeComponentCoordinates

/-! # Geometric Cone -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.GeometricCone.IntrinsicPadicGeometricConeTotalMaps

/-! The actual original edge, literal cone edges and refinement
cochain maps with their source and target total complexes fixed. -/
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

def sourceOld : CochainComplex (ModuleCat.{2} R) ℕ :=
  CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy.total.{1, 2} R (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₁)
    (ConeSectionData.IntrinsicPadicGeometricConeSectionData.sourceOldSections p f₁ n I₁)

def sourceNew : CochainComplex (ModuleCat.{2} R) ℕ :=
  CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy.total.{1, 2} R U
    (ConeSectionData.IntrinsicPadicGeometricConeSectionData.sourceNewSections p u f₁ n I₁)

def sourceOriginalEdge : ConeSectionData.IntrinsicPadicGeometricConeSectionData.sourceGlobal p n I₁ ⟶ sourceOld p f₁ n I₁ :=
  TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.edge p X₁ Y₁ f₁ n I₁

def sourceOldEdge : ConeSectionData.IntrinsicPadicGeometricConeSectionData.sourceGlobal p n I₁ ⟶ sourceOld p f₁ n I₁ :=
  CechPresheaf.ConeTotal.CechPresheafConeTotal.map (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₁)
    (ConeSectionData.IntrinsicPadicGeometricConeSectionData.sourceOldSections p f₁ n I₁)
    (ConeSectionData.IntrinsicPadicGeometricConeSectionData.sourceGlobal p n I₁)
    (ConeSectionData.IntrinsicPadicGeometricConeSectionData.sourceOldCone p f₁ n I₁)

def sourceNewEdge : ConeSectionData.IntrinsicPadicGeometricConeSectionData.sourceGlobal p n I₁ ⟶ sourceNew p u f₁ n I₁ :=
  CechPresheaf.ConeTotal.CechPresheafConeTotal.map U
    (ConeSectionData.IntrinsicPadicGeometricConeSectionData.sourceNewSections p u f₁ n I₁)
    (ConeSectionData.IntrinsicPadicGeometricConeSectionData.sourceGlobal p n I₁)
    (ConeSectionData.IntrinsicPadicGeometricConeSectionData.sourceNewCone p u f₁ n I₁)

def sourceRefinement : sourceOld p f₁ n I₁ ⟶ sourceNew p u f₁ n I₁ :=
  GlobalRefinementMaps.IntrinsicPadicGeometricGlobalRefinementMaps.sourceMap p u f₁ n I₁

def targetOld : CochainComplex (ModuleCat.{2} R) ℕ :=
  CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy.total.{1, 2} R (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₂)
    (ConeSectionData.IntrinsicPadicGeometricConeSectionData.targetOldSections p f₂ n I₂)

def targetNew : CochainComplex (ModuleCat.{2} R) ℕ :=
  CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy.total.{1, 2} R U
    (ConeSectionData.IntrinsicPadicGeometricConeSectionData.targetNewSections p u f₂ n I₂)

def targetOriginalEdge : ConeSectionData.IntrinsicPadicGeometricConeSectionData.targetGlobal p n I₂ ⟶ targetOld p f₂ n I₂ :=
  TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.edge p X₂ Y₂ f₂ n I₂

def targetOldEdge : ConeSectionData.IntrinsicPadicGeometricConeSectionData.targetGlobal p n I₂ ⟶ targetOld p f₂ n I₂ :=
  CechPresheaf.ConeTotal.CechPresheafConeTotal.map (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₂)
    (ConeSectionData.IntrinsicPadicGeometricConeSectionData.targetOldSections p f₂ n I₂)
    (ConeSectionData.IntrinsicPadicGeometricConeSectionData.targetGlobal p n I₂)
    (ConeSectionData.IntrinsicPadicGeometricConeSectionData.targetOldCone p f₂ n I₂)

def targetNewEdge : ConeSectionData.IntrinsicPadicGeometricConeSectionData.targetGlobal p n I₂ ⟶ targetNew p u f₂ n I₂ :=
  CechPresheaf.ConeTotal.CechPresheafConeTotal.map U
    (ConeSectionData.IntrinsicPadicGeometricConeSectionData.targetNewSections p u f₂ n I₂)
    (ConeSectionData.IntrinsicPadicGeometricConeSectionData.targetGlobal p n I₂)
    (ConeSectionData.IntrinsicPadicGeometricConeSectionData.targetNewCone p u f₂ n I₂)

def targetRefinement : targetOld p f₂ n I₂ ⟶ targetNew p u f₂ n I₂ :=
  GlobalRefinementMaps.IntrinsicPadicGeometricGlobalRefinementMaps.targetMap p u f₂ n I₂

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.GeometricCone.IntrinsicPadicGeometricConeTotalMaps

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.GeometricCone.IntrinsicPadicGeometricConeOldEdgeCoordinates

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.GeometricCone.IntrinsicPadicGeometricConeTotalMaps

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
theorem source_old_component : (IntrinsicPadicGeometricConeTotalMaps.sourceOriginalEdge p f₁ n I₁).f 1 = (IntrinsicPadicGeometricConeTotalMaps.sourceOldEdge p f₁ n I₁).f 1 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact ConcreteCategory.congr_hom
    (ConeSectionData.IntrinsicPadicGeometricTypedReferenceEdgeComponents.source_edge_component p f₁ n I₁) x

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem target_old_component : (IntrinsicPadicGeometricConeTotalMaps.targetOriginalEdge p f₂ n I₂).f 1 = (IntrinsicPadicGeometricConeTotalMaps.targetOldEdge p f₂ n I₂).f 1 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact ConcreteCategory.congr_hom
    (ConeSectionData.IntrinsicPadicGeometricTypedReferenceEdgeComponents.target_edge_component p f₂ n I₂) x

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.GeometricCone.IntrinsicPadicGeometricConeOldEdgeCoordinates

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.GeometricCone.IntrinsicPadicGeometricConeTypedSquare

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.GeometricCone.IntrinsicPadicGeometricConeTotalMaps

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
theorem source_square : (IntrinsicPadicGeometricConeTotalMaps.sourceOriginalEdge p f₁ n I₁).f 1 ≫ (IntrinsicPadicGeometricConeTotalMaps.sourceRefinement p u f₁ n I₁).f 1 =
    (IntrinsicPadicGeometricConeTotalMaps.sourceNewEdge p u f₁ n I₁).f 1 :=
  Cech.RefinementConeComponentCoordinates.CechRefinementConeComponentCoordinates.component.{1, 2} R (Affine.MapPairs.AffineMapPairs.source u.left) U
    (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₁) (Cover.IntrinsicPadicGeometricCoverRefinements.source p u)
    (ConeSectionData.IntrinsicPadicGeometricConeSectionData.sourceOldSections p f₁ n I₁)
    (ConeSectionData.IntrinsicPadicGeometricConeSectionData.sourceGlobal p n I₁)
    (IntrinsicPadicGeometricConeTotalMaps.sourceOriginalEdge p f₁ n I₁)
    (ConeSectionData.IntrinsicPadicGeometricConeSectionData.sourceOldCone p f₁ n I₁)
    (ConeSectionData.IntrinsicPadicGeometricConeSectionData.sourceNewCone p u f₁ n I₁)
    (IntrinsicPadicGeometricConeOldEdgeCoordinates.source_old_component p f₁ n I₁)
    (fun W => ConeSectionData.IntrinsicPadicGeometricConeSectionData.source_component p u f₁ n I₁ W)

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem target_square : (IntrinsicPadicGeometricConeTotalMaps.targetOriginalEdge p f₂ n I₂).f 1 ≫ (IntrinsicPadicGeometricConeTotalMaps.targetRefinement p u f₂ n I₂).f 1 =
    (IntrinsicPadicGeometricConeTotalMaps.targetNewEdge p u f₂ n I₂).f 1 :=
  Cech.RefinementConeComponentCoordinates.CechRefinementConeComponentCoordinates.component.{1, 2} R (Affine.MapPairs.AffineMapPairs.target u.left) U
    (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₂) (Cover.IntrinsicPadicGeometricCoverRefinements.target p u)
    (ConeSectionData.IntrinsicPadicGeometricConeSectionData.targetOldSections p f₂ n I₂)
    (ConeSectionData.IntrinsicPadicGeometricConeSectionData.targetGlobal p n I₂)
    (IntrinsicPadicGeometricConeTotalMaps.targetOriginalEdge p f₂ n I₂)
    (ConeSectionData.IntrinsicPadicGeometricConeSectionData.targetOldCone p f₂ n I₂)
    (ConeSectionData.IntrinsicPadicGeometricConeSectionData.targetNewCone p u f₂ n I₂)
    (IntrinsicPadicGeometricConeOldEdgeCoordinates.target_old_component p f₂ n I₂)
    (fun W => ConeSectionData.IntrinsicPadicGeometricConeSectionData.target_component p u f₂ n I₂ W)

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.GeometricCone.IntrinsicPadicGeometricConeTypedSquare

end

end OAI
