import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ConeObjectCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CommonHomologyMaps
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.HomologyHeterogeneous

/-! # Reference Cone One -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReferenceConeOne.IntrinsicPadicGeometricTypedCommonHomologyCoordinates

/-! Transport the native common edge by proved object equalities
directly on degree-one cohomology. -/
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
theorem source_homology_heq : HEq (CommonHomologyMaps.IntrinsicPadicGeometricConeHomologyMaps.source_edge p u f₁ n I₁)
    (CommonHomologyMaps.IntrinsicPadicGeometricCommonHomologyMaps.source_common p u f₁ n I₁) :=
  CechCone.HomologyHeterogeneous.CechConeHomologyHeterogeneous.homology U
    (ConeSectionData.IntrinsicPadicGeometricConeSectionData.sourceNewSections p u f₁ n I₁)
    (CommonGlobal.IntrinsicPadicGeometricCommonGlobal.sourceSections p u f₁ n I₁)
    (ConeSectionData.IntrinsicPadicGeometricConeSectionData.sourceGlobal p n I₁)
    (GlobalCone.IntrinsicPadicGeometricGlobalCone.sourceGlobal p n I₁)
    (ConeSectionData.IntrinsicPadicGeometricConeSectionData.sourceNewCone p u f₁ n I₁)
    (GlobalCone.IntrinsicPadicGeometricGlobalCone.sourceCone p u f₁ n I₁)
    (ConeObjectCoordinates.IntrinsicPadicGeometricConeObjectCoordinates.source_sections p u f₁ n I₁)
    (ConeObjectCoordinates.IntrinsicPadicGeometricConeObjectCoordinates.source_global p n I₁)
    (ConeObjectCoordinates.IntrinsicPadicGeometricConeObjectCoordinates.source_cone p u f₁ n I₁) 1

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem source_homology : CommonHomologyMaps.IntrinsicPadicGeometricConeHomologyMaps.source_edge p u f₁ n I₁ =
    CommonHomologyMaps.IntrinsicPadicGeometricCommonHomologyMaps.source_common p u f₁ n I₁ :=
  eq_of_heq (source_homology_heq p u f₁ n I₁)

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem target_homology_heq : HEq (CommonHomologyMaps.IntrinsicPadicGeometricConeHomologyMaps.target_edge p u f₂ n I₂)
    (CommonHomologyMaps.IntrinsicPadicGeometricCommonHomologyMaps.target_common p u f₂ n I₂) :=
  CechCone.HomologyHeterogeneous.CechConeHomologyHeterogeneous.homology U
    (ConeSectionData.IntrinsicPadicGeometricConeSectionData.targetNewSections p u f₂ n I₂)
    (CommonGlobal.IntrinsicPadicGeometricCommonGlobal.targetSections p u f₂ n I₂)
    (ConeSectionData.IntrinsicPadicGeometricConeSectionData.targetGlobal p n I₂)
    (GlobalCone.IntrinsicPadicGeometricGlobalCone.targetGlobal p n I₂)
    (ConeSectionData.IntrinsicPadicGeometricConeSectionData.targetNewCone p u f₂ n I₂)
    (GlobalCone.IntrinsicPadicGeometricGlobalCone.targetCone p u f₂ n I₂)
    (ConeObjectCoordinates.IntrinsicPadicGeometricConeObjectCoordinates.target_sections p u f₂ n I₂)
    (ConeObjectCoordinates.IntrinsicPadicGeometricConeObjectCoordinates.target_global p n I₂)
    (ConeObjectCoordinates.IntrinsicPadicGeometricConeObjectCoordinates.target_cone p u f₂ n I₂) 1

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem target_homology : CommonHomologyMaps.IntrinsicPadicGeometricConeHomologyMaps.target_edge p u f₂ n I₂ =
    CommonHomologyMaps.IntrinsicPadicGeometricCommonHomologyMaps.target_common p u f₂ n I₂ :=
  eq_of_heq (target_homology_heq p u f₂ n I₂)

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReferenceConeOne.IntrinsicPadicGeometricTypedCommonHomologyCoordinates

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReferenceConeOne.IntrinsicPadicGeometricReferenceConeHOne

/-! The original inverse-comparison edge is preserved by the exact
refinement used in the checked native integral comparison square. -/
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
theorem source_cone : CommonHomologyMaps.IntrinsicPadicGeometricConeHomologyMaps.source_original p f₁ n I₁ ≫
    CommonHomologyMaps.IntrinsicPadicGeometricConeHomologyMaps.source_refinement p u f₁ n I₁ =
      CommonHomologyMaps.IntrinsicPadicGeometricCommonHomologyMaps.source_common p u f₁ n I₁ :=
  (CommonHomologyMaps.IntrinsicPadicGeometricConeHomologyMaps.source_square p u f₁ n I₁).trans
    (IntrinsicPadicGeometricTypedCommonHomologyCoordinates.source_homology p u f₁ n I₁)

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem target_cone : CommonHomologyMaps.IntrinsicPadicGeometricConeHomologyMaps.target_original p f₂ n I₂ ≫
    CommonHomologyMaps.IntrinsicPadicGeometricConeHomologyMaps.target_refinement p u f₂ n I₂ =
      CommonHomologyMaps.IntrinsicPadicGeometricCommonHomologyMaps.target_common p u f₂ n I₂ :=
  (CommonHomologyMaps.IntrinsicPadicGeometricConeHomologyMaps.target_square p u f₂ n I₂).trans
    (IntrinsicPadicGeometricTypedCommonHomologyCoordinates.target_homology p u f₂ n I₂)

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReferenceConeOne.IntrinsicPadicGeometricReferenceConeHOne

end

end OAI
