import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ConeSectionData
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.FunctorObjectReassociation

/-! # Cone Object Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ConeObjectCoordinates.IntrinsicPadicGeometricConeObjectCoordinates

noncomputable section

/-! Proved object equalities relate the original and common section
complexes before transporting their Cech edges. -/
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

local notation "w₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₁
local notation "S₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex.functor
  (p := p) (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w₁ n

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] in
theorem source_sections : ConeSectionData.IntrinsicPadicGeometricConeSectionData.sourceNewSections p u f₁ n I₁ =
    CommonGlobal.IntrinsicPadicGeometricCommonGlobal.sourceSections p u f₁ n I₁ :=
  Section.FunctorObjectReassociation.SectionFunctorObjectReassociation.equality S₁ I₁.cocomplex (Affine.MapPairs.AffineMapPairs.source u.left)
    (SectionBifunctor.IntrinsicPadicSectionBifunctor.specialOpens p X₁ Y₁ f₁)

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem source_global : ConeSectionData.IntrinsicPadicGeometricConeSectionData.sourceGlobal p n I₁ =
    GlobalCone.IntrinsicPadicGeometricGlobalCone.sourceGlobal p n I₁ := rfl

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] in
theorem source_cone : HEq (ConeSectionData.IntrinsicPadicGeometricConeSectionData.sourceNewCone p u f₁ n I₁)
    (GlobalCone.IntrinsicPadicGeometricGlobalCone.sourceCone p u f₁ n I₁) := HEq.rfl

local notation "w₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₂
local notation "S₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex.functor
  (p := p) (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w₂ n

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] in
theorem target_sections : ConeSectionData.IntrinsicPadicGeometricConeSectionData.targetNewSections p u f₂ n I₂ =
    CommonGlobal.IntrinsicPadicGeometricCommonGlobal.targetSections p u f₂ n I₂ :=
  Section.FunctorObjectReassociation.SectionFunctorObjectReassociation.equality S₂ I₂.cocomplex (Affine.MapPairs.AffineMapPairs.target u.left)
    (SectionBifunctor.IntrinsicPadicSectionBifunctor.specialOpens p X₂ Y₂ f₂)

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem target_global : ConeSectionData.IntrinsicPadicGeometricConeSectionData.targetGlobal p n I₂ =
    GlobalCone.IntrinsicPadicGeometricGlobalCone.targetGlobal p n I₂ := rfl

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] in
theorem target_cone : HEq (ConeSectionData.IntrinsicPadicGeometricConeSectionData.targetNewCone p u f₂ n I₂)
    (GlobalCone.IntrinsicPadicGeometricGlobalCone.targetCone p u f₂ n I₂) := HEq.rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ConeObjectCoordinates.IntrinsicPadicGeometricConeObjectCoordinates
