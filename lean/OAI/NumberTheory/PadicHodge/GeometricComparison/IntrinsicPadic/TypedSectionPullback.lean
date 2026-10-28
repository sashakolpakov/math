import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ConeSectionData
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralInjectiveHomotopy

/-! # Typed Section Pullback -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.TypedSectionPullback.IntrinsicPadicGeometricTypedSectionPullback

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

local notation "Pairs" => OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.Charts (Over.Hom.left u)

def sourceIntegral : CochainComplex (Pairsᵒᵖ ⥤ ModuleCat.{2} R) ℕ :=
  AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ)
    ((Affine.MapPairs.AffineMapPairs.source u.left).op ⋙ IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.source p X₁ n)

def targetIntegral : CochainComplex (Pairsᵒᵖ ⥤ ModuleCat.{2} R) ℕ :=
  AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ)
    ((Affine.MapPairs.AffineMapPairs.target u.left).op ⋙ IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.source p X₂ n)

def sourceComparison : sourceIntegral p u n ⟶
    ConeSectionData.IntrinsicPadicGeometricConeSectionData.sourceNewSections p u f₁ n I₁ :=
  IntegralInjectiveHomotopy.IntrinsicPadicGeometricIntegralInjectiveHomotopy.sourceComparison p u f₁ hp₁ n I₁

def targetComparison : targetIntegral p u n ⟶
    ConeSectionData.IntrinsicPadicGeometricConeSectionData.targetNewSections p u f₂ n I₂ :=
  IntegralInjectiveHomotopy.IntrinsicPadicGeometricIntegralInjectiveHomotopy.targetComparison p u f₂ hp₂ n I₂

def integralMap : targetIntegral p u n ⟶ sourceIntegral p u n :=
  IntegralInjectiveHomotopy.IntrinsicPadicGeometricIntegralInjectiveHomotopy.geometricMap p u n

def injectiveMap : ConeSectionData.IntrinsicPadicGeometricConeSectionData.targetNewSections p u f₂ n I₂ ⟶
    ConeSectionData.IntrinsicPadicGeometricConeSectionData.sourceNewSections p u f₁ n I₁ :=
  SectionHomotopy.IntrinsicPadicGeometricSectionHomotopy.injectiveMap p u v f₁ f₂ hsquare n I₁ I₂

def globalMap : ConeSectionData.IntrinsicPadicGeometricConeSectionData.targetGlobal p n I₂ ⟶
    ConeSectionData.IntrinsicPadicGeometricConeSectionData.sourceGlobal p n I₁ :=
  GlobalCone.IntrinsicPadicGeometricGlobalCone.globalMap p v n I₁ I₂

def homotopy : Homotopy
    (targetComparison p u f₂ hp₂ n I₂ ≫ injectiveMap p u v f₁ f₂ hsquare n I₁ I₂)
    (integralMap p u n ≫ sourceComparison p u f₁ hp₁ n I₁) :=
  IntegralInjectiveHomotopy.IntrinsicPadicGeometricIntegralInjectiveHomotopy.homotopy p u v f₁ f₂ hp₁ hp₂ hsquare n I₁ I₂

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] in
theorem cone_naturality : ConeSectionData.IntrinsicPadicGeometricConeSectionData.targetNewCone p u f₂ n I₂ ≫
    injectiveMap p u v f₁ f₂ hsquare n I₁ I₂ =
      (CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := Pairs)).map (globalMap p v n I₁ I₂) ≫
        ConeSectionData.IntrinsicPadicGeometricConeSectionData.sourceNewCone p u f₁ n I₁ :=
  GlobalCone.IntrinsicPadicGeometricGlobalCone.naturality p u v f₁ f₂ hsquare n I₁ I₂

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.TypedSectionPullback.IntrinsicPadicGeometricTypedSectionPullback
