import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.TypedSectionPullback
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CommonHomologyMaps
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.OneHomotopySquare
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.CohomologyNaturality

/-! # Typed Cech Pullback -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.TypedCechPullback.IntrinsicPadicGeometricTypedCechPullback

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

def sourceIntegral : CochainComplex (ModuleCat.{2} R) ℕ :=
  CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy.total.{1, 2} R U
    (TypedSectionPullback.IntrinsicPadicGeometricTypedSectionPullback.sourceIntegral p u n)

def targetIntegral : CochainComplex (ModuleCat.{2} R) ℕ :=
  CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy.total.{1, 2} R U
    (TypedSectionPullback.IntrinsicPadicGeometricTypedSectionPullback.targetIntegral p u n)

def sourceComparison : sourceIntegral p u n ⟶ GeometricCone.IntrinsicPadicGeometricConeTotalMaps.sourceNew p u f₁ n I₁ :=
  Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.map.{1, 2} R (IntegralComparison.NonemptyCechNerve.nerve U)
    (TypedSectionPullback.IntrinsicPadicGeometricTypedSectionPullback.sourceComparison p u f₁ hp₁ n I₁)

def targetComparison : targetIntegral p u n ⟶ GeometricCone.IntrinsicPadicGeometricConeTotalMaps.targetNew p u f₂ n I₂ :=
  Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.map.{1, 2} R (IntegralComparison.NonemptyCechNerve.nerve U)
    (TypedSectionPullback.IntrinsicPadicGeometricTypedSectionPullback.targetComparison p u f₂ hp₂ n I₂)

def integralMap : targetIntegral p u n ⟶ sourceIntegral p u n :=
  Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.map.{1, 2} R (IntegralComparison.NonemptyCechNerve.nerve U)
    (TypedSectionPullback.IntrinsicPadicGeometricTypedSectionPullback.integralMap p u n)

def injectiveMap : GeometricCone.IntrinsicPadicGeometricConeTotalMaps.targetNew p u f₂ n I₂ ⟶ GeometricCone.IntrinsicPadicGeometricConeTotalMaps.sourceNew p u f₁ n I₁ :=
  Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.map.{1, 2} R (IntegralComparison.NonemptyCechNerve.nerve U)
    (TypedSectionPullback.IntrinsicPadicGeometricTypedSectionPullback.injectiveMap p u v f₁ f₂ hsquare n I₁ I₂)

def sourceComparisonHOne : (sourceIntegral p u n).homology 1 ⟶ (GeometricCone.IntrinsicPadicGeometricConeTotalMaps.sourceNew p u f₁ n I₁).homology 1 :=
  HomologicalComplex.homologyMap (sourceComparison p u f₁ hp₁ n I₁) 1

def targetComparisonHOne : (targetIntegral p u n).homology 1 ⟶ (GeometricCone.IntrinsicPadicGeometricConeTotalMaps.targetNew p u f₂ n I₂).homology 1 :=
  HomologicalComplex.homologyMap (targetComparison p u f₂ hp₂ n I₂) 1

def integralHOne : (targetIntegral p u n).homology 1 ⟶ (sourceIntegral p u n).homology 1 :=
  HomologicalComplex.homologyMap (integralMap p u n) 1

def injectiveHOne : (GeometricCone.IntrinsicPadicGeometricConeTotalMaps.targetNew p u f₂ n I₂).homology 1 ⟶ (GeometricCone.IntrinsicPadicGeometricConeTotalMaps.sourceNew p u f₁ n I₁).homology 1 :=
  HomologicalComplex.homologyMap (injectiveMap p u v f₁ f₂ hsquare n I₁ I₂) 1

def globalHOne : (ConeSectionData.IntrinsicPadicGeometricConeSectionData.targetGlobal p n I₂).homology 1 ⟶
    (ConeSectionData.IntrinsicPadicGeometricConeSectionData.sourceGlobal p n I₁).homology 1 :=
  HomologicalComplex.homologyMap (TypedSectionPullback.IntrinsicPadicGeometricTypedSectionPullback.globalMap p v n I₁ I₂) 1

theorem homology : targetComparisonHOne p u f₂ hp₂ n I₂ ≫
    injectiveHOne p u v f₁ f₂ hsquare n I₁ I₂ =
      integralHOne p u n ≫ sourceComparisonHOne p u f₁ hp₁ n I₁ :=
  CechPresheaf.OneHomotopySquare.CechPresheafHOneHomotopySquare.homology.{1, 2, 0, 0} R U
    (TypedSectionPullback.IntrinsicPadicGeometricTypedSectionPullback.targetComparison p u f₂ hp₂ n I₂)
    (TypedSectionPullback.IntrinsicPadicGeometricTypedSectionPullback.injectiveMap p u v f₁ f₂ hsquare n I₁ I₂)
    (TypedSectionPullback.IntrinsicPadicGeometricTypedSectionPullback.integralMap p u n)
    (TypedSectionPullback.IntrinsicPadicGeometricTypedSectionPullback.sourceComparison p u f₁ hp₁ n I₁)
    (TypedSectionPullback.IntrinsicPadicGeometricTypedSectionPullback.homotopy p u v f₁ f₂ hp₁ hp₂ hsquare n I₁ I₂)

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem cone_homology : CommonHomologyMaps.IntrinsicPadicGeometricConeHomologyMaps.target_edge p u f₂ n I₂ ≫
    injectiveHOne p u v f₁ f₂ hsquare n I₁ I₂ =
      globalHOne p v n I₁ I₂ ≫ CommonHomologyMaps.IntrinsicPadicGeometricConeHomologyMaps.source_edge p u f₁ n I₁ :=
  CechCone.CohomologyNaturality.CechConeHOneNaturality.homology.{1, 2, 0, 0} R U
    (ConeSectionData.IntrinsicPadicGeometricConeSectionData.targetNewCone p u f₂ n I₂)
    (ConeSectionData.IntrinsicPadicGeometricConeSectionData.sourceNewCone p u f₁ n I₁)
    (TypedSectionPullback.IntrinsicPadicGeometricTypedSectionPullback.injectiveMap p u v f₁ f₂ hsquare n I₁ I₂)
    (TypedSectionPullback.IntrinsicPadicGeometricTypedSectionPullback.globalMap p v n I₁ I₂)
    (TypedSectionPullback.IntrinsicPadicGeometricTypedSectionPullback.cone_naturality p u v f₁ f₂ hsquare n I₁ I₂)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.TypedCechPullback.IntrinsicPadicGeometricTypedCechPullback
