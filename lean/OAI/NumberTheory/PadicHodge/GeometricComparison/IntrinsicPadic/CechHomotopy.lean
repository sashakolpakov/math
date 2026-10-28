import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralInjectiveHomotopy
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TotalHomotopySquare
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinedHomotopy
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.OneHomotopySquare

/-! # Cech Homotopy -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechHomotopy.IntrinsicPadicGeometricCechHomotopy

noncomputable section

/-! Actual geometric homotopy of the native integral comparisons
induces a commuting H-one square on the original paired Cech total. -/

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
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U

local instance limits : HasLimitsOfSize.{0, 0} (ModuleCat.{2} R) := ModuleCat.hasLimitsOfSize.{0, 0, 2, 1}
local instance colimits : HasColimitsOfSize.{0, 0} (ModuleCat.{2} R) := ModuleCat.hasColimitsOfSize.{2, 1, 0, 0} R

def sourceComparison := Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.map.{1, 2} R E
  (IntegralInjectiveHomotopy.IntrinsicPadicGeometricIntegralInjectiveHomotopy.sourceComparison p u f₁ hp₁ n I₁)
def targetComparison := Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.map.{1, 2} R E
  (IntegralInjectiveHomotopy.IntrinsicPadicGeometricIntegralInjectiveHomotopy.targetComparison p u f₂ hp₂ n I₂)
def sourceMap := Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.map.{1, 2} R E
  (IntegralInjectiveHomotopy.IntrinsicPadicGeometricIntegralInjectiveHomotopy.geometricMap p u n)
def targetMap := Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.map.{1, 2} R E
  (SectionHomotopy.IntrinsicPadicGeometricSectionHomotopy.injectiveMap p u v f₁ f₂ hsquare n I₁ I₂)

def sourceComparisonHOne := CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy.mapHOne.{1, 2} R U
  (IntegralInjectiveHomotopy.IntrinsicPadicGeometricIntegralInjectiveHomotopy.sourceComparison p u f₁ hp₁ n I₁)
def targetComparisonHOne := CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy.mapHOne.{1, 2} R U
  (IntegralInjectiveHomotopy.IntrinsicPadicGeometricIntegralInjectiveHomotopy.targetComparison p u f₂ hp₂ n I₂)
def sourceHOneMap := CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy.mapHOne.{1, 2} R U
  (IntegralInjectiveHomotopy.IntrinsicPadicGeometricIntegralInjectiveHomotopy.geometricMap p u n)
def targetHOneMap := CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy.mapHOne.{1, 2} R U
  (SectionHomotopy.IntrinsicPadicGeometricSectionHomotopy.injectiveMap p u v f₁ f₂ hsquare n I₁ I₂)

theorem homology : targetComparisonHOne p u f₂ hp₂ n I₂ ≫ targetHOneMap p u v f₁ f₂ hsquare n I₁ I₂ =
    sourceHOneMap p u n ≫ sourceComparisonHOne p u f₁ hp₁ n I₁ :=
  CechPresheaf.OneHomotopySquare.CechPresheafHOneHomotopySquare.homology.{1, 2, 0, 0} R U
    (IntegralInjectiveHomotopy.IntrinsicPadicGeometricIntegralInjectiveHomotopy.targetComparison p u f₂ hp₂ n I₂)
    (SectionHomotopy.IntrinsicPadicGeometricSectionHomotopy.injectiveMap p u v f₁ f₂ hsquare n I₁ I₂)
    (IntegralInjectiveHomotopy.IntrinsicPadicGeometricIntegralInjectiveHomotopy.geometricMap p u n)
    (IntegralInjectiveHomotopy.IntrinsicPadicGeometricIntegralInjectiveHomotopy.sourceComparison p u f₁ hp₁ n I₁)
    (IntegralInjectiveHomotopy.IntrinsicPadicGeometricIntegralInjectiveHomotopy.homotopy p u v f₁ f₂ hp₁ hp₂ hsquare n I₁ I₂)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechHomotopy.IntrinsicPadicGeometricCechHomotopy
