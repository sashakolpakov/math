import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FiniteCech
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallAssemblyOne
import OAI.NumberTheory.PadicHodge.GeometricComparison.RefinedGlobalSquare

/-! # Small Finite -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallFinite.IntrinsicPadicGeometricSmallFiniteComparison

noncomputable section

/-! The original small p-adic finite comparison is natural
on the actual common source cover under geometric pullback. -/

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

local notation "F" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.coefficients p

def commonComparison := (SmallCoefficientOne.IntrinsicPadicGeometricSmallCoefficientHOne.sourceIso p u n).hom ≫
  FiniteCech.IntrinsicPadicGeometricFiniteCechComparison.commonComparison p u f₁ hp₁ n I₁

def sourceIso := SmallCoefficientLevel.IntrinsicPadicSmallCoefficientLevel.homologyIso p X₁ n ≪≫
  IntegralGlobalOne.IntrinsicPadicIntegralGlobalHOne.homologyIso p X₁ Y₁ f₁ hp₁ n I₁

def targetIso := SmallCoefficientLevel.IntrinsicPadicSmallCoefficientLevel.homologyIso p X₂ n ≪≫
  IntegralGlobalOne.IntrinsicPadicIntegralGlobalHOne.homologyIso p X₂ Y₂ f₂ hp₂ n I₂

omit [IsSeparated Y₂.hom] in
theorem source : (sourceIso p f₁ hp₁ n I₁).hom =
    (F).map (HomologicalComplex.homologyMap (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.sourceRefinement p u n) 1) ≫
      commonComparison p u f₁ hp₁ n I₁ :=
  RefinedGlobalSquare.RefinedComparisonGlobalSquare.source
    (SmallCoefficientLevel.IntrinsicPadicSmallCoefficientLevel.homologyIso p X₁ n).hom
    (Refinement.IntrinsicPadicGeometricComparisonRefinement.sourceIntegralHOne p u n)
    (IntegralGlobalOne.IntrinsicPadicIntegralGlobalHOne.homologyIso p X₁ Y₁ f₁ hp₁ n I₁).hom
    ((F).map (HomologicalComplex.homologyMap (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.sourceRefinement p u n) 1))
    (SmallCoefficientOne.IntrinsicPadicGeometricSmallCoefficientHOne.sourceIso p u n).hom
    (FiniteCech.IntrinsicPadicGeometricFiniteCechComparison.commonComparison p u f₁ hp₁ n I₁)
    (SmallCoefficientOne.IntrinsicPadicGeometricSmallCoefficientHOne.source p u n).symm
    (FiniteCech.IntrinsicPadicGeometricFiniteCechComparison.source p u f₁ hp₁ n I₁).symm

include hsquare in
theorem target : (targetIso p f₂ hp₂ n I₂).hom ≫
    ModuleCat.ofHom (IntegralComparison.BoundedCrystalline.CrystallinePullback.pullback v.left
      (FrameData.IntrinsicPadicFrameGeometricData.global_over_witt p v) n 1) =
    (F).map (HomologicalComplex.homologyMap (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.targetRefinement p u n) 1) ≫
      (F).map (HomologicalComplex.homologyMap (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.geometricMap p u n) 1) ≫
        commonComparison p u f₁ hp₁ n I₁ :=
  RefinedGlobalSquare.RefinedComparisonGlobalSquare.target
    (SmallCoefficientLevel.IntrinsicPadicSmallCoefficientLevel.homologyIso p X₂ n).hom
    (Refinement.IntrinsicPadicGeometricComparisonRefinement.targetIntegralHOne p u n)
    (IntegralGlobalOne.IntrinsicPadicIntegralGlobalHOne.homologyIso p X₂ Y₂ f₂ hp₂ n I₂).hom
    (ModuleCat.ofHom (IntegralComparison.BoundedCrystalline.CrystallinePullback.pullback v.left
      (FrameData.IntrinsicPadicFrameGeometricData.global_over_witt p v) n 1))
    ((F).map (HomologicalComplex.homologyMap (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.targetRefinement p u n) 1))
    (SmallCoefficientOne.IntrinsicPadicGeometricSmallCoefficientHOne.targetIso p u n).hom
    (CechHomotopy.IntrinsicPadicGeometricCechHomotopy.sourceHOneMap p u n)
    ((F).map (HomologicalComplex.homologyMap (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.geometricMap p u n) 1))
    (SmallCoefficientOne.IntrinsicPadicGeometricSmallCoefficientHOne.sourceIso p u n).hom
    (FiniteCech.IntrinsicPadicGeometricFiniteCechComparison.commonComparison p u f₁ hp₁ n I₁)
    (SmallCoefficientOne.IntrinsicPadicGeometricSmallCoefficientHOne.target p u n).symm
    (SmallAssemblyOne.IntrinsicPadicGeometricSmallAssemblyHOne.naturality p u n).symm
    (FiniteCech.IntrinsicPadicGeometricFiniteCechComparison.target p u v f₁ f₂ hp₁ hp₂ hsquare n I₁ I₂).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallFinite.IntrinsicPadicGeometricSmallFiniteComparison
