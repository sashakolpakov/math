import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusReducedZero
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicPrincipalHodgeComparison
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PrincipalGlobalLevel

/-! # Frobenius Principal Zero -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusPrincipalZero.IntrinsicPadicFrobeniusPrincipalHodgeZero

noncomputable section

/-! Actual bounded crystalline Frobenius kills the original principal
reduction of the integral first Hodge image under the constructed finite comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (I : InjectiveResolution (IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y)))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "wittMap" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "Iq" => fun q : ℕ => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution wittMap q I
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve (OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X)

local notation "F" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.coefficients p
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X
local notation "B" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.bicomplex ℤ_[p] X U
local notation "K" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechCompletion.IntegralFirstThreeCechCompletion.complex ℤ_[p] X U

theorem homology :
    (F).map (HomologicalComplex.homologyMap
      (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion B 1) (.up ℕ)) 1) ≫
    (F).map (ModuleCat.ofHom (CochainQuotientCohomology.PrincipalCochainQuotient.reduction ℤ_[p] K (p : ℤ_[p]) 1 1)) ≫
      (PrincipalGlobalLevel.IntrinsicPadicPrincipalGlobalLevel.iso p X Y f hp I 0).hom ≫
        FrobeniusReducedZero.IntrinsicPadicFrobeniusReducedHodgeZero.frobenius p Y = 0 := by
  have h := ImageZero.ComparisonImageZero.factor
    ((F).map (HomologicalComplex.homologyMap
      (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion B 1) (.up ℕ)) 1))
    ((F).map (ModuleCat.ofHom (CochainQuotientCohomology.PrincipalCochainQuotient.reduction ℤ_[p] K (p : ℤ_[p]) 1 1)))
    (PrincipalCoefficientLevel.IntrinsicPadicPrincipalCoefficientLevel.iso p X 0).hom
    (PadicPrincipalHodgeComparison.IntrinsicPadicPrincipalHodgeComparison.map p X 0 1)
    (FrobeniusReducedZero.IntrinsicPadicFrobeniusReducedHodgeZero.inclusion p X)
    ((IntegralGlobalLevel.IntrinsicPadicIntegralGlobalLevel.homologyIso p X Y f hp I 0).hom ≫
      FrobeniusReducedZero.IntrinsicPadicFrobeniusReducedHodgeZero.frobenius p Y)
    (PadicPrincipalHodgeComparison.IntrinsicPadicPrincipalHodgeComparison.inclusion p X 0 1)
    (FrobeniusReducedZero.IntrinsicPadicFrobeniusReducedHodgeZero.homology p X Y f hp I)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact ConcreteCategory.congr_hom h x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusPrincipalZero.IntrinsicPadicFrobeniusPrincipalHodgeZero
