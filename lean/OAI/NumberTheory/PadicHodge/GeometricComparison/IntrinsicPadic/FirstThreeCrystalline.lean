import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechCompletion

/-! # First Three Crystalline -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FirstThreeCrystalline.IntrinsicPadicFirstThreeCrystalline

noncomputable section

/-! The finite crystalline comparison has the actual coefficient-power
quotient cohomology of the integral three-term Cech complex as its source. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]

local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X
local notation "C" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechCompletion.IntegralFirstThreeCechCompletion.complex ℤ_[p] X U
local notation "coefficients" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.coefficients p

def sourceHomologyIso (n : ℕ) :
    (Coefficient.IntrinsicPadicSmallQuotientTotal.total p X n).homology 1 ≅
      (PrincipalCochainExact.PrincipalCochainQuotient.quotient ℤ_[p] C (p : ℤ_[p]) (n + 1)).homology 1 :=
  Coefficient.IntrinsicPadicSmallQuotientTotal.firstThreeHomologyIso p X n ≪≫
    (IntegralCech.QuotientTotal.IntegralCechQuotientTotal.homologyIso ℤ_[p] X U
      ((Ideal.span {(p : ℤ_[p])}) ^ (n + 1)) 1).symm

variable
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ)
  (J : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) n))

def homologyIso :=
  (coefficients).mapIso (sourceHomologyIso p X n).symm ≪≫
    (Coefficient.IntrinsicPadicCoefficientHomology.iso p (Coefficient.IntrinsicPadicSmallQuotientTotal.total p X n) 1).symm ≪≫
      Coefficient.IntrinsicPadicSmallQuotientTotal.homologyIso p X Y f hp n J

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FirstThreeCrystalline.IntrinsicPadicFirstThreeCrystalline
