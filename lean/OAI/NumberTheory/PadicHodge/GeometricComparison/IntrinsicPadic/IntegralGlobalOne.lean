import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveCechGlobal
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralCechOne

/-! # Integral Global One -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralGlobalOne.IntrinsicPadicIntegralGlobalHOne

noncomputable section

/-! The canonical integral de Rham quotient Cech total computes original global
bounded crystalline H-one through its original injective section comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ)

local notation "Rcoeff" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "coverNerve" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve (OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X)
local notation "wittMap" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y

variable (J : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
  (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) n))

def homologyIso :=
  letI := IntegralCechOne.IntrinsicPadicIntegralCechHOne.quasiIsoAt p X Y f hp n J
  isoOfQuasiIsoAt (IntegralCechOne.IntrinsicPadicIntegralCechHOne.map p X Y f hp n J) 1 ≪≫
    InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.homologyIso p X Y f n J 1

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralGlobalOne.IntrinsicPadicIntegralGlobalHOne
