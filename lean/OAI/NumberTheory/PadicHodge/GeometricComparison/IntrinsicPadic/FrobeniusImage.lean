import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusFrameInjectiveHomotopy
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusFrameTruncation
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.HomotopyImageZero

/-! # Frobenius Image -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusImage.IntrinsicPadicFrobeniusHodgeImage

noncomputable section

/-! Actual level-zero Frobenius vanishes on the reduced-integral first
Hodge image under the original native comparison on Cech total H-one. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (I : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) 0))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve (OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X)
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (ComplexShape.up ℕ)
  (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.source p X 0)
local notation "a" => OAI.AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (ComplexShape.up ℕ)
  (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.transformation p X Y f hp 0)
local notation "φ" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusFrameTruncation.IntrinsicPadicFrobeniusFrameTruncation.map p X Y f hp
local notation "c" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameInjective.IntrinsicPadicFrameInjectiveComparison.map p X Y f hp 0 I
local notation "b" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusDiagonalInjectiveHomotopy.IntrinsicPadicFrobeniusDiagonalInjectiveHomotopy.injectiveMap p X Y f I
local notation "d" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.map p X Y f hp 0 I

def homotopy : Homotopy (d ≫ b) ((a ≫ φ) ≫ c) :=
  (Homotopy.ofEq (Category.assoc a c b)).trans
    (((FrobeniusFrameInjectiveHomotopy.IntrinsicPadicFrobeniusFrameInjectiveHomotopy.homotopy p X Y f hp I).compLeft a).trans
      (Homotopy.ofEq (Category.assoc a φ c).symm))

theorem homology :
    HomologicalComplex.homologyMap
      (Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.map.{1, 2} R E (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K 1)) 1 ≫
    HomologicalComplex.homologyMap (Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.map.{1, 2} R E d) 1 ≫
    HomologicalComplex.homologyMap (Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.map.{1, 2} R E b) 1 = 0 :=
  Cech.HomotopyImageZero.CechHomotopyImageZero.homology.{1, 2, 0, 0} R E (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K 1)
    d b (a ≫ φ) c (homotopy p X Y f hp I)
      (FrobeniusFrameTruncation.IntrinsicPadicFrobeniusFrameTruncation.integral_source_zero p X Y f hp)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusImage.IntrinsicPadicFrobeniusHodgeImage
