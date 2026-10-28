import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.LevelSourceCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresheafConeLevelCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameProductMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicDiagonalCechComparison

/-! # Frame Sheaf Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameSheafCoordinates.Intrinsic

noncomputable section

/-! The original native frame map, after coefficient change and
sheafification, is the literal Čech cone level map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p)))) (n : ℕ)

local notation "W" => WittVector p (ZMod p)
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)
local notation "D" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.Objects
  (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n
local notation "Rcoeff" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.sheafification
  (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n
local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.pdComplexes p X Y f hp n
local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechPresheafResolution.IntrinsicPadicCechPresheafResolution.diagram p X Y f hp n
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameProductMap.Intrinsic.transformation p X Y f hp n

local instance separated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

local instance sheafCoproducts : HasCoproducts.{0}
    (BoundedCrystalline.Site.ModuleSheaf
      (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n) :=
  GeometricComparison.Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts Rcoeff
    (BoundedCrystalline.Site.topology
      (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n)

abbrev map_eq := Cech.LevelSourceCoordinates.map (Functor.const Dᵒᵖ) S U Q P a
  (FrameProductMap.Intrinsic.complex p X Y f hp n)
  (Cech.ComplexDiagramCoordinates.totalIso U Q).hom
  (FrameProductMap.Intrinsic.map p X Y f hp n)
  (Cech.PresheafConeLevelCoordinates.map_eq W U Q P a)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameSheafCoordinates.Intrinsic
