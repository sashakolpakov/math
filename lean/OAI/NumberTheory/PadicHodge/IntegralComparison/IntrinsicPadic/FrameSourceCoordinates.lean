import OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.SourceCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameSheafCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.SheafSectionNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SheafConstantCoordinates

/-! # Frame Source Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameSourceCoordinates.Intrinsic

noncomputable section

/-! The native sheafified frame map uses the canonical coefficient-source
isomorphism and the original constant-sheaf level transformation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p)))) (n : ℕ)

local notation "W" => WittVector p (ZMod p)
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)
local notation "CR" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "JT" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.topology
  (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.sheafification
  (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.RelativeResolution.coefficientFunctor (B := W)
local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.pdComplexes p X Y f hp n
local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.diagram p X Y f hp n
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X
local notation "M" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameProductMap.Intrinsic.complex p X Y f hp n

local instance separated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

local instance sheafCoproducts : HasCoproducts.{0}
    (BoundedCrystalline.Site.ModuleSheaf
      (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n) :=
  GeometricComparison.Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts CR JT

abbrev constantFunctor := constantSheaf JT (ModuleCat.{1} CR)
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameSourceCoordinates.Intrinsic.constantFunctor p Y n

abbrev sourceIso := CechCoefficient.SourceCoordinates.sourceIso F U Q M
  (Cech.ComplexDiagramCoordinates.totalIso U Q)

def transformation := Functor.whiskerLeft
  (GeometricComparison.IntrinsicPadic.FrameFunctor.IntrinsicPadicFrameFunctor.functor p X Y f hp n).op
  (GeometricComparison.Frame.SheafSectionNaturality.FrameSheafSectionNaturality.sheafTransformation
    (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n)

abbrev sheafMap := ((S).mapHomologicalComplex (.up ℕ)).map
  (FrameProductMap.Intrinsic.map p X Y f hp n)

abbrev comparison := CechCoefficient.SourceCoordinates.map_composite F T U Q P
  (transformation p X Y f hp n) M (Cech.ComplexDiagramCoordinates.totalIso U Q)
  (GeometricComparison.IntrinsicPadic.CechSheafResolution.IntrinsicPadicCechSheafResolution.complex p X Y f hp n)
  (sheafMap p X Y f hp n) (GeometricComparison.IntrinsicPadic.PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalIso p X Y f hp n).hom
  (FrameSheafCoordinates.Intrinsic.map_eq p X Y f hp n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameSourceCoordinates.Intrinsic
