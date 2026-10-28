import OAI.NumberTheory.PadicHodge.IntegralComparison.Constant.ComplexPrismCone
import OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.ModuleTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameDiagonalMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionRowRestriction
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution

/-! # Cech Prism -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.CechPrism.Intrinsic

noncomputable section

/-! The signed Čech prism for the actual truncated-model frame
and open-section diagrams. Every inverse-meet hypothesis is supplied
by the native frame restriction theorem. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p)))) (n : ℕ)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X
local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.source p X Y f hp n
local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.diagram p X Y f hp n
local notation "S" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionBifunctor.IntrinsicPadicSectionBifunctor.sections p X Y f n
local notation "B" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionBifunctor.IntrinsicPadicSectionBifunctor.rows p X Y f hp n

local instance constZero :
    (Functor.const X.left.affineOpensᵒᵖ : ModuleCat.{2} R ⥤
      X.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} R).PreservesZeroMorphisms where
  map_zero _ _ := rfl

def cone : (Functor.const X.left.affineOpensᵒᵖ).obj Q ⟶ B :=
  Constant.ComplexPrismCone.cone Q (P ⋙ (S).mapHomologicalComplex (.up ℕ))
    (GeometricComparison.IntrinsicPadic.FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.openTransformation p X Y f hp n)

def diagonal := CechPrism.ModuleTotal.diagonal R U Q B
  (cone p X Y f hp n)
  (fun I V => GeometricComparison.IntrinsicPadic.SectionRowRestriction.IntrinsicPadicSectionRowRestriction.meet_isIso p X Y f hp n V I)

def global := CechPrism.ModuleTotal.global R U Q B (cone p X Y f hp n)

theorem homology (i : ℕ) : HomologicalComplex.homologyMap (diagonal p X Y f hp n) i =
    HomologicalComplex.homologyMap (global p X Y f hp n) i :=
  CechPrism.ModuleTotal.homology R U Q B (cone p X Y f hp n)
    (fun I V => GeometricComparison.IntrinsicPadic.SectionRowRestriction.IntrinsicPadicSectionRowRestriction.meet_isIso p X Y f hp n V I) i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.CechPrism.Intrinsic
