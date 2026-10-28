import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.OpenTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameSourceCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameDiagonalMap

/-! # Constant Open Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.ConstantOpenCoordinates.Intrinsic

noncomputable section

/-! The canonical constant-sheaf section construction is the original
frame-to-open-section transformation on the actual truncated model. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p)))) (n : ℕ)

local notation "W" => WittVector p (ZMod p)
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)
local notation "CR" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W)
local notation "JT" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.topology
  (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n
local notation "G" => OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.globalSections
  (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n
local notation "S" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionBifunctor.IntrinsicPadicSectionBifunctor.sections p X Y f n
local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.pdComplexes p X Y f hp n ⋙
  Functor.mapHomologicalComplex (Crystalline.RelativeResolution.coefficientFunctor (B := W)) (ComplexShape.up ℕ)
local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.diagram p X Y f hp n
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameSourceCoordinates.Intrinsic.transformation p X Y f hp n

local instance separated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

local instance constZero :
    (Functor.const X.left.affineOpensᵒᵖ : ModuleCat.{2} CR ⥤
      X.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} CR).PreservesZeroMorphisms where
  map_zero _ _ := rfl

def restriction : G ⋙ Functor.const X.left.affineOpensᵒᵖ ⟶ S :=
  Functor.whiskerRight (GeometricComparison.Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.transformation
    (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n)
    ((Functor.whiskeringLeft X.left.affineOpensᵒᵖ Y.left.Opensᵒᵖ (ModuleCat.{2} CR)).obj
      (GeometricComparison.IntrinsicPadic.SectionBifunctor.IntrinsicPadicSectionBifunctor.specialOpens p X Y f).op)

abbrev extIso := Ext.ZeroPresheafSections.iso.{1,0,1,2} CR JT

def transformation := ConstantSection.OpenTotal.transformation.{1,0,1,2,0,0} CR JT G S
  (extIso p Y n).hom (restriction p X Y f n) Q P a

omit [IsProper X.hom] [X.left.IsSeparated] in
theorem transformation_eq : transformation p X Y f hp n =
    GeometricComparison.IntrinsicPadic.FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.openTransformation p X Y f hp n := by
  apply NatTrans.ext
  funext U
  apply HomologicalComplex.Hom.ext
  funext i
  apply NatTrans.ext
  funext V
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.ConstantOpenCoordinates.Intrinsic
