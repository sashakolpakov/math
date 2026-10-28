import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.PrismLocal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresheafGlobalAugmentation

/-! # Global Augmentation Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.GlobalAugmentationQuasiIso.Intrinsic

noncomputable section

/-! The literal global presheaf augmentation from the truncated-model
frame Čech total is a quasi-isomorphism. The native own-chart comparison
and the signed Čech prism discharge all local hypotheses. -/

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
local notation "a" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.openTransformation p X Y f hp n

local instance constZero :
    (Functor.const X.left.affineOpensᵒᵖ : ModuleCat.{2} R ⥤
      X.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} R).PreservesZeroMorphisms where
  map_zero _ _ := rfl

theorem quasiIso : QuasiIso (Cech.PresheafGlobalAugmentation.map R U Q
    (P ⋙ (S).mapHomologicalComplex (.up ℕ)) a) := Cech.PresheafGlobalAugmentation.quasiIso R U Q
  (P ⋙ (S).mapHomologicalComplex (.up ℕ)) a
  (PrismLocal.IntrinsicComparison.global_quasiIso p X Y f hp n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.GlobalAugmentationQuasiIso.Intrinsic
