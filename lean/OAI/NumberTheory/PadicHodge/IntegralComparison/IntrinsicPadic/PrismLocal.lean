import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.CechPrism
import OAI.NumberTheory.PadicHodge.IntegralComparison.Constant.ComplexPrismDiagonal
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameDiagonalIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.LocalQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.RegroupedLocalQuasiIso

/-! # Prism Local -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.PrismLocal.IntrinsicComparison

noncomputable section

/-! The actual truncated-model local diagonal augmentations are
quasi-isomorphisms on the chosen cover and all its intersections.
Their original outer Čech total is therefore a quasi-isomorphism. -/

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
local notation "γ" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.CechPrism.Intrinsic.cone p X Y f hp n
local notation "h" => fun I V => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionRowRestriction.IntrinsicPadicSectionRowRestriction.meet_isIso p X Y f hp n V I

local instance constZero :
    (Functor.const X.left.affineOpensᵒᵖ : ModuleCat.{2} R ⥤
      X.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} R).PreservesZeroMorphisms where
  map_zero _ _ := rfl

def localMap := CechPrism.LocalAugmentation.map U Q B γ h

variable (I : X.left.affineOpens)
  (i : GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X)
  (hi : I.val ≤ GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X i)

include hi in
omit [X.left.IsSeparated] in
theorem own_chart_isIso : IsIso (((γ).app (op I)).app (op I)) := by
  have he := Constant.ComplexPrismDiagonal.Cone.diagonal Q
    (P ⋙ (S).mapHomologicalComplex (.up ℕ))
    (GeometricComparison.IntrinsicPadic.FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.openTransformation p X Y f hp n) (op I)
  exact he.symm ▸ GeometricComparison.IntrinsicPadic.FrameDiagonalIso.IntrinsicPadicFrameDiagonalIso.isIso p X Y f hp n I i hi

include hi in
theorem local_quasiIso : QuasiIso ((localMap p X Y f hp n).app (op I)) := by
  have : IsIso (((γ).app (op I)).app (op I)) := own_chart_isIso p X Y f hp n I i hi
  exact CechPrism.LocalQuasiIso.quasiIso.{1,0,2} R U Q B γ h I i hi

theorem intersection_quasiIso (j : ℕ)
    (b : Fin (j+1) → GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X) :
    QuasiIso (((γ).app (op (∏ᶜ (U ∘ b)))).app (op (∏ᶜ (U ∘ b)))) := by
  have : IsIso (((γ).app (op (∏ᶜ (U ∘ b)))).app (op (∏ᶜ (U ∘ b)))) :=
    own_chart_isIso p X Y f hp n (∏ᶜ (U ∘ b)) (b 0) (leOfHom (Pi.π (U ∘ b) 0))
  infer_instance

theorem quasiIso : QuasiIso (CechPrism.Regrouped.Comparison.diagonal R U Q B γ h) := CechPrism.RegroupedLocalQuasiIso.diagonal.{1,0,2} R U Q B γ h
  (intersection_quasiIso p X Y f hp n)

theorem global_quasiIso : QuasiIso (CechPrism.Regrouped.Comparison.global R U Q B γ) := CechPrism.RegroupedLocalQuasiIso.global.{1,0,2} R U Q B γ h
  (intersection_quasiIso p X Y f hp n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.PrismLocal.IntrinsicComparison
