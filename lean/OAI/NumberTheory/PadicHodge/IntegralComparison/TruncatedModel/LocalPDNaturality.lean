import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.LocalPrincipal
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.LocalPDMap

/-! # Local PD Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.LocalPDNaturality

noncomputable section

/-! The complete original local comparison square, including the reindexed composite, assembled before model specialization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ)
  (X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X₁.hom] [Smooth X₁.hom] [X₁.left.IsSeparated]
  [IsProper X₂.hom] [Smooth X₂.hom] [X₂.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom]
  (f₁ : Y.left ⟶ X₁.left) (f₂ : Y.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y.hom X₁.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y.hom X₂.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U₁ : X₁.left.affineOpens) (U₂ : X₂.left.affineOpens)
  (e : (SmallFrame.functor p k n X₂ Y f₂ hp₂).obj U₂ ≅
    (SmallFrame.functor p k n X₁ Y f₁ hp₁).obj U₁)

local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalCoefficientNaturality.restriction p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e
local notation "s" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalCoefficientNaturality.sourceIso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e

local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFamilyIso.Family.reindex p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e
local notation "O₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.opens p k n X₁ Y f₁ U₁
local notation "O₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.opens p k n X₂ Y f₂ U₂
local notation "G₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.frames p k n X₁ Y f₁ hp₁ U₁
local notation "G₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.frames p k n X₂ Y f₂ hp₂ U₂
local notation "F₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.center p k n X₁ Y f₁ hp₁ U₁
local notation "F₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.center p k n X₂ Y f₂ hp₂ U₂
local notation "ρ₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.cone p k n X₁ Y f₁ hp₁ U₁
local notation "ρ₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.cone p k n X₂ Y f₂ hp₂ U₂

attribute [local instance] LocalPrincipal.Sections.globalSeparated

abbrev naturality := by
  let : IsIso (BoundedFrame.LocalMap.restriction w n O₁ G₁ F₁ ρ₁) :=
    PrincipalIn.Family.fixed_isIso p k n X₁ Y f₁ hp₁ U₁
  let : IsIso (BoundedFrame.LocalMap.restriction w n O₂ G₂ F₂ ρ₂) :=
    PrincipalIn.Family.fixed_isIso p k n X₂ Y f₂ hp₂ U₂
  exact BoundedFrame.LocalPDMap.Square.mapped_comparison w n (R).op O₁ O₂ G₁ G₂ F₁ F₂ ρ₁ ρ₂
    (PrincipalTransportedFamily.Family.iso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e)
    (PrincipalTransportedFamily.Family.baseIso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e)
    (PrincipalTransportedFamily.Family.projection_square p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e)
    (PrincipalOpenFunctorEq.opens_eq p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).symm
    (Principal.Comparison.source p k n X₁ Y f₁ hp₁ U₁)
    (Principal.Comparison.source p k n X₂ Y f₂ hp₂ U₂)
    (Principal.Comparison.coefficientMap p k n X₁ Y f₁ hp₁ U₁)
    (Principal.Comparison.coefficientMap p k n X₂ Y f₂ hp₂ U₂)
    (s).hom (LocalPrincipal.PDNaturality.coefficient_square p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.LocalPDNaturality
