import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFamilyIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SmallFrameOpens
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSections

/-! # Principal Opens Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalOpensIso

noncomputable section

/-! Transported native principal frames use literally equal original
special-fiber opens in the section comparison. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
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

local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFrame.Index X₁.left U₁
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFamilyIso.Family.reindex p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e
local notation "P₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Diagram.functor X₁.left U₁.val U₁.property
local notation "P₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Diagram.functor X₂.left U₂.val U₂.property

omit [IsProper X₁.hom] [X₁.left.IsSeparated] [IsProper X₂.hom] [X₂.left.IsSeparated] [IsSeparated Y.hom] in
theorem opens_apply (r : C) :
    PrincipalSections.opens p k n X₂ Y f₂ U₂ ((R).obj r) =
      PrincipalSections.opens p k n X₁ Y f₁ U₁ r := by
  have hs := PrincipalFamilyIso.Family.special_opens_eq p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e r
  change ((SmallFrame.functor p k n X₂ Y f₂ hp₂).obj ((P₂).obj ((R).obj r))).immersion.opensRange =
    ((SmallFrame.functor p k n X₁ Y f₁ hp₁).obj ((P₁).obj r)).immersion.opensRange at hs
  rw [SmallFrameOpens.opensRange, SmallFrameOpens.opensRange] at hs
  exact hs

omit [IsProper X₁.hom] [X₁.left.IsSeparated] [IsProper X₂.hom] [X₂.left.IsSeparated] [IsSeparated Y.hom] in
theorem opens_function :
    (fun r : C => PrincipalSections.opens p k n X₂ Y f₂ U₂ ((R).obj r)) =
      (fun r : C => PrincipalSections.opens p k n X₁ Y f₁ U₁ r) :=
  funext (opens_apply p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalOpensIso
