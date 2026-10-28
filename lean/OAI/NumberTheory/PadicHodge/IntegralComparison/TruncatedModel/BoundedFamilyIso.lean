import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.BoundedFrameIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFamilyIso

/-! # Bounded Family Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.BoundedFamilyIso.Family

noncomputable section

/-! The native principal-family isomorphism and its projection square
on the original bounded crystalline site. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ)
  (X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [Smooth X₁.hom] [Smooth X₂.hom]
  (Y : Over (Spec (CommRingCat.of k)))
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
local notation "G₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameFunctor.functor p k n X₁ Y f₁ hp₁
local notation "G₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameFunctor.functor p k n X₂ Y f₂ hp₂
local notation "s" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFamilyIso.Family.iso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e

def baseIso := BoundedFrameIso.iso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e

def iso : (R) ⋙ (P₂) ⋙ (G₂) ≅ (P₁) ⋙ (G₁) :=
  NatIso.ofComponents (fun r => BoundedFrameIso.iso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂
    ((P₁).obj r) ((P₂).obj ((R).obj r)) ((s).app r)) (by
      intro r t a
      apply ObjectProperty.hom_ext
      apply BigCrystallineSite.Object.Hom.ext
      ext z
      exact congrArg (fun f => f.ambientMap z) ((s).hom.naturality a))

def projection (r : C) : ((R) ⋙ (P₂) ⋙ (G₂)).obj r ⟶ (G₂).obj U₂ :=
  (G₂).map (AffinePrincipal.Diagram.projection X₂.left U₂.val U₂.property ((R).obj r))

theorem projection_square (r : C) :
    (iso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).hom.app r ≫
      (G₁).map (AffinePrincipal.Diagram.projection X₁.left U₁.val U₁.property r) =
        projection p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e r ≫
          (baseIso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).hom := by
  apply ObjectProperty.hom_ext
  apply BigCrystallineSite.Object.Hom.ext
  ext a
  exact congrArg (fun f => f.ambientMap a)
    (PrincipalFamilyIso.Family.projection_square p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e r)

def oppositeIso := NatIso.op (iso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.BoundedFamilyIso.Family
