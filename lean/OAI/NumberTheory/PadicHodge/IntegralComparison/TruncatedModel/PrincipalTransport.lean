import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFamilyIso

/-! # Principal Transport -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTransport

noncomputable section

/-! The native principal-family isomorphism commutes with the exact
localization maps used by the original PD-complex comparison. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
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

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFamilyIso.Family.reindex p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e
local notation "s" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFamilyIso.Family.iso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e

theorem principal_square : (s).hom ≫ PrincipalFrame.transformation p k n X₁ Y f₁ hp₁ U₁ =
    Functor.whiskerLeft (R) (PrincipalFrame.transformation p k n X₂ Y f₂ hp₂ U₂) ≫
      (CrystallinePrincipal.Iso.diagramIso p k Y e).hom := by
  apply NatTrans.ext
  funext r
  change (PrincipalFrame.map p k n X₂ Y f₂ hp₂ U₂ ((R).obj r) ≫
    CrystallinePrincipal.Iso.map p k Y e r ≫
      (PrincipalSmallIso.diagramIso p k n X₁ Y f₁ hp₁ U₁).inv.app r) ≫
        PrincipalFrame.map p k n X₁ Y f₁ hp₁ U₁ r = _
  have hi : (PrincipalSmallIso.diagramIso p k n X₁ Y f₁ hp₁ U₁).inv.app r ≫
      PrincipalFrame.map p k n X₁ Y f₁ hp₁ U₁ r = 𝟙 _ :=
    ((PrincipalSmallIso.diagramIso p k n X₁ Y f₁ hp₁ U₁).app r).inv_hom_id
  rw [Category.assoc, Category.assoc, hi]
  exact congrArg (fun z => PrincipalFrame.map p k n X₂ Y f₂ hp₂ U₂ ((R).obj r) ≫ z)
    (Category.comp_id (CrystallinePrincipal.Iso.map p k Y e r))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTransport
