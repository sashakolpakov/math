import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalOpensIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn

/-! # Principal Open Functor Eq -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalOpenFunctorEq

noncomputable section

/-! The two native principal families have equal functors of
original geometric opens after the actual coefficient reindexing. -/

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

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFamilyIso.Family.reindex p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e

omit [IsProper X₁.hom] [X₁.left.IsSeparated] [IsProper X₂.hom] [X₂.left.IsSeparated] [IsSeparated Y.hom] in
theorem opens_eq : (R).op ⋙ PrincipalIn.Family.opens p k n X₂ Y f₂ U₂ =
    PrincipalIn.Family.opens p k n X₁ Y f₁ U₁ :=
  CategoryTheory.Functor.ext (fun r => congrArg op
    (PrincipalOpensIso.opens_apply p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e r.unop))
    (fun _ _ _ => Subsingleton.elim _ _)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalOpenFunctorEq
