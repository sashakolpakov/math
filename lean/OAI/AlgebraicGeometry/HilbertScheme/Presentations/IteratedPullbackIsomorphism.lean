import OAI.AlgebraicGeometry.HilbertScheme.Presentations.OpenPullbackIsomorphismTransport

/-! # Iterated Pullback Isomorphism -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.IteratedPullbackIsomorphism

noncomputable section

/-! Isomorphism of the projection after two successive base changes is
equivalent to isomorphism after their composite base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {W X Y B : Scheme.{u}}

theorem isIso_pullback_fst_iterated_iff (g : Y ⟶ B) (f : X ⟶ B) (h : W ⟶ Y) :
    IsIso (pullback.fst h (pullback.fst g f)) ↔ IsIso (pullback.fst (h ≫ g) f) := by
  rw [← isIso_comp_left_iff (pullbackRightPullbackFstIso g f h).hom,
    pullbackRightPullbackFstIso_hom_fst]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.IteratedPullbackIsomorphism
