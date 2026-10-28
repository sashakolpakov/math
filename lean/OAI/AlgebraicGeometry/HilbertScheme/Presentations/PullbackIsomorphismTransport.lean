import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Pullback Isomorphism Transport -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.PullbackIsomorphismTransport

noncomputable section

/-! Isomorphism of a base-change projection is unchanged by replacing
the source of the original morphism by an isomorphic scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {W X Y B : Scheme.{u}}

theorem isIso_pullback_fst_comp_right_iff (g : Y ⟶ B) (f : X ⟶ B)
    (e : W ⟶ X) [IsIso e] :
    IsIso (pullback.fst g (e ≫ f)) ↔ IsIso (pullback.fst g f) := by
  rw [← isIso_comp_left_iff (pullbackLeftPullbackSndIso g f e).hom,
    pullbackLeftPullbackSndIso_hom_fst, isIso_comp_left_iff]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.PullbackIsomorphismTransport
