import OAI.AlgebraicGeometry.HilbertScheme.Presentations.PullbackIsomorphismTransport
import Mathlib.AlgebraicGeometry.Restrict

/-! # Open Pullback Isomorphism Transport -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.OpenPullbackIsomorphismTransport

noncomputable section

/-! Isomorphism conditions on pullback projections along open immersions
are exactly isomorphism of the morphism restricted to the actual image open. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {W X Y B : Scheme.{u}}

theorem isIso_pullback_fst_comp_left_iff (g : Y ⟶ B) (f : X ⟶ B)
    (e : W ⟶ Y) [IsIso e] :
    IsIso (pullback.fst (e ≫ g) f) ↔ IsIso (pullback.fst g f) := by
  rw [← isIso_comp_left_iff (pullbackRightPullbackFstIso g f e).hom,
    pullbackRightPullbackFstIso_hom_fst,
    ← isIso_comp_right_iff (pullback.fst e (pullback.fst g f)) e,
    pullback.condition, isIso_comp_left_iff]

theorem isIso_pullback_fst_open_iff (f : X ⟶ Y) (U : Y.Opens) :
    IsIso (pullback.fst U.ι f) ↔ IsIso (f ∣_ U) := by
  rw [← (isPullback_morphismRestrict f U).isoPullback_inv_fst, isIso_comp_left_iff]

theorem isIso_pullback_fst_openImmersion_iff (f : X ⟶ Y) (g : W ⟶ Y) [IsOpenImmersion g] :
    IsIso (pullback.fst g f) ↔ IsIso (f ∣_ g.opensRange) := by
  calc
    IsIso (pullback.fst g f) ↔
        IsIso (pullback.fst (g.isoOpensRange.hom ≫ g.opensRange.ι) f) := by
      rw [Scheme.Hom.isoOpensRange_hom_ι]
    _ ↔ IsIso (pullback.fst g.opensRange.ι f) :=
      isIso_pullback_fst_comp_left_iff _ _ _
    _ ↔ IsIso (f ∣_ g.opensRange) := isIso_pullback_fst_open_iff f g.opensRange

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.OpenPullbackIsomorphismTransport
