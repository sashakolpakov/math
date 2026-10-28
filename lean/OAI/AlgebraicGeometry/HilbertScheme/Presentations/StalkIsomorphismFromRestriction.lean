import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IteratedPullbackIsomorphism
import Mathlib.AlgebraicGeometry.Stalk

/-! # Stalk Isomorphism From Restriction -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.StalkIsomorphismFromRestriction

noncomputable section

/-! An isomorphism on an open neighborhood remains an isomorphism on
the actual local spectrum at each point of that neighborhood. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

theorem isIso_pullback_stalk_of_isIso_restrict (U : Y.Opens) [IsIso (f ∣_ U)]
    (y : Y) (hy : y ∈ U) : IsIso (pullback.fst (Y.fromSpecStalk y) f) := by
  have hr : Set.range (Y.fromSpecStalk y) ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι, Scheme.range_fromSpecStalk]
    intro z hz
    exact hz.mem_open U.isOpen hy
  let g := IsOpenImmersion.lift U.ι (Y.fromSpecStalk y) hr
  have hg : g ≫ U.ι = Y.fromSpecStalk y := IsOpenImmersion.lift_fac _ _ _
  let : IsIso (pullback.fst U.ι f) := (OpenPullbackIsomorphismTransport.isIso_pullback_fst_open_iff f U).mpr inferInstance
  have h : IsIso (pullback.fst (g ≫ U.ι) f) :=
    (IteratedPullbackIsomorphism.isIso_pullback_fst_iterated_iff U.ι f g).mp inferInstance
  exact hg ▸ h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.StalkIsomorphismFromRestriction
