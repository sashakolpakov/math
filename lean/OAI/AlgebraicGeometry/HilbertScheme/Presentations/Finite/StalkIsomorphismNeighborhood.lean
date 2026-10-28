import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.AffineStalkIsomorphismNeighborhood
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IteratedPullbackIsomorphism
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Stalk Isomorphism Neighborhood -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.StalkIsomorphismNeighborhood

noncomputable section

/-! On any locally noetherian target, a finite morphism that is an
isomorphism over a local spectrum is an isomorphism on an actual open neighborhood. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
variable (f : X ⟶ Y) [IsFinite f]

theorem exists_open_finite_isomorphism_of_stalk (y : Y)
    (hy : IsIso (pullback.fst (Y.fromSpecStalk y) f)) :
    ∃ U : Y.Opens, y ∈ U ∧ IsIso (f ∣_ U) := by
  let C := Y.affineOpenCover
  obtain ⟨i, a, ha⟩ := C.openCover.exists_eq y
  change C.I₀ at i
  change Spec (C.X i) at a
  change C.f i a = y at ha
  subst y
  let g := C.f i
  let : IsOpenImmersion g := C.map_prop i
  have hR : IsNoetherianRing (C.X i) := isLocallyNoetherian_Spec.mp
    (isLocallyNoetherian_of_isOpenImmersion g)
  let f' := pullback.fst g f
  have hp : IsIso (pullback.fst ((Spec (C.X i)).fromSpecStalk a) f') := by
    apply (IteratedPullbackIsomorphism.isIso_pullback_fst_iterated_iff g f _).mpr
    have he : Spec.map (g.stalkMap a) ≫ Y.fromSpecStalk (g a) =
        (Spec (C.X i)).fromSpecStalk a ≫ g := Scheme.SpecMap_stalkMap_fromSpecStalk g
    exact he ▸ (OpenPullbackIsomorphismTransport.isIso_pullback_fst_comp_left_iff (Y.fromSpecStalk (g a)) f
      (Spec.map (g.stalkMap a))).mpr hy
  obtain ⟨V, hV, hfV⟩ := @AffineStalkIsomorphismNeighborhood.exists_open_finite_affine_isomorphism_of_stalk (C.X i) _ hR
    (pullback g f) f' inferInstance a hp
  let j : V.toScheme ⟶ Y := V.ι ≫ g
  have hj : IsIso (pullback.fst j f) :=
    (IteratedPullbackIsomorphism.isIso_pullback_fst_iterated_iff g f V.ι).mp ((OpenPullbackIsomorphismTransport.isIso_pullback_fst_open_iff f' V).mpr hfV)
  exact ⟨j.opensRange, ⟨⟨a, hV⟩, rfl⟩, (OpenPullbackIsomorphismTransport.isIso_pullback_fst_openImmersion_iff f j).mp hj⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.StalkIsomorphismNeighborhood
