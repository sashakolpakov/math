import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.AffineBaseIsomorphismNeighborhood
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.OpenPullbackIsomorphismTransport
import Mathlib.AlgebraicGeometry.Stalk

/-! # Affine Stalk Isomorphism Neighborhood -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.AffineStalkIsomorphismNeighborhood

noncomputable section

/-! A finite morphism over a noetherian affine scheme that becomes an
isomorphism over a structure-sheaf stalk is an isomorphism on an actual open neighborhood. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsFinite f]

theorem exists_open_finite_affine_isomorphism_of_stalk (p : PrimeSpectrum R)
    (hp : IsIso (pullback.fst ((Spec (.of R)).fromSpecStalk p) f)) :
    ∃ U : (Spec (.of R)).Opens, p ∈ U ∧ IsIso (f ∣_ U) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)))
  let e := Spec.map (Spec.stalkIso (.of R) p).inv
  have he : e ≫ g = (Spec (.of R)).fromSpecStalk p := by
    change Spec.map (Spec.stalkIso (.of R) p).inv ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal))) = _
    rw [← Spec.map_comp]
    exact (congrArg (fun a : CommRingCat.of R ⟶ (Spec (.of R)).presheaf.stalk p => Spec.map a)
      (Spec.algebraMap_stalkIso_inv (R := .of R) (x := p))).trans (Spec.fromSpecStalk_eq (.of R) p).symm
  have hg : IsIso (pullback.fst g f) :=
    (OpenPullbackIsomorphismTransport.isIso_pullback_fst_comp_left_iff g f e).mp (he.symm ▸ hp)
  obtain ⟨r, hr, h⟩ := AffineBaseIsomorphismNeighborhood.exists_principalOpen_finite_morphism_isomorphism f p hg
  let j := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))
  refine ⟨j.opensRange, ?_, (OpenPullbackIsomorphismTransport.isIso_pullback_fst_openImmersion_iff f j).mp h⟩
  have ho : j.opensRange = PrimeSpectrum.basicOpen r :=
    Scheme.Hom.opensRange_localizationAway (R := .of R) r
  exact Eq.mpr (congrArg (fun U : (Spec (.of R)).Opens => p ∈ U) ho) hr

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.AffineStalkIsomorphismNeighborhood
