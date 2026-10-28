import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Principal.AffineIsomorphismNeighborhood
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.PullbackIsomorphismTransport
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Affine Base Isomorphism Neighborhood -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.AffineBaseIsomorphismNeighborhood

noncomputable section

/-! A finite morphism over a noetherian affine base that is an
isomorphism over a local spectrum is so over a principal neighborhood. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsFinite f]

theorem exists_principalOpen_finite_morphism_isomorphism (p : PrimeSpectrum R)
    (hp : IsIso (pullback.fst
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)))) f)) :
    ∃ r ∉ p.asIdeal, IsIso (pullback.fst
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) f) := by
  let : IsAffine X := isAffine_of_isAffineHom f
  let A : Type u := Γ(X, ⊤)
  let e : Spec (.of A) ≅ X := X.isoSpec.symm
  let φ : R →+* A := (Spec.preimage (e.hom ≫ f)).hom
  let : Algebra R A := φ.toAlgebra
  have he : Spec.map (CommRingCat.ofHom (algebraMap R A)) = e.hom ≫ f :=
    Spec.map_preimage (e.hom ≫ f)
  have hf : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
    rw [he]
    infer_instance
  let : Module.Finite R A := (IsFinite.SpecMap_iff _).mp hf
  have hp' : IsIso (pullback.fst
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal))))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))) := by
    rw [he, PullbackIsomorphismTransport.isIso_pullback_fst_comp_right_iff]
    exact hp
  obtain ⟨r, hr, h⟩ := Principal.AffineIsomorphismNeighborhood.exists_principalOpen_affine_isomorphism (A := A) p hp'
  rw [he, PullbackIsomorphismTransport.isIso_pullback_fst_comp_right_iff] at h
  exact ⟨r, hr, h⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.AffineBaseIsomorphismNeighborhood
