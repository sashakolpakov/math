import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Algebra.Ring.Subring.Basic
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantBasisOf
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantPolynomialOf
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantLocalizationIs
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.DeterminantCoverEq
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LocalBasisAnd
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.FlatInvariants
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantTensorExists

/-! # Affine Ring -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineRing.Construction.Affine

/-!
# The affine candidate for the FiniteDescent quotient

The candidate is the spectrum of the actual equalizer ring of invariant
functions. Its affine universal property is proved here. The finite-flat
effectiveness argument will show that it is also the fppf quotient.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {A B : Type u} [CommRing A] [CommRing B]

/-- The ring of functions invariant under a pair of affine relation maps. -/
abbrev invariants (s t : A →+* B) : Subring A := s.eqLocus t

/-- The affine quotient candidate, with its actual invariant coordinate ring. -/
noncomputable abbrev quotient (s t : A →+* B) : Scheme.{u} :=
  Spec (.of (invariants s t))

/-- Inclusion of invariant functions induces the affine candidate map. -/
noncomputable def projection (s t : A →+* B) : Spec (.of A) ⟶ quotient s t :=
  Spec.map (CommRingCat.ofHom (invariants s t).subtype)

/-- The affine candidate identifies the two relation maps. -/
theorem projection_condition (s t : A →+* B) :
    Spec.map (CommRingCat.ofHom s) ≫ projection s t =
      Spec.map (CommRingCat.ofHom t) ≫ projection s t := by
  unfold projection
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a
  exact a.property

/-- An invariant ring homomorphism factors uniquely through the invariant ring. -/
theorem invariant_ring_universal_property
    (s t : A →+* B) {R : Type u} [CommRing R]
    (f : R →+* A) (hf : s.comp f = t.comp f) :
    ∃! g : R →+* invariants s t, (invariants s t).subtype.comp g = f := by
  let g : R →+* invariants s t := f.codRestrict (invariants s t)
    (fun r => congrArg (fun e : R →+* B => e r) hf)
  refine ⟨g, rfl, ?_⟩
  intro g' hg'
  ext r
  exact congrArg (fun e : R →+* A => e r) hg'

/-- The spectrum of the invariant ring is the coequalizer against affine targets. -/
theorem quotient_universal_property_spec
    (s t : A →+* B) (R : CommRingCat.{u})
    (f : Spec (.of A) ⟶ Spec R)
    (hf : Spec.map (CommRingCat.ofHom s) ≫ f =
      Spec.map (CommRingCat.ofHom t) ≫ f) :
    ∃! g : quotient s t ⟶ Spec R, projection s t ≫ g = f := by
  obtain ⟨f₀, rfl⟩ := Spec.map_surjective f
  rw [← Spec.map_comp, ← Spec.map_comp] at hf
  have hf₀ : s.comp f₀.hom = t.comp f₀.hom :=
    congrArg (fun h => h.hom) (Spec.map_injective hf)
  obtain ⟨g, hg, hu⟩ := invariant_ring_universal_property s t f₀.hom hf₀
  refine ⟨Spec.map (CommRingCat.ofHom g), ?_, ?_⟩
  · change projection s t ≫ Spec.map (CommRingCat.ofHom g) = Spec.map f₀
    unfold projection
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact congrArg (fun e : R →+* A => e r) hg
  · intro g' hg'
    obtain ⟨g₀, rfl⟩ := Spec.map_surjective g'
    unfold projection at hg'
    rw [← Spec.map_comp] at hg'
    have hg₀ : (invariants s t).subtype.comp g₀.hom = f₀.hom :=
      congrArg (fun h => h.hom) (Spec.map_injective hg')
    apply congrArg Spec.map
    ext r
    exact congrArg (fun e : R →+* invariants s t => (e r : A)) (hu g₀.hom hg₀)

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineRing.Construction.Affine
