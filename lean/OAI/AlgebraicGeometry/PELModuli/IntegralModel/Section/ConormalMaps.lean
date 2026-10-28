import OAI.AlgebraicGeometry.Divisors.LineBundles.Section.ConormalFinite
import Mathlib.LinearAlgebra.Dual.Defs

/-! # Conormal Maps -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.ConormalMaps.SectionConormal

noncomputable section

/-! Smooth algebra sections have actual finite projective conormal
modules. Maps preserving the sections induce functorial conormal maps. -/

variable {R B C D : Type} [CommRing R] [CommRing B] [CommRing C] [CommRing D]
  [Algebra R B] [Algebra R C] [Algebra R D]

def module (e : B →ₐ[R] R) := (RingHom.ker e.toRingHom).Cotangent

instance (e : B →ₐ[R] R) : AddCommGroup (module e) :=
  inferInstanceAs (AddCommGroup (RingHom.ker e.toRingHom).Cotangent)

instance (e : B →ₐ[R] R) : Module R (module e) :=
  inferInstanceAs (Module R (RingHom.ker e.toRingHom).Cotangent)

theorem kernel_le_comap (e : B →ₐ[R] R) (q : C →ₐ[R] R)
    (f : B →ₐ[R] C) (hf : q.comp f = e) :
    RingHom.ker e.toRingHom ≤ (RingHom.ker q.toRingHom).comap f.toRingHom := by
  intro b hb
  change q (f b) = 0
  exact (AlgHom.congr_fun hf b).trans hb

def map (e : B →ₐ[R] R) (q : C →ₐ[R] R)
    (f : B →ₐ[R] C) (hf : q.comp f = e) : module e →ₗ[R] module q :=
  Ideal.mapCotangent _ _ f (kernel_le_comap e q f hf)

theorem map_toCotangent (e : B →ₐ[R] R) (q : C →ₐ[R] R)
    (f : B →ₐ[R] C) (hf : q.comp f = e) (b : RingHom.ker e.toRingHom) :
    map e q f hf (Ideal.toCotangent _ b) =
      Ideal.toCotangent _ ⟨f b, kernel_le_comap e q f hf b.property⟩ := rfl

theorem map_id (e : B →ₐ[R] R) : map e e (AlgHom.id R B) (AlgHom.comp_id e) = LinearMap.id := by
  apply LinearMap.ext
  intro v
  obtain ⟨b, rfl⟩ := Ideal.toCotangent_surjective (RingHom.ker e.toRingHom) v
  rfl

theorem map_comp (e : B →ₐ[R] R) (q : C →ₐ[R] R) (r : D →ₐ[R] R)
    (f : B →ₐ[R] C) (g : C →ₐ[R] D) (hf : q.comp f = e) (hg : r.comp g = q) :
    (map q r g hg).comp (map e q f hf) =
      map e r (g.comp f) (by rw [← AlgHom.comp_assoc, hg, hf]) := by
  apply LinearMap.ext
  intro v
  obtain ⟨b, rfl⟩ := Ideal.toCotangent_surjective (RingHom.ker e.toRingHom) v
  rfl

theorem finite_projective (e : B →ₐ[R] R) [Algebra.FormallySmooth R B]
    [Algebra.EssFiniteType R B] :
    Module.Finite R (module e) ∧ Module.Projective R (module e) := by
  let : Algebra B R := e.toRingHom.toAlgebra
  let : IsScalarTower R B R := IsScalarTower.of_algebraMap_eq fun r => (e.commutes r).symm
  exact ⟨Divisors.LineBundles.Section.ConormalFinite.BundleCycles.sectionConormal_finite R B,
    Divisors.LineBundles.Smooth.SectionCotangent.BundleCycles.smoothSectionCotangent_projective (A := R) (B := B)⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.ConormalMaps.SectionConormal
