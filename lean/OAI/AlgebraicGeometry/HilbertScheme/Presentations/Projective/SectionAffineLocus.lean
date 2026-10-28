import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.SectionCoefficientIdeal
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.AffinePoints
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Section Affine Locus -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.SectionAffineLocus

noncomputable section

/-! The spectrum of a projective section's coefficient quotient is an
actual closed parameter scheme. Its points on every test scheme are
exactly the vanishing condition in the test scheme's global algebra. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry TensorProduct

universe u v
variable {R : Type u} [CommRing R]

theorem quotientAlgHom_nonempty_iff (J : Ideal R) (A : Type v) [CommRing A] [Algebra R A] :
    Nonempty ((R ⧸ J) →ₐ[R] A) ↔ J ≤ RingHom.ker (algebraMap R A) := by
  constructor
  · rintro ⟨f⟩ r hr
    change algebraMap R A r = 0
    exact (f.commutes r).symm.trans
      ((congrArg f (Ideal.Quotient.eq_zero_iff_mem.mpr hr)).trans (map_zero f))
  · intro h
    exact ⟨Ideal.Quotient.liftₐ J (Algebra.ofId R A) (fun r hr => h hr)⟩

theorem quotientAlgHom_unique (J : Ideal R) (A : Type v) [CommRing A] [Algebra R A]
    (f g : (R ⧸ J) →ₐ[R] A) : f = g := by
  apply AlgHom.ext
  intro q
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact (f.commutes r).trans (g.commutes r).symm

variable (R : CommRingCat.{u}) {M : Type u} [AddCommGroup M] [Module R M]
variable {ι : Type v} (x : ι → M)

def projectiveSectionAffineLocus : Over (Spec R) :=
  Relative.AffinePoints.relativeAffineScheme R (R ⧸ SectionCoefficientIdeal.projectiveSectionCoefficientIdeal x)

instance projectiveSectionAffineLocus_isClosedImmersion :
    IsClosedImmersion (projectiveSectionAffineLocus R x).hom := by
  change IsClosedImmersion (Spec.map (CommRingCat.ofHom
    (algebraMap R (R ⧸ SectionCoefficientIdeal.projectiveSectionCoefficientIdeal x))))
  exact IsClosedImmersion.spec_of_surjective _ (Ideal.Quotient.mk_surjective)

theorem projectiveSectionAffineLocus_points_iff [Module.Projective R M] (T : Over (Spec R)) :
    Nonempty (T ⟶ projectiveSectionAffineLocus R x) ↔
      ∀ i, (1 : Relative.AffinePoints.relativeGlobalAlgebra R T) ⊗ₜ[R] x i = 0 := by
  have he : Nonempty (T ⟶ projectiveSectionAffineLocus R x) ↔
      Nonempty ((R ⧸ SectionCoefficientIdeal.projectiveSectionCoefficientIdeal x) →ₐ[R] Relative.AffinePoints.relativeGlobalAlgebra R T) :=
    ⟨fun ⟨f⟩ => ⟨Relative.AffinePoints.relativeAffinePointEquiv R _ T f⟩,
      fun ⟨f⟩ => ⟨(Relative.AffinePoints.relativeAffinePointEquiv R _ T).symm f⟩⟩
  exact he.trans ((quotientAlgHom_nonempty_iff _ _).trans
    (SectionCoefficientIdeal.projectiveSectionCoefficientIdeal_le_ker_iff (Relative.AffinePoints.relativeGlobalAlgebra R T) x))

theorem projectiveSectionAffineLocus_unique (T : Over (Spec R))
    (f g : T ⟶ projectiveSectionAffineLocus R x) : f = g := by
  apply (Relative.AffinePoints.relativeAffinePointEquiv R _ T).injective
  exact quotientAlgHom_unique _ _ _ _

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.SectionAffineLocus
