import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Flatness
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-! # Properness -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Properness.GradedHilbert

noncomputable section

/-!
The structure morphism of a polynomial homogeneous quotient is proper.
Its degree-zero algebra is a quotient of the coefficient ring, and its
whole coordinate algebra is finitely generated over that degree-zero part.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

theorem projectiveStructureMap_proper [Algebra.FiniteType R A]
    (hzero : Function.Surjective (algebraMap R (𝒜 0))) :
    IsProper (Flatness.GradedHilbert.projectiveStructureMap 𝒜) := by
  have : IsScalarTower R (𝒜 0) A :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := 𝒜 0) (A := A) (fun _ => rfl)
  have : Algebra.FiniteType (𝒜 0) A := Algebra.FiniteType.of_restrictScalars_finiteType R (𝒜 0) A
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 0)))) :=
    IsClosedImmersion.spec_of_surjective _ hzero
  change IsProper (Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 0))))
  infer_instance

variable {n : ℕ}

theorem quotientGrading_zero_algebraMap_surjective (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    Function.Surjective (algebraMap R (Graded.Quotient.GradedHilbert.quotientGrading I 0)) := by
  intro q
  obtain ⟨f, hf, hq⟩ := q.property
  have hfeq : f = C (f.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp
    ((totalDegree_zero_iff_isHomogeneous (Fin (n + 1))).mpr hf)
  refine ⟨f.coeff 0, Subtype.ext ?_⟩
  change Ideal.Quotient.mk I.toIdeal (C (f.coeff 0)) = q.val
  rw [← hfeq]
  exact hq

theorem projectiveQuotient_proper (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    IsProper (Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I)) :=
  projectiveStructureMap_proper (Graded.Quotient.GradedHilbert.quotientGrading I) (quotientGrading_zero_algebraMap_surjective I)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Properness.GradedHilbert
