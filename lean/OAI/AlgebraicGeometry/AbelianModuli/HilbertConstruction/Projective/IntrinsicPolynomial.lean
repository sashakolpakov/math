import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.TensorPowers
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.Polynomial
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.SectionPolynomial

/-! # Intrinsic Polynomial -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.IntrinsicPolynomial

noncomputable section

/-! The homogeneous coordinate Hilbert polynomial is the intrinsic section Hilbert polynomial of the actual degree-one twisting line bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading K n))

def projectiveTwistingPowerSectionsIso (d : ℕ) :
    (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))).obj
      ((ProjectiveTwisting.Bundle.projectiveTwistingBundle I 1).tensorPower d).sheaf ≃ₗ[K]
    (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))).obj
      (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf :=
  Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsIso (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)) (ProjectiveTwisting.TensorPowers.projectiveTwistingBundle_tensorPowerIso I d)

theorem projectiveTwistingBundle_intrinsicHilbertPolynomial_iff (P : Polynomial ℚ) :
    (ProjectiveTwisting.Bundle.projectiveTwistingBundle I 1).HasSectionHilbertPolynomial (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)) P ↔
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P := by
  rw [ProjectiveTwisting.Polynomial.projectiveTwistingSections_hilbertPolynomial_iff]
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, fun d hd => ?_⟩
    obtain ⟨hf, he⟩ := hB d hd
    have := hf
    exact ⟨Module.Finite.equiv (projectiveTwistingPowerSectionsIso I d),
      ((congrArg (fun a : ℕ => (a : ℚ)) (projectiveTwistingPowerSectionsIso I d).finrank_eq).symm.trans he.symm)⟩
  · rintro ⟨B, hB⟩
    refine ⟨B, fun d hd => ?_⟩
    obtain ⟨hf, he⟩ := hB d hd
    have := hf
    exact ⟨Module.Finite.equiv (projectiveTwistingPowerSectionsIso I d).symm,
      he.symm.trans (congrArg (fun a : ℕ => (a : ℚ)) (projectiveTwistingPowerSectionsIso I d).finrank_eq.symm)⟩

theorem projectiveTwistingBundle_intrinsicHilbertPolynomial_exists :
    ∃ P : Polynomial ℚ, (ProjectiveTwisting.Bundle.projectiveTwistingBundle I 1).HasSectionHilbertPolynomial
      (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)) P := by
  obtain ⟨P, hP⟩ := HilbertScheme.Presentations.Hilbert.Existence.GradedHilbert.exists_hilbertPolynomial I
  exact ⟨P, (projectiveTwistingBundle_intrinsicHilbertPolynomial_iff I P).mpr hP⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.IntrinsicPolynomial
