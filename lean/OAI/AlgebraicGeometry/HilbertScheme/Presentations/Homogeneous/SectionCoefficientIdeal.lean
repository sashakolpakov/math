import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.SectionCoefficientIdeal
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.BaseChange

/-! # Section Coefficient Ideal -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.SectionCoefficientIdeal.GradedHilbert

noncomputable section

/-! Coefficient ideals detect vanishing of homogeneous equations in
projective degree quotients after arbitrary coefficient-ring extension. -/

open TensorProduct _root_.MvPolynomial

universe u v w
variable {R : Type u} [CommRing R] {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (d : ℕ)
variable (A : Type v) [CommRing A] [Algebra R A]

theorem degreeQuotient_baseChange_section_zero_iff (f : Hilbert.Polynomial.GradedHilbert.grading R n d) :
    (1 : A) ⊗ₜ[R] (Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d).mkQ f = 0 ↔
      MvPolynomial.map (algebraMap R A) f.val ∈ (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I).toIdeal := by
  let e := Graded.BaseChange.GradedHilbert.degreeQuotientBaseChangeEquiv (S := A) I d
  have he := Graded.BaseChange.GradedHilbert.degreeQuotientBaseChangeEquiv_tmul (S := A) I d 1 f
  constructor
  · intro h
    have hz := congrArg e h
    rw [map_zero] at hz
    rw [show e ((1 : A) ⊗ₜ[R] (Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d).mkQ f) = _ from he] at hz
    have hm := (Submodule.Quotient.mk_eq_zero (Hilbert.Polynomial.GradedHilbert.degreeRelations
      (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I).toIdeal d)).mp hz
    change (1 : A) • MvPolynomial.map (algebraMap R A) f.val ∈
      (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I).toIdeal at hm
    simpa only [one_smul] using hm
  · intro h
    apply e.injective
    rw [map_zero]
    rw [show e ((1 : A) ⊗ₜ[R] (Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d).mkQ f) = _ from he]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    change (1 : A) • MvPolynomial.map (algebraMap R A) f.val ∈
      (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I).toIdeal
    simpa only [one_smul] using h

variable {ι : Type w} (g : ι → Hilbert.Polynomial.GradedHilbert.grading R n d)

def homogeneousSectionCoefficientIdeal : Ideal R :=
  Presentations.Projective.SectionCoefficientIdeal.projectiveSectionCoefficientIdeal (fun i => (Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d).mkQ (g i))

theorem homogeneousSectionCoefficientIdeal_le_ker_iff [Module.Projective R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d)] :
    homogeneousSectionCoefficientIdeal I d g ≤ RingHom.ker (algebraMap R A) ↔
      ∀ i, MvPolynomial.map (algebraMap R A) (g i).val ∈
        (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I).toIdeal := by
  rw [homogeneousSectionCoefficientIdeal, Presentations.Projective.SectionCoefficientIdeal.projectiveSectionCoefficientIdeal_le_ker_iff]
  exact forall_congr' (fun i => degreeQuotient_baseChange_section_zero_iff I d A (g i))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.SectionCoefficientIdeal.GradedHilbert
