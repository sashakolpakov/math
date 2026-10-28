import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.SectionCoefficientIdeal
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.FamilyCoordinateBound

/-! # Equation Coefficient Ideal -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.EquationCoefficientIdeal.GradedHilbert

noncomputable section

/-! For a flat projective family over a noetherian coefficient ring,
sufficiently high homogeneous equations vanish on an arbitrary base change
exactly when its coefficient map kills their explicit coefficient ideal. -/

open _root_.AlgebraicGeometry TensorProduct

universe u v
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) [Flat (Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))]
variable (d : ℕ) (hd : FamilyCoordinateBound.GradedHilbert.projectiveFamilyCoordinateBound I ≤ d)

include hd in
theorem projectiveFamilyCoordinateBound_projective : Module.Projective R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) := by
  let : Module.Projective R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := R) I).toIdeal d) :=
    (FamilyCoordinateBound.GradedHilbert.projectiveFamilyCoordinateBound_spec I R d hd).1
  exact Module.Projective.of_equiv ((Graded.BaseChange.GradedHilbert.degreeQuotientBaseChangeEquiv (S := R) I d).symm.trans
    (TensorProduct.lid R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d)))

variable {ι : Type v} (g : ι → Hilbert.Polynomial.GradedHilbert.grading R n d)
variable (A : Type u) [CommRing A] [Algebra R A]

include hd in
theorem projectiveEquationCoefficientIdeal_le_ker_iff :
    Homogeneous.SectionCoefficientIdeal.GradedHilbert.homogeneousSectionCoefficientIdeal I d g ≤ RingHom.ker (algebraMap R A) ↔
      ∀ i, MvPolynomial.map (algebraMap R A) (g i).val ∈
        (Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I)).toIdeal := by
  let : Module.Projective R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) :=
    projectiveFamilyCoordinateBound_projective I d hd
  rw [Homogeneous.SectionCoefficientIdeal.GradedHilbert.homogeneousSectionCoefficientIdeal_le_ker_iff]
  apply forall_congr'
  intro i
  let f : Hilbert.Polynomial.GradedHilbert.grading A n d := ⟨MvPolynomial.map (algebraMap R A) (g i).val,
    (g i).property.map (algebraMap R A)⟩
  change f ∈ Hilbert.Polynomial.GradedHilbert.degreeRelations (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I).toIdeal d ↔
    f ∈ Hilbert.Polynomial.GradedHilbert.degreeRelations (Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I)).toIdeal d
  rw [(FamilyCoordinateBound.GradedHilbert.projectiveFamilyCoordinateBound_spec I A d hd).2]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.EquationCoefficientIdeal.GradedHilbert
