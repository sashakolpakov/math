import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.BaseChangeBound
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.FlatBaseChange

/-! # Family Coordinate Bound -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.FamilyCoordinateBound.GradedHilbert

noncomputable section

/-! Constructed degree bounds for projective-family coordinates, valid over arbitrary test algebras. -/

open _root_.AlgebraicGeometry TensorProduct

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) [Flat (Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))]

theorem exists_projectiveFamilyCoordinateBound :
    ∃ N : ℕ, ∀ (S : Type u) [CommRing S] [Algebra R S], ∀ d ≥ N,
      Module.Projective S (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I).toIdeal d) ∧
      Hilbert.Polynomial.GradedHilbert.degreeRelations (Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I)).toIdeal d =
        Hilbert.Polynomial.GradedHilbert.degreeRelations (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I).toIdeal d := by
  obtain ⟨N, hN⟩ := Coordinate.FlatBaseChange.GradedHilbert.projectiveQuotient_eventual_projective_all_baseChanges I
  obtain ⟨B, hB⟩ := Saturation.BaseChangeBound.GradedHilbert.projectiveQuotient_uniform_saturation_baseChange I
  exact ⟨max N B, fun S _ _ d hd =>
    ⟨hN S d ((le_max_left _ _).trans hd), hB S d ((le_max_right _ _).trans hd)⟩⟩

def projectiveFamilyCoordinateBound : ℕ := (exists_projectiveFamilyCoordinateBound I).choose

theorem projectiveFamilyCoordinateBound_spec
    (S : Type u) [CommRing S] [Algebra R S] (d : ℕ) (hd : projectiveFamilyCoordinateBound I ≤ d) :
    Module.Projective S (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I).toIdeal d) ∧
      Hilbert.Polynomial.GradedHilbert.degreeRelations (Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I)).toIdeal d =
        Hilbert.Polynomial.GradedHilbert.degreeRelations (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I).toIdeal d :=
  (exists_projectiveFamilyCoordinateBound I).choose_spec S d hd

def saturatedDegreeQuotientBaseChangeEquiv
    (S : Type u) [CommRing S] [Algebra R S] (d : ℕ) (hd : projectiveFamilyCoordinateBound I ≤ d) :
    S ⊗[R] Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d ≃ₗ[S]
      Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I)).toIdeal d :=
  (Graded.BaseChange.GradedHilbert.degreeQuotientBaseChangeEquiv I d).trans
    (Submodule.quotEquivOfEq _ _ (projectiveFamilyCoordinateBound_spec I S d hd).2.symm)

theorem saturatedDegreeQuotient_projective_baseChange
    (S : Type u) [CommRing S] [Algebra R S] (d : ℕ) (hd : projectiveFamilyCoordinateBound I ≤ d) :
    Module.Projective S
      (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I)).toIdeal d) := by
  let : Module.Projective S (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I).toIdeal d) :=
    (projectiveFamilyCoordinateBound_spec I S d hd).1
  exact Module.Projective.of_equiv
    (Submodule.quotEquivOfEq _ _ (projectiveFamilyCoordinateBound_spec I S d hd).2.symm)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.FamilyCoordinateBound.GradedHilbert
