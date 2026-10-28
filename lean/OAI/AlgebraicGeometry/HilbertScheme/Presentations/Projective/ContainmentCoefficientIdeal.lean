import OAI.AlgebraicGeometry.HilbertScheme.Presentations.HighDegreeProjectiveEquations
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.SaturationOrder
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.SaturationBaseChangeEquality
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.EquationCoefficientIdeal
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.GeneratorsBaseChange

/-! # Containment Coefficient Ideal -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ContainmentCoefficientIdeal.GradedHilbert

noncomputable section

/-! Containment in any fixed projective closed subscheme is cut out
by an actual coefficient ideal for a flat projective family over a
noetherian ring. The criterion holds over every coefficient algebra. -/

open _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
variable (I K : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) [Flat (Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))]

theorem exists_projectiveContainmentCoefficientIdeal :
    ∃ J : Ideal R, ∀ (A : Type u) [CommRing A] [Algebra R A],
      J ≤ RingHom.ker (algebraMap R A) ↔
        Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) K) ≤
          Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I) := by
  obtain ⟨m, d, g, hg, hd, hs⟩ := HighDegreeProjectiveEquations.GradedHilbert.finite_single_degree_projective_equations_above K
    K.toIdeal.fg_of_isNoetherianRing (FamilyCoordinateBound.GradedHilbert.projectiveFamilyCoordinateBound I)
  let v : Fin m → Hilbert.Polynomial.GradedHilbert.grading R n d := fun i => ⟨g i, hg i⟩
  refine ⟨Homogeneous.SectionCoefficientIdeal.GradedHilbert.homogeneousSectionCoefficientIdeal I d v, ?_⟩
  intro A _ _
  let L := Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g d hg
  let H := Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I)
  have hgen : Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) L ≤ H ↔
      ∀ i, MvPolynomial.map (algebraMap R A) (g i) ∈ H.toIdeal := by
    rw [show Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) L =
      Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal (Finite.SyzygyLifting.GradedHilbert.mapRelationVector (algebraMap R A) g) d
        (fun i => (hg i).map (algebraMap R A)) from Homogeneous.GeneratorsBaseChange.GradedHilbert.homogeneousGeneratorsIdeal_baseChange g d hg]
    change Ideal.span (Set.range (Finite.SyzygyLifting.GradedHilbert.mapRelationVector (algebraMap R A) g)) ≤ H.toIdeal ↔ _
    rw [Ideal.span_le]
    constructor
    · intro h i
      exact h ⟨i, rfl⟩
    · intro h f hf
      obtain ⟨i, rfl⟩ := hf
      exact h i
  have he := SaturationBaseChangeEquality.GradedHilbert.projectiveSaturation_extended_eq_of_eq (A := A) L K hs
  exact (EquationCoefficientIdeal.GradedHilbert.projectiveEquationCoefficientIdeal_le_ker_iff I d hd v A).trans
    (hgen.symm.trans ((SaturationOrder.GradedHilbert.projectiveSaturation_le_iff (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) L) H
      (Saturation.GradedHilbert.projectiveSaturation_isSaturated _)).symm.trans
        (by rw [he])))

def projectiveContainmentCoefficientIdeal : Ideal R :=
  (exists_projectiveContainmentCoefficientIdeal I K).choose

theorem projectiveContainmentCoefficientIdeal_spec
    (A : Type u) [CommRing A] [Algebra R A] :
    projectiveContainmentCoefficientIdeal I K ≤ RingHom.ker (algebraMap R A) ↔
      Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) K) ≤
        Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I) :=
  (exists_projectiveContainmentCoefficientIdeal I K).choose_spec A

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ContainmentCoefficientIdeal.GradedHilbert
