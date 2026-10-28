import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.FamilyCoordinates
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.DegreeGeneratedBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SubmoduleFiberEquality

/-! # Family Generation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.FamilyGeneration.GradedHilbert

noncomputable section

/-! Uniform single-degree generation of high homogeneous relations for saturated flat projective families. -/

open _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (hSat : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal)
variable [Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))]
variable (P : Polynomial ℚ) (hP : ∀ p : PrimeSpectrum R,
  Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
    (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I)).toIdeal P)

include hSat hP in
theorem uniformFamily_degreeGenerated_relations (N : ℕ) (hN : FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
    (d : ℕ) (hd : N ≤ d) :
    Hilbert.Polynomial.GradedHilbert.degreeRelations (DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal I N).toIdeal d = Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d := by
  have hNB : RegularCoordinateFlag.GradedHilbert.regularCoordinateFlagBound.{u} n P ≤ N := (le_max_left _ _).trans hN
  have hNP : Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{u} n P ≤ N := (le_max_right _ _).trans hN
  let : Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) :=
    SaturatedCoordinates.GradedHilbert.uniform_saturated_coordinate_flat I hSat P hP d (hNB.trans hd)
  apply SubmoduleFiberEquality.submodule_eq_of_residue_baseChange R _ _ (Hilbert.Polynomial.GradedHilbert.degreeRelations_mono (DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal_le I N) d)
  intro p
  apply Submodule.map_injective_of_injective (Homogeneous.CoefficientBaseChange.GradedHilbert.homogeneousPieceBaseChangeEquiv
    (R := R) (S := p.asIdeal.ResidueField) (n := n) d).injective
  rw [RelationsBaseChangeMap.GradedHilbert.degreeRelations_baseChange_map, RelationsBaseChangeMap.GradedHilbert.degreeRelations_baseChange_map, DegreeGeneratedBaseChange.GradedHilbert.degreeGeneratedIdeal_baseChange]
  let J := Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I
  have hsatN : Hilbert.Polynomial.GradedHilbert.degreeRelations J.toIdeal N = Hilbert.Polynomial.GradedHilbert.degreeRelations (Projective.Saturation.GradedHilbert.projectiveSaturation J).toIdeal N :=
    (SaturationBaseChange.GradedHilbert.uniform_saturated_saturation_baseChange I hSat P hP p.asIdeal.ResidueField N hNB).symm
  have hsatd : Hilbert.Polynomial.GradedHilbert.degreeRelations (Projective.Saturation.GradedHilbert.projectiveSaturation J).toIdeal d = Hilbert.Polynomial.GradedHilbert.degreeRelations J.toIdeal d :=
    SaturationBaseChange.GradedHilbert.uniform_saturated_saturation_baseChange I hSat P hP p.asIdeal.ResidueField d (hNB.trans hd)
  change Hilbert.Polynomial.GradedHilbert.degreeRelations (DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal J N).toIdeal d = Hilbert.Polynomial.GradedHilbert.degreeRelations J.toIdeal d
  rw [DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal_eq_of_degreeRelations_eq J (Projective.Saturation.GradedHilbert.projectiveSaturation J) N hsatN]
  obtain ⟨B, hB, hBdeg⟩ := (Hilbert.Truncation.GradedHilbert.hilbertParameterDegree_spec n P p.asIdeal.ResidueField (Projective.Saturation.GradedHilbert.projectiveSaturation J)
    (Projective.Saturation.GradedHilbert.projectiveSaturation_isSaturated J) (hP p)).1
  rw [DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal_eventual_relations (Projective.Saturation.GradedHilbert.projectiveSaturation J) N B hB (fun b hb => by
    obtain ⟨_, e, he, hbe⟩ := hBdeg b hb
    exact ⟨e, he.trans hNP, hbe⟩) d hd]
  exact hsatd

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.FamilyGeneration.GradedHilbert
