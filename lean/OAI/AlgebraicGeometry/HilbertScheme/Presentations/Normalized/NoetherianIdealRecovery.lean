import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.PolynomialIdealRingMap
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SingleDegreeIdealReconstruction
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.FamilyGeneration

/-! # Noetherian Ideal Recovery -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.NoetherianIdealRecovery.GradedHilbert

noncomputable section

/-! Normalized degree-N equations over noetherian rings are recovered from
their flat saturated family, with scheme-theoretic equality over nonreduced bases. -/

open _root_.AlgebraicGeometry

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n N : ℕ}
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem normalizedNoetherianIdeal_eq_degreeGenerated
    (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) (Q : Matrix ι (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) R) (hQ : Matrices.Grassmannian.IsNormalized a Q)
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (hI : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal)
    [Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))]
    (hsat : Projective.Saturation.GradedHilbert.projectiveSaturation (PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q) = I)
    (P : Polynomial ℚ) (hP : ∀ p : PrimeSpectrum R, Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
      (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I)).toIdeal P)
    (hN : Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat) :
    PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q = DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal I N := by
  let J := PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q
  have hJI : J.toIdeal ≤ I.toIdeal := by
    rw [← hsat]
    exact Projective.Saturation.GradedHilbert.le_projectiveSaturation J
  let : Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal N) :=
    Uniform.SaturatedCoordinates.GradedHilbert.uniform_saturated_coordinate_flat I hI P hP N ((le_max_left _ _).trans hN)
  apply SingleDegreeIdealReconstruction.GradedHilbert.normalizedPolynomialIdeal_eq_degreeGenerated I N a Q
  apply SubmoduleFiberEquality.submodule_eq_of_residue_baseChange R _ _ (Hilbert.Polynomial.GradedHilbert.degreeRelations_mono hJI N)
  intro p
  apply Submodule.map_injective_of_injective (Homogeneous.CoefficientBaseChange.GradedHilbert.homogeneousPieceBaseChangeEquiv
    (R := R) (S := p.asIdeal.ResidueField) (n := n) N).injective
  rw [RelationsBaseChangeMap.GradedHilbert.degreeRelations_baseChange_map, RelationsBaseChangeMap.GradedHilbert.degreeRelations_baseChange_map]
  apply Hilbert.Polynomial.GradedHilbert.degreeRelations_eq_of_le_of_hilbertFunction_eq
    (Ideal.map_mono (f := MvPolynomial.map (algebraMap R p.asIdeal.ResidueField)) hJI) N
  have hIrank := Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree_rankAtStalk I hI P hP N hN p
  rw [Relative.Coordinates.GradedHilbert.degreeQuotient_rankAtStalk] at hIrank
  have hJrank : Hilbert.Polynomial.GradedHilbert.hilbertFunction (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) J).toIdeal N =
      Fintype.card ι := by
    change Hilbert.Polynomial.GradedHilbert.hilbertFunction (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) (PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q)).toIdeal N = _
    rw [PolynomialTransitions.GradedHilbert.normalizedPolynomialIdeal_baseChange]
    exact (PolynomialKernel.GradedHilbert.normalizedPolynomialDegreeQuotientEquiv a _ (hQ.map _)).finrank_eq.trans
      (Module.finrank_fintype_fun_eq_card p.asIdeal.ResidueField)
  exact hJrank.trans (hr.trans hIrank.symm)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.NoetherianIdealRecovery.GradedHilbert
