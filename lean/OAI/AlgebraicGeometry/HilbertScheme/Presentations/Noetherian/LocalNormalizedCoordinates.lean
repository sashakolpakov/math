import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.LocalFunction
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.DegreeIdealPresentation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.FamilyReconstruction

/-! # Local Normalized Coordinates -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.LocalNormalizedCoordinates.GradedHilbert

noncomputable section

/-! Uniform normalized Hilbert coordinates for saturated flat projective
families over local noetherian rings, including nonreduced rings. -/

open _root_.AlgebraicGeometry

universe u
variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (hI : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal)
variable [Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))]
variable (P : Polynomial ℚ) (hP : ∀ p : PrimeSpectrum R, Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
  (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I)).toIdeal P)
include hI hP

theorem exists_noetherian_local_normalized_hilbert_coordinates (N : ℕ)
    (hN : Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat) :
    ∃ (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) (Q : Matrix ι (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) R),
      Normalized.Matrices.Grassmannian.IsNormalized a Q ∧ Function.Injective a ∧
      Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q = DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal I N ∧
      Projective.Saturation.GradedHilbert.projectiveSaturation (Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q) = I ∧
      ∀ d ≥ N, Module.Free R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q).toIdeal d) ∧
        (Hilbert.Polynomial.GradedHilbert.hilbertFunction (Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q).toIdeal d : ℚ) = P.eval (d : ℚ) := by
  let H : Module.Grassmannian R (Hilbert.Polynomial.GradedHilbert.grading R n N) (Fintype.card ι) := {
    toSubmodule := Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal N
    finite_quotient := inferInstance
    projective_quotient := Uniform.SaturatedCoordinates.GradedHilbert.uniform_saturated_coordinate_projective I hI P hP N ((le_max_left _ _).trans hN)
    rankAtStalk_eq := fun p => (Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree_rankAtStalk I hI P hP N hN p).trans hr.symm }
  obtain ⟨a, Q, hQ, ha, he⟩ := Normalized.DegreeIdealPresentation.GradedHilbert.exists_normalized_degreeIdeal_presentation I H rfl
  refine ⟨a, Q, hQ, ha, he, ?_, ?_⟩
  · rw [he]
    exact Uniform.FamilyReconstruction.GradedHilbert.uniformFamily_reconstruction I hI P hP N hN
  · intro d hd
    have hrel : Hilbert.Polynomial.GradedHilbert.degreeRelations (Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q).toIdeal d = Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d := by
      rw [he]
      exact Uniform.FamilyGeneration.GradedHilbert.uniformFamily_degreeGenerated_relations I hI P hP N hN d hd
    let : Module.Free R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) := LocalFunction.GradedHilbert.uniformLocal_degreeQuotient_free I hI P hP d (hN.trans hd)
    refine ⟨Module.Free.of_equiv (Submodule.quotEquivOfEq _ _ hrel.symm), ?_⟩
    have hdim : Hilbert.Polynomial.GradedHilbert.hilbertFunction (Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q).toIdeal d = Hilbert.Polynomial.GradedHilbert.hilbertFunction I.toIdeal d :=
      (Submodule.quotEquivOfEq _ _ hrel).finrank_eq
    rw [hdim]
    exact LocalFunction.GradedHilbert.uniformLocal_hilbertFunction I hI P hP d (hN.trans hd)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.LocalNormalizedCoordinates.GradedHilbert
