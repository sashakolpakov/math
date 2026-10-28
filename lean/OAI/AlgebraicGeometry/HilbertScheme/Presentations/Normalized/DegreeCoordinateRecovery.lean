import OAI.AlgebraicGeometry.HilbertScheme.Presentations.DegreeCoordinateRelations
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.PolynomialKernel
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.DegreeGeneratedIdeal

/-! # Degree Coordinate Recovery -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.DegreeCoordinateRecovery.GradedHilbert

noncomputable section

/-! A normalized single-degree presentation recovers the actual monomial
coordinate quotient used by the Grassmannian classifying map. -/

universe u
variable {R : Type u} [CommRing R] {n N : ℕ}

theorem degreeGeneratedIdeal_degreeRelations_self (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    Hilbert.Polynomial.GradedHilbert.degreeRelations (DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal I N).toIdeal N = Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal N := by
  apply le_antisymm (Hilbert.Polynomial.GradedHilbert.degreeRelations_mono (DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal_le I N) N)
  intro f hf
  exact DegreeGeneratedIdeal.GradedHilbert.mem_degreeGeneratedIdeal I N f.val f.property hf

theorem degreeCoordinateRelations_degreeGenerated (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    DegreeCoordinateRelations.GradedHilbert.degreeCoordinateRelations (DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal I N) N = DegreeCoordinateRelations.GradedHilbert.degreeCoordinateRelations I N := by
  unfold DegreeCoordinateRelations.GradedHilbert.degreeCoordinateRelations
  rw [degreeGeneratedIdeal_degreeRelations_self]

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem degreeCoordinateRelations_normalized (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N)
    (Q : Matrix ι (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) R) (hQ : Matrices.Grassmannian.IsNormalized a Q) :
    DegreeCoordinateRelations.GradedHilbert.degreeCoordinateRelations (PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q) N = (Matrix.toLin' Q).ker := by
  rw [DegreeCoordinateRelations.GradedHilbert.degreeCoordinateRelations, PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal_degreeRelations, ← Submodule.map_comp]
  let e := (Homogeneous.CoordinateBasis.GradedHilbert.coordinateDegreeBasis R n N).equivFun
  have he : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id :=
    LinearMap.ext (fun x => e.apply_symm_apply x)
  rw [he, Submodule.map_id]
  exact hQ

theorem normalizedGrassmannian_eq_of_generatedIdeal (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (H : Module.Grassmannian R (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N → R) (Fintype.card ι))
    (hH : H.toSubmodule = DegreeCoordinateRelations.GradedHilbert.degreeCoordinateRelations I N)
    (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) (Q : Matrix ι (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) R) (hQ : Matrices.Grassmannian.IsNormalized a Q)
    (hI : PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q = DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal I N) : Quotients.Grassmannian.normalizedGrassmannian a Q hQ = H := by
  apply Module.Grassmannian.ext
  change (Matrix.toLin' Q).ker = H.toSubmodule
  have he := congrArg (fun J : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n) => DegreeCoordinateRelations.GradedHilbert.degreeCoordinateRelations J N) hI
  rw [degreeCoordinateRelations_normalized a Q hQ, degreeCoordinateRelations_degreeGenerated] at he
  exact he.trans hH.symm

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.DegreeCoordinateRecovery.GradedHilbert
