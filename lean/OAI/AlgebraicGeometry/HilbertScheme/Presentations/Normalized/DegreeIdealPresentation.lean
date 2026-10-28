import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.LinearTransport
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.QuotientCover
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SingleDegreeIdealReconstruction

/-! # Degree Ideal Presentation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.DegreeIdealPresentation.GradedHilbert

noncomputable section

/-! A finite projective degree quotient over a local ring has a normalized
matrix whose polynomial ideal is exactly the ideal generated in that degree. -/

universe u
variable {R : Type u} [CommRing R] [IsLocalRing R] {n N : ℕ}
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem exists_normalized_degreeIdeal_presentation
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (H : Module.Grassmannian R (Hilbert.Polynomial.GradedHilbert.grading R n N) (Fintype.card ι))
    (hH : H.toSubmodule = Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal N) :
    ∃ (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) (Q : Matrix ι (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) R),
      Matrices.Grassmannian.IsNormalized a Q ∧ Function.Injective a ∧ PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q = DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal I N := by
  let e := (Homogeneous.CoordinateBasis.GradedHilbert.coordinateDegreeBasis R n N).equivFun
  let G := Presentations.Grassmannian.LinearTransport.grassmannianLinearTransport e H
  obtain ⟨a, Q, hQ, ha, he⟩ := QuotientCover.Grassmannian.normalizedGrassmannian_local_cover G
  refine ⟨a, Q, hQ, ha, SingleDegreeIdealReconstruction.GradedHilbert.normalizedPolynomialIdeal_eq_degreeGenerated I N a Q ?_⟩
  have hk := congrArg Module.Grassmannian.toSubmodule he
  change (Matrix.toLin' Q).ker = H.toSubmodule.map e.toLinearMap at hk
  rw [hH] at hk
  rw [PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal_degreeRelations a Q hQ, hk, ← Submodule.map_comp]
  have heid : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
    exact LinearMap.ext (fun x => e.symm_apply_apply x)
  rw [heid, Submodule.map_id]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.DegreeIdealPresentation.GradedHilbert
