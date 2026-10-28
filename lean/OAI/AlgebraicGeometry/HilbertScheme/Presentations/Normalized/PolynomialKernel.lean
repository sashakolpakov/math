import OAI.AlgebraicGeometry.HilbertScheme.Presentations.GeneratedDegreeRelations
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.PolynomialGenerators
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.Quotients

/-! # Polynomial Kernel -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.PolynomialKernel.GradedHilbert

noncomputable section

/-! The degree-N relations of the universal polynomial ideal recover the
actual kernel of the normalized quotient matrix. -/

open _root_.MvPolynomial _root_.Module

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.Quotients.Grassmannian
universe u
variable {R : Type u} [CommRing R] {n N : ℕ}
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

def normalizedPolynomialIdeal (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N)
    (Q : Matrix ι (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) R) : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n) :=
  Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal (PolynomialGenerators.GradedHilbert.normalizedPolynomialGenerator a Q) N
    (PolynomialGenerators.GradedHilbert.normalizedPolynomialGenerator_homogeneous a Q)

theorem normalizedPolynomialIdeal_degreeRelations (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N)
    (Q : Matrix ι (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) R) (hQ : Matrices.Grassmannian.IsNormalized a Q) :
    Hilbert.Polynomial.GradedHilbert.degreeRelations (normalizedPolynomialIdeal a Q).toIdeal N =
      (Matrix.toLin' Q).ker.map (Homogeneous.CoordinateBasis.GradedHilbert.coordinateDegreeBasis R n N).equivFun.symm.toLinearMap := by
  rw [normalizedPolynomialIdeal, GeneratedDegreeRelations.GradedHilbert.homogeneousGenerators_degreeRelations_span,
    ← KernelBaseChange.Grassmannian.normalizedKernelMatrix_range a Q hQ, Matrix.range_toLin', Submodule.map_span]
  congr 1
  ext f
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨(KernelBaseChange.Grassmannian.normalizedKernelMatrix a Q).col j, ⟨j, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
    exact ⟨j, rfl⟩

def normalizedPolynomialDegreeQuotientEquiv (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N)
    (Q : Matrix ι (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) R) (hQ : Matrices.Grassmannian.IsNormalized a Q) :
    Hilbert.Polynomial.GradedHilbert.DegreeQuotient (normalizedPolynomialIdeal a Q).toIdeal N ≃ₗ[R] (ι → R) :=
  (Submodule.Quotient.equiv _ _ (Homogeneous.CoordinateBasis.GradedHilbert.coordinateDegreeBasis R n N).equivFun.symm
    (normalizedPolynomialIdeal_degreeRelations a Q hQ).symm).symm.trans
      (Quotients.Grassmannian.normalizedQuotientEquiv a Q hQ)

theorem normalizedPolynomialIdeal_injective (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) :
    Function.Injective (fun Q : {Q : Matrix ι (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) R // Matrices.Grassmannian.IsNormalized a Q} =>
      normalizedPolynomialIdeal a Q.val) := by
  intro Q K h
  apply Subtype.ext
  apply Quotients.Grassmannian.normalizedMatrix_eq_of_kernel_eq a Q.val K.val Q.property K.property
  have hd := congrArg (fun I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n) => Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal N) h
  rw [normalizedPolynomialIdeal_degreeRelations a Q.val Q.property,
    normalizedPolynomialIdeal_degreeRelations a K.val K.property] at hd
  exact Submodule.map_injective_of_injective
    (Homogeneous.CoordinateBasis.GradedHilbert.coordinateDegreeBasis R n N).equivFun.symm.injective hd

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.PolynomialKernel.GradedHilbert
