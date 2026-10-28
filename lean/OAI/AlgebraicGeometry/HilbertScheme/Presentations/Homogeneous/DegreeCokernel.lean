import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.DegreeMatrix
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Matrix.CokernelCoordinates

/-! # Degree Cokernel -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.DegreeCokernel.GradedHilbert

noncomputable section

/-! The explicit finite degree matrix has the actual homogeneous quotient as
its cokernel, before and after arbitrary coefficient specialization. -/

open _root_.MvPolynomial _root_.Module

universe u
variable {R : Type u} [CommRing R] {n : ℕ} {ι : Type u} [Fintype ι] [DecidableEq ι]

def homogeneousDegreeMatrixCokernelEquiv (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (N : ℕ)
    (hg : ∀ i, (g i).IsHomogeneous N) (d : ℕ) :
    ((CoordinateBasis.GradedHilbert.DegreeIndex.{u} n (d + N) → R) ⧸ (Matrix.toLin' (DegreeMatrix.GradedHilbert.homogeneousDegreeMatrix g N hg d)).range) ≃ₗ[R]
      Hilbert.Polynomial.GradedHilbert.DegreeQuotient (RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg).toIdeal (d + N) :=
  (Presentations.Matrix.CokernelCoordinates.matrixCokernelBasisEquiv (Pi.basis (fun _ : ι => CoordinateBasis.GradedHilbert.coordinateDegreeBasis R n d))
    (CoordinateBasis.GradedHilbert.coordinateDegreeBasis R n (d + N)) (RelationPresentation.GradedHilbert.homogeneousRelationPresentation g N hg d)).trans
      (RelationPresentation.GradedHilbert.homogeneousPresentationCokernelEquiv g N hg d)

def homogeneousSpecializedMatrixCokernelEquiv {S : Type u} [CommRing S] (φ : R →+* S)
    (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N) (d : ℕ) :
    ((CoordinateBasis.GradedHilbert.DegreeIndex.{u} n (d + N) → S) ⧸ (Matrix.toLin' ((DegreeMatrix.GradedHilbert.homogeneousDegreeMatrix g N hg d).map φ)).range) ≃ₗ[S]
      Hilbert.Polynomial.GradedHilbert.DegreeQuotient (RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal (fun i => MvPolynomial.map φ (g i)) N
        (fun i => (hg i).map φ)).toIdeal (d + N) := by
  rw [DegreeMatrix.GradedHilbert.homogeneousDegreeMatrix_map]
  exact homogeneousDegreeMatrixCokernelEquiv _ N _ d

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.DegreeCokernel.GradedHilbert
