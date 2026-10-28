import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.GeneratorsBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.DegreeCokernel

/-! # Degree Matrices -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.DegreeMatrices

noncomputable section

/-! Finite coefficient matrices present the actual generated degree quotients on normalized Grassmann charts. -/

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.DegreeCokernel.GradedHilbert

universe u

variable {R : Type u} [CommRing R] {n N : ℕ} {ι : Type u} [Fintype ι] [DecidableEq ι]
variable (a : ι → ULift.{u} (Homogeneous.Coordinates.HomogeneousMonomials (Fin (n + 1)) N))
variable (Q : Matrix ι (ULift.{u} (Homogeneous.Coordinates.HomogeneousMonomials (Fin (n + 1)) N)) R)

def normalizedHomogeneousDegreeMatrix (d : ℕ) :
    Matrix (HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n (d + N))
      (HilbertScheme.Presentations.Homogeneous.DegreeMatrix.GradedHilbert.DegreeRelationIndex (ULift.{u} (Homogeneous.Coordinates.HomogeneousMonomials (Fin (n + 1)) N)) n d) R :=
  HilbertScheme.Presentations.Homogeneous.DegreeMatrix.GradedHilbert.homogeneousDegreeMatrix (fun j => (HomogeneousGenerators.normalizedHomogeneousGenerator a Q j).val) N
    (fun j => (HomogeneousGenerators.normalizedHomogeneousGenerator a Q j).property) d

def normalizedHomogeneousDegreeMatrixCokernelEquiv (hQ : HilbertScheme.Presentations.Normalized.Matrices.Grassmannian.IsNormalized a Q) (d : ℕ) :
    ((HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n (d + N) → R) ⧸ (Matrix.toLin' (normalizedHomogeneousDegreeMatrix a Q d)).range) ≃ₗ[R]
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R (d + N) ⧸
        Single.DegreeRelationExtension.singleDegreePiece N (HomogeneousGenerators.normalizedHomogeneousRelations Q) (d + N)) :=
  (HilbertScheme.Presentations.Homogeneous.DegreeCokernel.GradedHilbert.homogeneousDegreeMatrixCokernelEquiv (fun j => (HomogeneousGenerators.normalizedHomogeneousGenerator a Q j).val) N
    (fun j => (HomogeneousGenerators.normalizedHomogeneousGenerator a Q j).property) d).trans
      (Submodule.quotEquivOfEq _ _ (HomogeneousGenerators.normalizedHomogeneousIdeal_degree a Q hQ (d + N)))

omit [DecidableEq ι] in
theorem normalizedHomogeneousDegreeMatrix_map {A : Type u} [CommRing A] (φ : R →+* A) (d : ℕ) :
    (normalizedHomogeneousDegreeMatrix a Q d).map φ = normalizedHomogeneousDegreeMatrix a (Q.map φ) d := by
  have h := HilbertScheme.Presentations.Homogeneous.DegreeMatrix.GradedHilbert.homogeneousDegreeMatrix_map φ (fun j => (HomogeneousGenerators.normalizedHomogeneousGenerator a Q j).val)
    N (fun j => (HomogeneousGenerators.normalizedHomogeneousGenerator a Q j).property) d
  refine h.trans ?_
  change HilbertScheme.Presentations.Homogeneous.DegreeMatrix.GradedHilbert.homogeneousDegreeMatrix _ N _ d = HilbertScheme.Presentations.Homogeneous.DegreeMatrix.GradedHilbert.homogeneousDegreeMatrix _ N _ d
  congr 1
  funext j
  exact GeneratorsBaseChange.normalizedHomogeneousGenerator_map φ a Q j

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.DegreeMatrices
