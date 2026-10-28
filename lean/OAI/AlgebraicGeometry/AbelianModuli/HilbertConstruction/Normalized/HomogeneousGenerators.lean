import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.QuotientParameters
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quotient.ChartKernels
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Single.DegreeIdealRelations
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.KernelBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.RelationPresentation

/-! # Homogeneous Generators -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.HomogeneousGenerators

noncomputable section

/-! Explicit homogeneous generators for the relation kernel on a normalized Grassmann chart. -/

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.RelationPresentation.GradedHilbert

universe u

variable {R : Type u} [CommRing R] {n N : ℕ} {ι : Type u} [Fintype ι] [DecidableEq ι]
variable (a : ι → ULift.{u} (Homogeneous.Coordinates.HomogeneousMonomials (Fin (n + 1)) N))
variable (Q : Matrix ι (ULift.{u} (Homogeneous.Coordinates.HomogeneousMonomials (Fin (n + 1)) N)) R)

def normalizedHomogeneousGenerator (j : ULift.{u} (Homogeneous.Coordinates.HomogeneousMonomials (Fin (n + 1)) N)) :
    MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R N :=
  (Homogeneous.QuotientParameters.homogeneousLiftedCoordinates.{u, 0} (Fin (n + 1)) N R).symm
    (fun i => HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.normalizedKernelMatrix a Q i j)

def normalizedHomogeneousRelations : Submodule R (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R N) :=
  (Matrix.toLin' Q).ker.map
    (Homogeneous.QuotientParameters.homogeneousLiftedCoordinates.{u, 0} (Fin (n + 1)) N R).symm.toLinearMap

theorem normalizedHomogeneousGenerator_span (hQ : HilbertScheme.Presentations.Normalized.Matrices.Grassmannian.IsNormalized a Q) :
    Submodule.span R (Set.range (normalizedHomogeneousGenerator a Q)) = normalizedHomogeneousRelations Q := by
  let K := HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.normalizedKernelMatrix a Q
  have hc : Submodule.span R (Set.range (fun j => fun i => K i j)) = (Matrix.toLin' Q).ker := by
    rw [← HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.normalizedKernelMatrix_range a Q hQ]
    have h := Quotient.ChartKernels.linearMap_range_span_basis (Pi.basisFun R _) (Matrix.toLin' K)
    simp only [Pi.basisFun_apply, Matrix.toLin'_apply, Matrix.mulVec_single_one] at h
    exact h.symm
  change Submodule.span R (Set.range
    ((Homogeneous.QuotientParameters.homogeneousLiftedCoordinates.{u, 0} (Fin (n + 1)) N R).symm ∘ (fun j => fun i => K i j))) = _
  rw [Set.range_comp]
  exact (Submodule.map_span
    (Homogeneous.QuotientParameters.homogeneousLiftedCoordinates.{u, 0} (Fin (n + 1)) N R).symm.toLinearMap _).symm.trans
      (congrArg (fun L => L.map
        (Homogeneous.QuotientParameters.homogeneousLiftedCoordinates.{u, 0} (Fin (n + 1)) N R).symm.toLinearMap) hc)

def normalizedHomogeneousIdeal : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) :=
  HilbertScheme.Presentations.Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal (fun j => (normalizedHomogeneousGenerator a Q j).val) N
    (fun j => (normalizedHomogeneousGenerator a Q j).property)

theorem normalizedHomogeneousIdeal_eq (hQ : HilbertScheme.Presentations.Normalized.Matrices.Grassmannian.IsNormalized a Q) :
    normalizedHomogeneousIdeal a Q = (Single.DegreeRelationExtension.singleDegreeRelations N (normalizedHomogeneousRelations Q)).toHomogeneousIdeal := by
  apply HomogeneousIdeal.ext
  change Ideal.span (Set.range (fun j => (normalizedHomogeneousGenerator a Q j).val)) =
    (Single.DegreeRelationExtension.singleDegreeRelations N (normalizedHomogeneousRelations Q)).toIdeal
  rw [Single.DegreeRelationExtension.singleDegreeRelations_ideal, ← normalizedHomogeneousGenerator_span a Q hQ,
    Submodule.map_span, ← Set.range_comp]
  exact (Submodule.span_span_of_tower R (MvPolynomial (Fin (n + 1)) R) _).symm

theorem normalizedHomogeneousIdeal_degree (hQ : HilbertScheme.Presentations.Normalized.Matrices.Grassmannian.IsNormalized a Q) (d : ℕ) :
    Homogeneous.IdealIncidence.homogeneousDegreeRelations (normalizedHomogeneousIdeal a Q) d =
      Single.DegreeRelationExtension.singleDegreePiece N (normalizedHomogeneousRelations Q) d := by
  rw [normalizedHomogeneousIdeal_eq a Q hQ]
  exact (Single.DegreeRelationExtension.singleDegreeRelations N (normalizedHomogeneousRelations Q)).toHomogeneousIdeal_degree d

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.HomogeneousGenerators
