import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.CoordinateBasis
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.RelationPresentation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.StdBasis

/-! # Degree Matrix -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.DegreeMatrix.GradedHilbert

noncomputable section

/-! The finite coefficient matrix presenting each homogeneous quotient degree,
and its compatibility with arbitrary coefficient homomorphisms. -/

open _root_.MvPolynomial _root_.Module

universe u
variable {R : Type u} [CommRing R] {n : ℕ} {ι : Type u} [Fintype ι] [DecidableEq ι]

abbrev DegreeRelationIndex (ι : Type u) (n d : ℕ) := Σ _i : ι, CoordinateBasis.GradedHilbert.DegreeIndex.{u} n d

def homogeneousDegreeMatrix (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (N : ℕ)
    (hg : ∀ i, (g i).IsHomogeneous N) (d : ℕ) :
    Matrix (CoordinateBasis.GradedHilbert.DegreeIndex.{u} n (d + N)) (DegreeRelationIndex ι n d) R :=
  LinearMap.toMatrix (Pi.basis (fun _ : ι => CoordinateBasis.GradedHilbert.coordinateDegreeBasis R n d))
    (CoordinateBasis.GradedHilbert.coordinateDegreeBasis R n (d + N)) (RelationPresentation.GradedHilbert.homogeneousRelationPresentation g N hg d)

theorem homogeneousDegreeMatrix_apply (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (N : ℕ)
    (hg : ∀ i, (g i).IsHomogeneous N) (d : ℕ)
    (a : CoordinateBasis.GradedHilbert.DegreeIndex.{u} n (d + N)) (b : DegreeRelationIndex ι n d) :
    homogeneousDegreeMatrix g N hg d a b = (monomial b.2.down.val 1 * g b.1).coeff a.down.val := by
  classical
  rw [homogeneousDegreeMatrix, LinearMap.toMatrix_apply, CoordinateBasis.GradedHilbert.coordinateDegreeBasis_repr,
    Pi.basis_apply, RelationPresentation.GradedHilbert.homogeneousRelationPresentation_val]
  simp [SyzygiesFromPolynomialKernel.GradedHilbert.polynomialRelationMap, Pi.single_apply, apply_ite, ite_mul, CoordinateBasis.GradedHilbert.coordinateDegreeBasis_val]

theorem homogeneousDegreeMatrix_map {S : Type u} [CommRing S] (φ : R →+* S)
    (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N) (d : ℕ) :
    (homogeneousDegreeMatrix g N hg d).map φ =
      homogeneousDegreeMatrix (fun i => MvPolynomial.map φ (g i)) N (fun i => (hg i).map φ) d := by
  ext a b
  simp only [Matrix.map_apply, homogeneousDegreeMatrix_apply]
  rw [← MvPolynomial.coeff_map, map_mul, map_monomial, map_one]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.DegreeMatrix.GradedHilbert
