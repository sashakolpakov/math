import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.CoordinateBasis
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.KernelBaseChange

/-! # Polynomial Generators -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.PolynomialGenerators.GradedHilbert

noncomputable section

/-! Homogeneous polynomial generators extracted from the explicit kernel
projection of a normalized Grassmannian matrix. -/

open _root_.MvPolynomial _root_.Module

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian
universe u
variable {R : Type u} [CommRing R] {n N : ℕ}
variable {ι : Type u} [Fintype ι]

def normalizedPolynomialGenerator (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N)
    (Q : Matrix ι (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) R) (j : Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n :=
  ((Homogeneous.CoordinateBasis.GradedHilbert.coordinateDegreeBasis R n N).equivFun.symm ((KernelBaseChange.Grassmannian.normalizedKernelMatrix a Q).col j)).val

theorem normalizedPolynomialGenerator_homogeneous (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N)
    (Q : Matrix ι (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) R) (j : Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) :
    (normalizedPolynomialGenerator a Q j).IsHomogeneous N :=
  ((Homogeneous.CoordinateBasis.GradedHilbert.coordinateDegreeBasis R n N).equivFun.symm ((KernelBaseChange.Grassmannian.normalizedKernelMatrix a Q).col j)).property

theorem normalizedPolynomialGenerator_sum (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N)
    (Q : Matrix ι (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) R) (j : Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) :
    normalizedPolynomialGenerator a Q j =
      ∑ k, C (KernelBaseChange.Grassmannian.normalizedKernelMatrix a Q k j) * monomial k.down.val 1 := by
  rw [normalizedPolynomialGenerator, Basis.equivFun_symm_apply]
  simp only [Submodule.coe_sum, Submodule.coe_smul, Homogeneous.CoordinateBasis.GradedHilbert.coordinateDegreeBasis_val, smul_eq_C_mul,
    Matrix.col_apply]

theorem normalizedPolynomialGenerator_map {S : Type u} [CommRing S] (φ : R →+* S)
    (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) (Q : Matrix ι (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) R)
    (j : Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) :
    MvPolynomial.map φ (normalizedPolynomialGenerator a Q j) =
      normalizedPolynomialGenerator a (Q.map φ) j := by
  simp only [normalizedPolynomialGenerator_sum, map_sum, map_mul, map_C, map_monomial,
    map_one, ← KernelBaseChange.Grassmannian.normalizedKernelMatrix_map φ a Q, Matrix.map_apply]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.PolynomialGenerators.GradedHilbert
