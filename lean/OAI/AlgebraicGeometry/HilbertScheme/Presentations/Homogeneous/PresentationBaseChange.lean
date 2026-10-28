import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.RelationPresentation
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Presentation Base Change -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.PresentationBaseChange.GradedHilbert

noncomputable section

/-! Actual homogeneous relation presentations commute with coefficient base change. -/

open _root_.MvPolynomial TensorProduct

universe u v z

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
variable {n : ℕ} {ι : Type z} [Fintype ι]

def homogeneousVectorBaseChangeEquiv (d : ℕ) :
    S ⊗[R] (ι → Hilbert.Polynomial.GradedHilbert.grading R n d) ≃ₗ[R] (ι → Hilbert.Polynomial.GradedHilbert.grading S n d) := by
  classical
  exact (TensorProduct.piRight R R S (fun _ : ι => Hilbert.Polynomial.GradedHilbert.grading R n d)).trans
    (LinearEquiv.piCongrRight (fun _ : ι =>
      (CoefficientBaseChange.GradedHilbert.homogeneousPieceBaseChangeEquiv (R := R) (S := S) (n := n) d).restrictScalars R))

theorem homogeneousVectorBaseChangeEquiv_tmul (d : ℕ) (s : S)
    (a : ι → Hilbert.Polynomial.GradedHilbert.grading R n d) (i : ι) :
    (homogeneousVectorBaseChangeEquiv (S := S) d (s ⊗ₜ[R] a) i).val =
      s • MvPolynomial.map (algebraMap R S) (a i).val := by
  classical
  change (CoefficientBaseChange.GradedHilbert.homogeneousPieceBaseChangeEquiv (S := S) d (s ⊗ₜ[R] a i)).val = _
  exact CoefficientBaseChange.GradedHilbert.homogeneousPieceBaseChangeEquiv_tmul d s (a i)

theorem homogeneousPresentation_baseChange
    (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N)
    (d : ℕ) (x : S ⊗[R] (ι → Hilbert.Polynomial.GradedHilbert.grading R n d)) :
    CoefficientBaseChange.GradedHilbert.homogeneousPieceBaseChangeEquiv (S := S) (d + N)
      ((RelationPresentation.GradedHilbert.homogeneousRelationPresentation g N hg d).lTensor S x) =
    RelationPresentation.GradedHilbert.homogeneousRelationPresentation (Finite.SyzygyLifting.GradedHilbert.mapRelationVector (algebraMap R S) g) N
      (fun i => (hg i).map (algebraMap R S)) d
      (homogeneousVectorBaseChangeEquiv (S := S) d x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s a =>
    apply Subtype.ext
    rw [LinearMap.lTensor_tmul, CoefficientBaseChange.GradedHilbert.homogeneousPieceBaseChangeEquiv_tmul,
      RelationPresentation.GradedHilbert.homogeneousRelationPresentation_val]
    change s • MvPolynomial.map (algebraMap R S) (SyzygiesFromPolynomialKernel.GradedHilbert.polynomialRelationMap g (fun i => (a i).val)) =
      SyzygiesFromPolynomialKernel.GradedHilbert.polynomialRelationMap (Finite.SyzygyLifting.GradedHilbert.mapRelationVector (algebraMap R S) g)
        (fun i => (homogeneousVectorBaseChangeEquiv (S := S) d (s ⊗ₜ[R] a) i).val)
    simp only [SyzygiesFromPolynomialKernel.GradedHilbert.polynomialRelationMap, LinearMap.coe_mk, AddHom.coe_mk,
      homogeneousVectorBaseChangeEquiv_tmul, Finite.SyzygyLifting.GradedHilbert.mapRelationVector, map_sum, map_mul,
      Finset.smul_sum, smul_mul_assoc]
  | add x y hx hy =>
    simp only [LinearMap.map_add, LinearEquiv.map_add, hx, hy]

omit [Fintype ι] in
theorem coordinateDegreeSpace_free (d : ℕ) : Module.Free R (Hilbert.Polynomial.GradedHilbert.grading R n d) := by
  rw [Hilbert.Polynomial.GradedHilbert.grading, homogeneousSubmodule_eq_finsupp_supported]
  exact Module.Free.of_basis (basisRestrictSupport R {a : Fin (n + 1) →₀ ℕ | a.degree = d})

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.PresentationBaseChange.GradedHilbert
