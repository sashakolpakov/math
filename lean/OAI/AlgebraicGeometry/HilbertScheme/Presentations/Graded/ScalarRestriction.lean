import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IntegerPolynomialGrading
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.RingTheory.MvPolynomial.Basic

/-! # Scalar Restriction -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.ScalarRestriction.GradedModules

noncomputable section

/-! Restriction of coefficient scalars preserves graded decompositions and the actual polynomial graded action. -/

open _root_.MvPolynomial DirectSum

universe u v w t

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]

section Decomposition

variable {δ : Type w} [DecidableEq δ]
variable {M : Type t} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
variable (ℳ : δ → Submodule S M) [Decomposition ℳ]

@[instance_reducible]
def restrictScalarsDecomposition : Decomposition (fun d => (ℳ d).restrictScalars R) where
  decompose' := DirectSum.decompose ℳ
  left_inv := (DirectSum.decompose ℳ).left_inv
  right_inv := (DirectSum.decompose ℳ).right_inv

end Decomposition

variable {σ : Type w} [Fintype σ]

omit [Fintype σ] in
theorem coefficientMap_integer_homogeneous {d : ℤ} {p : MvPolynomial σ R}
    (hp : p ∈ WeightedFreeModules.GradedModules.polynomialIntegerGrading R d) :
    MvPolynomial.map (algebraMap R S) p ∈ WeightedFreeModules.GradedModules.polynomialIntegerGrading S d := by
  intro m hm
  apply hp
  intro hz
  exact hm (by rw [MvPolynomial.coeff_map, hz, map_zero])

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {M : Type t} [AddCommGroup M] [Module R M] [Module S M]
  [Module (MvPolynomial σ R) M] [Module (MvPolynomial σ S) M]
  [IsScalarTower R S M] [IsScalarTower (MvPolynomial σ R) (MvPolynomial σ S) M]
variable (ℳ : ℤ → Submodule S M) [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) S) ℳ]

omit [Fintype σ] in
theorem coefficientRestriction_gradedSMul :
    SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) (fun d => (ℳ d).restrictScalars R) := by
  constructor
  intro i j p m hp hm
  change p • m ∈ ℳ (i + j)
  rw [← algebraMap_smul (MvPolynomial σ S)]
  have hm' : m ∈ ℳ j := hm
  have hp' : MvPolynomial.map (algebraMap R S) p ∈ WeightedFreeModules.GradedModules.polynomialIntegerGrading S i :=
    coefficientMap_integer_homogeneous hp
  exact SetLike.GradedSMul.smul_mem hp' hm'

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.ScalarRestriction.GradedModules
