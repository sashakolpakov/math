import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Coordinate Substitution -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.CoordinateSubstitution

noncomputable section

/-! A linear change of coefficient vectors extends to polynomial
substitution, preserves every homogeneous degree, and respects composition. -/
universe u v w
variable {R : Type u} [CommRing R] {σ : Type v} {τ : Type w}

def linearCoordinatePolynomial : (σ →₀ R) →ₗ[R] MvPolynomial σ R :=
  Finsupp.linearCombination R MvPolynomial.X

theorem linearCoordinatePolynomial_single (i : σ) (r : R) :
    linearCoordinatePolynomial (Finsupp.single i r) = r • (MvPolynomial.X i : MvPolynomial σ R) :=
  Finsupp.linearCombination_single R r i

theorem linearCoordinatePolynomial_homogeneous (a : σ →₀ R) :
    (linearCoordinatePolynomial a).IsHomogeneous 1 := by
  change a.sum (fun i r => r • (MvPolynomial.X i : MvPolynomial σ R)) ∈
    MvPolynomial.homogeneousSubmodule σ R 1
  exact (MvPolynomial.homogeneousSubmodule σ R 1).sum_mem
    (fun i _ => (MvPolynomial.homogeneousSubmodule σ R 1).smul_mem _ (MvPolynomial.isHomogeneous_X R i))

def polynomialLinearSubstitution (T : (σ →₀ R) →ₗ[R] (τ →₀ R)) :
    MvPolynomial σ R →ₐ[R] MvPolynomial τ R :=
  MvPolynomial.aeval (fun i => linearCoordinatePolynomial (T (Finsupp.single i 1)))

theorem polynomialLinearSubstitution_X (T : (σ →₀ R) →ₗ[R] (τ →₀ R)) (i : σ) :
    polynomialLinearSubstitution T (MvPolynomial.X i) =
      linearCoordinatePolynomial (T (Finsupp.single i 1)) :=
  MvPolynomial.aeval_X _ i

theorem polynomialLinearSubstitution_linear (T : (σ →₀ R) →ₗ[R] (τ →₀ R)) (a : σ →₀ R) :
    polynomialLinearSubstitution T (linearCoordinatePolynomial a) =
      linearCoordinatePolynomial (T a) := by
  induction a using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | single i r =>
      have hs : Finsupp.single i r = r • Finsupp.single i (1 : R) := by
        rw [Finsupp.smul_single', mul_one]
      rw [linearCoordinatePolynomial_single, map_smul, polynomialLinearSubstitution_X,
        hs, map_smul, map_smul]

theorem polynomialLinearSubstitution_homogeneous
    (T : (σ →₀ R) →ₗ[R] (τ →₀ R)) {d : ℕ} {p : MvPolynomial σ R}
    (hp : p.IsHomogeneous d) : (polynomialLinearSubstitution T p).IsHomogeneous d := by
  simpa only [polynomialLinearSubstitution, one_mul] using hp.aeval
    (fun i => linearCoordinatePolynomial (T (Finsupp.single i 1)))
    (fun i => linearCoordinatePolynomial_homogeneous (T (Finsupp.single i 1)))

theorem polynomialLinearSubstitution_id :
    polynomialLinearSubstitution (LinearMap.id : (σ →₀ R) →ₗ[R] (σ →₀ R)) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro i
  exact (polynomialLinearSubstitution_X LinearMap.id i).trans
    ((linearCoordinatePolynomial_single i 1).trans (one_smul R _))

theorem polynomialLinearSubstitution_comp {κ : Type*}
    (T : (σ →₀ R) →ₗ[R] (τ →₀ R)) (U : (τ →₀ R) →ₗ[R] (κ →₀ R)) :
    (polynomialLinearSubstitution U).comp (polynomialLinearSubstitution T) =
      polynomialLinearSubstitution (U.comp T) := by
  apply MvPolynomial.algHom_ext
  intro i
  change polynomialLinearSubstitution U (polynomialLinearSubstitution T (MvPolynomial.X i)) = _
  rw [polynomialLinearSubstitution_X, polynomialLinearSubstitution_linear,
    polynomialLinearSubstitution_X]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.CoordinateSubstitution
