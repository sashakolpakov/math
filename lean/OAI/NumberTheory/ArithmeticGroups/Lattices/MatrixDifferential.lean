import OAI.NumberTheory.ArithmeticGroups.Lattices.DifferentialDerivationCore
import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.CoefficientMap

/-! # Matrix Differential -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixDifferential.Construction

noncomputable section

section

/-! Polynomial equations of the algebraic hull of a family of matrix
directions. These equations vanish at the identity and are preserved by
every specified infinitesimal direction. -/

open scoped Classical

def matrixDifferentialCore {k : Type} [Field k] {n : ℕ}
    (S : Set (Matrix (Fin n) (Fin n) k)) : Ideal (Algebraic.CoordinatePolynomial n k) :=
  DifferentialDerivationCore.Construction.differentialCore (Infinitesimal.Action.Construction.rightInfinitesimal '' S)
    (RingHom.ker (Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k)))

theorem matrixDifferentialCore_eval_one {k : Type} [Field k] {n : ℕ}
    (S : Set (Matrix (Fin n) (Fin n) k)) {p : Algebraic.CoordinatePolynomial n k}
    (hp : p ∈ matrixDifferentialCore S) :
    Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) p = 0 :=
  DifferentialDerivationCore.Construction.differentialCore_le _ _ hp

theorem matrixDifferentialCore_derivative {k : Type} [Field k] {n : ℕ}
    (S : Set (Matrix (Fin n) (Fin n) k)) {A : Matrix (Fin n) (Fin n) k} (hA : A ∈ S)
    {p : Algebraic.CoordinatePolynomial n k} (hp : p ∈ matrixDifferentialCore S) :
    Infinitesimal.Action.Construction.rightInfinitesimal A p ∈ matrixDifferentialCore S :=
  DifferentialDerivationCore.Construction.differentialCore_derivation (Infinitesimal.Action.Construction.rightInfinitesimal '' S)
    (RingHom.ker (Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k)))
    (Infinitesimal.Action.Construction.rightInfinitesimal A) ⟨A, hA, rfl⟩ hp

theorem vanishingIdeal_le_matrixDifferentialCore {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (S : Set (Matrix (Fin n) (Fin n) k))
    (hS : S ⊆ Infinitesimal.Action.Construction.infinitesimalStabilizer G) :
    VanishingIdeal.Construction.coordinateVanishingIdeal G ≤ matrixDifferentialCore S := by
  apply DifferentialDerivationCore.Construction.le_differentialCore
  · intro p hp
    exact hp k (RingHom.id k) (1 : G.RationalPoints)
  · rintro D ⟨A, hA, rfl⟩ p hp
    exact (Infinitesimal.Action.Construction.mem_infinitesimalStabilizer G A).mp (hS hA) p hp

theorem matrixDifferentialCore_isRadical {k : Type} [Field k] [CharZero k] {n : ℕ}
    (S : Set (Matrix (Fin n) (Fin n) k)) : (matrixDifferentialCore S).IsRadical :=
  DifferentialDerivationCore.Construction.differentialCore_isRadical _ _ (RingHom.ker_isPrime _).isRadical

theorem leftTranslate_mem_matrixDifferentialCore {k : Type} [Field k] {n : ℕ}
    (S : Set (Matrix (Fin n) (Fin n) k)) (g : Algebraic.SL n k)
    (hg : ∀ p ∈ matrixDifferentialCore S, Algebraic.evaluateMatrix (RingHom.id k) g p = 0)
    {p : Algebraic.CoordinatePolynomial n k} (hp : p ∈ matrixDifferentialCore S) :
    LeftTranslation.Construction.leftTranslate (g : Matrix (Fin n) (Fin n) k) p ∈ matrixDifferentialCore S := by
  apply Ideal.mem_iInf.mpr
  intro m
  induction m generalizing p with
  | zero =>
      change Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) (LeftTranslation.Construction.leftTranslate _ p) = 0
      rw [TangentIdentity.Construction.leftTranslate_evaluate_one]
      exact hg p hp
  | succ m ih =>
      refine ⟨ih hp, ?_⟩
      rintro D ⟨A, hA, rfl⟩
      rw [LeftTranslation.Construction.rightInfinitesimal_leftTranslate]
      exact ih (matrixDifferentialCore_derivative S hA hp)

theorem leftTranslate_evaluate_rational {k : Type} [Field k] {n : ℕ}
    (g x : Algebraic.SL n k) (p : Algebraic.CoordinatePolynomial n k) :
    Algebraic.evaluateMatrix (RingHom.id k) x (LeftTranslation.Construction.leftTranslate (g : Matrix (Fin n) (Fin n) k) p) =
      Algebraic.evaluateMatrix (RingHom.id k) (g * x) p := by
  have hg : Matrix.SpecialLinearGroup.map (RingHom.id k) g = g := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rfl
  rw [LeftTranslation.Construction.leftTranslate_evaluate, hg]

end

/-! Coordinate polynomials for a matrix acting on a vector, tested by a
linear functional. Infinitesimal right translation differentiates the
input vector. -/

open scoped Classical
open _root_.MvPolynomial

def matrixVectorPolynomial {k : Type} [Field k] {n : ℕ}
    (w : Fin n → k) (i : Fin n) : Algebraic.CoordinatePolynomial n k :=
  ∑ j, X (i, j) * C (w j)

theorem evaluate_matrixVectorPolynomial {k : Type} [Field k] {n : ℕ}
    (g : Algebraic.SL n k) (w : Fin n → k) (i : Fin n) :
    Algebraic.evaluateMatrix (RingHom.id k) g (matrixVectorPolynomial w i) =
      (g : Matrix (Fin n) (Fin n) k).mulVec w i := by
  simp [matrixVectorPolynomial, Algebraic.evaluateMatrix, Matrix.mulVec, dotProduct]

theorem derivative_matrixVectorPolynomial {k : Type} [Field k] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) k) (w : Fin n → k) (i : Fin n) :
    Infinitesimal.Action.Construction.rightInfinitesimal A (matrixVectorPolynomial w i) = matrixVectorPolynomial (A.mulVec w) i := by
  exact Infinitesimal.Action.Construction.rightInfinitesimal_on_linear_entry A (fun j _ => w j) i i

def matrixFunctionalPolynomial {k : Type} [Field k] {n : ℕ}
    (φ : Module.Dual k (Fin n → k)) (w : Fin n → k) : Algebraic.CoordinatePolynomial n k :=
  ∑ i, C (φ (Pi.single i 1)) * matrixVectorPolynomial w i

theorem dual_apply_eq_coordinate_sum {k : Type} [Field k] {n : ℕ}
    (φ : Module.Dual k (Fin n → k)) (w : Fin n → k) :
    φ w = ∑ i, φ (Pi.single i 1) * w i := by
  have he : (∑ i : Fin n, w i • Pi.single i (1 : k)) = w := by
    ext j
    simp [Pi.single_apply]
  rw [← he, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, smul_eq_mul]
  rw [he, mul_comm]

theorem evaluate_matrixFunctionalPolynomial {k : Type} [Field k] {n : ℕ}
    (g : Algebraic.SL n k) (φ : Module.Dual k (Fin n → k)) (w : Fin n → k) :
    Algebraic.evaluateMatrix (RingHom.id k) g (matrixFunctionalPolynomial φ w) =
      φ ((g : Matrix (Fin n) (Fin n) k).mulVec w) := by
  unfold matrixFunctionalPolynomial
  simp only [map_sum, map_mul, evaluate_matrixVectorPolynomial]
  have hC (a : k) : Algebraic.evaluateMatrix (RingHom.id k) g (C a) = a := by simp [Algebraic.evaluateMatrix]
  simp only [hC]
  exact (dual_apply_eq_coordinate_sum _ _).symm

theorem derivative_matrixFunctionalPolynomial {k : Type} [Field k] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) k) (φ : Module.Dual k (Fin n → k)) (w : Fin n → k) :
    Infinitesimal.Action.Construction.rightInfinitesimal A (matrixFunctionalPolynomial φ w) =
      matrixFunctionalPolynomial φ (A.mulVec w) := by
  unfold matrixFunctionalPolynomial
  simp only [map_sum, LeftTranslation.Construction.rightInfinitesimal_C_mul, derivative_matrixVectorPolynomial]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixDifferential.Construction
