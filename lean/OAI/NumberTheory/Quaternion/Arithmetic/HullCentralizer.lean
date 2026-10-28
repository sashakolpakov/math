import OAI.NumberTheory.Quaternion.Arithmetic.CentralizerPolynomials
import OAI.NumberTheory.ArithmeticGroups.Lattices.DifferentialHullGroup

/-! # Hull Centralizer -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.HullCentralizer

noncomputable section

/-! Every element of the algebraic hull commutes with any matrix that
commutes with all of its generating infinitesimal directions. -/

open scoped Classical
open OAI.NumberTheory.ArithmeticGroups.Lattices.DifferentialHullGroup.Construction _root_.MvPolynomial Set

variable {k : Type} [Field k] {n : ℕ}

theorem evaluate_centralizerMatrixPolynomial (g : ArithmeticGroups.Lattices.Algebraic.SL n k)
    (B : Matrix (Fin n) (Fin n) k) (i j : Fin n) :
    ArithmeticGroups.Lattices.Algebraic.evaluateMatrix (RingHom.id k) g (CentralizerPolynomials.centralizerMatrixPolynomial B i j) =
      ((g : Matrix (Fin n) (Fin n) k) * B - B * (g : Matrix (Fin n) (Fin n) k)) i j := by
  change ArithmeticGroups.Lattices.Algebraic.evaluateMatrix (RingHom.id k) g
    ((∑ l, X (i, l) * C (B l j)) - (∑ l, C (B i l) * X (l, j))) = _
  simp [Matrix.mul_apply, ArithmeticGroups.Lattices.Algebraic.evaluateMatrix]

theorem centralizer_polynomial_mem_core
    (S : Set (Matrix (Fin n) (Fin n) k)) (B : Matrix (Fin n) (Fin n) k)
    (hB : ∀ A ∈ S, A * B = B * A) (i j : Fin n) :
    CentralizerPolynomials.centralizerMatrixPolynomial B i j ∈ ArithmeticGroups.Lattices.MatrixDifferential.Construction.matrixDifferentialCore S := by
  let P : Set (ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial n k) := range
    (fun ij : Fin n × Fin n => CentralizerPolynomials.centralizerMatrixPolynomial B ij.1 ij.2)
  have hle : Ideal.span P ≤ ArithmeticGroups.Lattices.MatrixDifferential.Construction.matrixDifferentialCore S := by
    apply DifferentialGenerators.span_le_differentialCore_of_generators
    · rintro p ⟨⟨a, b⟩, rfl⟩
      change ArithmeticGroups.Lattices.Algebraic.evaluateMatrix (RingHom.id k) (1 : ArithmeticGroups.Lattices.Algebraic.SL n k)
        (CentralizerPolynomials.centralizerMatrixPolynomial B a b) = 0
      rw [evaluate_centralizerMatrixPolynomial]
      simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul, Matrix.mul_one,
        sub_self, Matrix.zero_apply]
    · rintro D ⟨A, hA, rfl⟩ p ⟨⟨a, b⟩, rfl⟩
      have he := congrArg (fun M : Matrix (Fin n) (Fin n) (ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial n k) => M a b)
        (CentralizerPolynomials.rightInfinitesimal_centralizerMatrixPolynomial A B (hB A hA))
      change ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.rightInfinitesimal A (CentralizerPolynomials.centralizerMatrixPolynomial B a b) =
        ∑ l, CentralizerPolynomials.centralizerMatrixPolynomial B a l * C (A l b) at he
      rw [he]
      apply Ideal.sum_mem
      intro l _
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨(a, l), rfl⟩)
  exact hle (Ideal.subset_span ⟨(i, j), rfl⟩)

theorem differentialHull_commutes
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup k n) (S : Set (Matrix (Fin n) (Fin n) k))
    (B : Matrix (Fin n) (Fin n) k) (hB : ∀ A ∈ S, A * B = B * A)
    (g : G.RationalPoints) (hg : g ∈ ArithmeticGroups.Lattices.DifferentialHullGroup.Construction.differentialHullSubgroup G S) :
    (g.val : Matrix (Fin n) (Fin n) k) * B = B * (g.val : Matrix (Fin n) (Fin n) k) := by
  apply sub_eq_zero.mp
  ext i j
  have he := hg (CentralizerPolynomials.centralizerMatrixPolynomial B i j) (centralizer_polynomial_mem_core S B hB i j)
  rwa [evaluate_centralizerMatrixPolynomial] at he

theorem evaluate_infinitesimal_centralizer_at_one
    (A B : Matrix (Fin n) (Fin n) k) (i j : Fin n) :
    ArithmeticGroups.Lattices.Algebraic.evaluateMatrix (RingHom.id k) (1 : ArithmeticGroups.Lattices.Algebraic.SL n k)
      (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.rightInfinitesimal A (CentralizerPolynomials.centralizerMatrixPolynomial B i j)) = (A * B - B * A) i j := by
  change ArithmeticGroups.Lattices.Algebraic.evaluateMatrix (RingHom.id k) (1 : ArithmeticGroups.Lattices.Algebraic.SL n k)
    (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.rightInfinitesimal A ((∑ l, X (i, l) * C (B l j)) - (∑ l, C (B i l) * X (l, j)))) = _
  simp only [map_sub, map_sum, Derivation.leibniz, ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.rightInfinitesimal_C, smul_eq_mul,
    mul_zero, zero_add, add_zero, map_mul, ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.evaluate_rightInfinitesimal_X]
  simp [ArithmeticGroups.Lattices.Algebraic.evaluateMatrix, Matrix.mul_apply, mul_comm]

theorem group_commutes_implies_infinitesimal_commutes [IsAlgClosed k]
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup k n) (B : Matrix (Fin n) (Fin n) k)
    (hB : ∀ g : G.RationalPoints,
      (g.val : Matrix (Fin n) (Fin n) k) * B = B * (g.val : Matrix (Fin n) (Fin n) k))
    {A : Matrix (Fin n) (Fin n) k} (hA : A ∈ ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G) : A * B = B * A := by
  apply sub_eq_zero.mp
  ext i j
  have hp : CentralizerPolynomials.centralizerMatrixPolynomial B i j ∈ ArithmeticGroups.Lattices.VanishingIdeal.Construction.coordinateVanishingIdeal G := by
    apply (ArithmeticGroups.Lattices.BaseChange.Construction.mem_vanishingIdeal_iff_rational_of_algClosed G _).mpr
    intro g
    rw [evaluate_centralizerMatrixPolynomial, hB g, sub_self]
    rfl
  have hd := (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.mem_infinitesimalStabilizer G A).mp hA _ hp
  have he := hd k (RingHom.id k) (1 : G.RationalPoints)
  change ArithmeticGroups.Lattices.Algebraic.evaluateMatrix (RingHom.id k) (1 : ArithmeticGroups.Lattices.Algebraic.SL n k)
    (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.rightInfinitesimal A (CentralizerPolynomials.centralizerMatrixPolynomial B i j)) = 0 at he
  rwa [evaluate_infinitesimal_centralizer_at_one] at he

end

end OAI.NumberTheory.Quaternion.Arithmetic.HullCentralizer
