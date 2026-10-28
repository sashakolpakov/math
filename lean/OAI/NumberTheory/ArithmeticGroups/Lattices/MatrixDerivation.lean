import OAI.NumberTheory.ArithmeticGroups.Lattices.CharZeroTangent
import OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixDifferential

/-! # Matrix Derivation -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixDerivation.Construction

noncomputable section

section

/-! The algebraic chain rule for evaluating matrix coordinate
polynomials along a derivation of an extension field. -/

open scoped Classical
open _root_.MvPolynomial

theorem evaluate_rightInfinitesimal_X_at_point
    {k : Type} [Field k] {n : ℕ} (g : Algebraic.SL n k)
    (A : Matrix (Fin n) (Fin n) k) (i j : Fin n) :
    Algebraic.evaluateMatrix (RingHom.id k) g (Infinitesimal.Action.Construction.rightInfinitesimal A (X (i, j))) =
      ((g : Matrix (Fin n) (Fin n) k) * A) i j := by
  simp [Infinitesimal.Action.Construction.rightInfinitesimal_X, Algebraic.evaluateMatrix, Matrix.mul_apply]

theorem derivation_evaluate_matrix
    {k K : Type} [Field k] [Field K] [Algebra k K] {n : ℕ}
    (D : Derivation k K K) (g : Algebraic.SL n K) (A : Matrix (Fin n) (Fin n) K)
    (hA : (g : Matrix (Fin n) (Fin n) K) * A = fun i j => D (g i j))
    (p : Algebraic.CoordinatePolynomial n k) :
    D (Algebraic.evaluateMatrix (algebraMap k K) g p) =
      Algebraic.evaluateMatrix (RingHom.id K) g (Infinitesimal.Action.Construction.rightInfinitesimal A (MvPolynomial.map (algebraMap k K) p)) := by
  have he (p : Algebraic.CoordinatePolynomial n k) :
      Algebraic.evaluateMatrix (RingHom.id K) g (MvPolynomial.map (algebraMap k K) p) =
        Algebraic.evaluateMatrix (algebraMap k K) g p := by
    rw [BaseChange.Construction.evaluateMatrix_coefficient_map, RingHom.id_comp]
  induction p using MvPolynomial.induction_on with
  | C c => simp [Algebraic.evaluateMatrix]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p ij hp =>
      rcases ij with ⟨i, j⟩
      have hx : Algebraic.evaluateMatrix (algebraMap k K) g (X (i, j)) = g i j := by simp [Algebraic.evaluateMatrix]
      have hxm : Algebraic.evaluateMatrix (RingHom.id K) g (X (i, j)) = g i j := by simp [Algebraic.evaluateMatrix]
      simp only [map_mul, MvPolynomial.map_X, Derivation.leibniz, smul_eq_mul, map_add, hp,
        he, hx, hxm, evaluate_rightInfinitesimal_X_at_point, hA]

theorem mem_infinitesimalStabilizer_iff_at_point
    {k : Type} [Field k] [CharZero k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (g : G.RationalPoints) (A : Matrix (Fin n) (Fin n) k) :
    A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G ↔
      ∀ p ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G,
        Algebraic.evaluateMatrix (RingHom.id k) g.val (Infinitesimal.Action.Construction.rightInfinitesimal A p) = 0 := by
  constructor
  · intro hA p hp
    exact (Infinitesimal.Action.Construction.mem_infinitesimalStabilizer G A).mp hA p hp k (RingHom.id k) g
  · intro h
    apply (CharZeroTangent.Construction.mem_infinitesimalStabilizer_iff_tangent G hG A).mpr
    intro p hp
    have he := h (LeftTranslation.Construction.leftTranslate ((g.val⁻¹ : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k) p)
      (LeftTranslation.Construction.leftTranslate_mem_vanishingIdeal G g.val⁻¹
        ((G.subgroup k (RingHom.id k)).inv_mem g.property) p hp)
    rw [LeftTranslation.Construction.rightInfinitesimal_leftTranslate, MatrixDifferential.Construction.leftTranslate_evaluate_rational, inv_mul_cancel] at he
    exact he

end

section

/-! Applying a derivation of an extension field to a group-valued
matrix gives a logarithmic derivative in the group's actual Lie algebra. -/

open scoped Classical

def logarithmicMatrixDerivative
    {k K : Type} [Field k] [Field K] [Algebra k K] {n : ℕ}
    (D : Derivation k K K) (g : Algebraic.SL n K) : Matrix (Fin n) (Fin n) K :=
  ((g⁻¹ : Algebraic.SL n K) : Matrix (Fin n) (Fin n) K) *
    (show Matrix (Fin n) (Fin n) K from fun i j => D (g i j))

theorem mul_logarithmicMatrixDerivative
    {k K : Type} [Field k] [Field K] [Algebra k K] {n : ℕ}
    (D : Derivation k K K) (g : Algebraic.SL n K) :
    (g : Matrix (Fin n) (Fin n) K) * logarithmicMatrixDerivative D g =
      fun i j => D (g i j) := by
  have hg : (g : Matrix (Fin n) (Fin n) K) *
      ((g⁻¹ : Algebraic.SL n K) : Matrix (Fin n) (Fin n) K) = 1 := by
    change ((g * g⁻¹ : Algebraic.SL n K) : Matrix (Fin n) (Fin n) K) = 1
    rw [mul_inv_cancel]
    rfl
  unfold logarithmicMatrixDerivative
  rw [← Matrix.mul_assoc, hg, Matrix.one_mul]

theorem logarithmicMatrixDerivative_mem
    {k K : Type} [Field k] [CharZero k] [Field K] [Algebra k K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (D : Derivation k K K)
    (g : (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K)).RationalPoints) :
    logarithmicMatrixDerivative D g.val ∈
      Infinitesimal.Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K)) := by
  let : CharZero K := Algebra.charZero_of_charZero k K
  let A := logarithmicMatrixDerivative D g.val
  let J := DifferentialDerivationCore.Construction.derivativeIdealStep {Infinitesimal.Action.Construction.rightInfinitesimal A}
    (RingHom.ker (Algebraic.evaluateMatrix (RingHom.id K) g.val))
  have hg : g.val ∈ G.subgroup K (algebraMap k K) := by
    have hh := g.property
    change g.val ∈ G.subgroup K ((RingHom.id K).comp (algebraMap k K)) at hh
    simpa only [RingHom.id_comp] using hh
  have hle : VanishingIdeal.Construction.coordinateVanishingIdeal (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K)) ≤ J := by
    rw [GeneralVanishingBaseChange.Construction.vanishingIdeal_charZero_baseChange G hG, Ideal.map_le_iff_le_comap]
    intro p hp
    have hp0 : Algebraic.evaluateMatrix (algebraMap k K) g.val p = 0 := hp K (algebraMap k K) ⟨g.val, hg⟩
    refine ⟨?_, ?_⟩
    · change Algebraic.evaluateMatrix (RingHom.id K) g.val (MvPolynomial.map (algebraMap k K) p) = 0
      rw [BaseChange.Construction.evaluateMatrix_coefficient_map, RingHom.id_comp, hp0]
    · intro E hE
      have he : E = Infinitesimal.Action.Construction.rightInfinitesimal A := Set.mem_singleton_iff.mp hE
      rw [he]
      change Algebraic.evaluateMatrix (RingHom.id K) g.val
        (Infinitesimal.Action.Construction.rightInfinitesimal A (MvPolynomial.map (algebraMap k K) p)) = 0
      rw [← derivation_evaluate_matrix D g.val A (mul_logarithmicMatrixDerivative D g.val), hp0, map_zero]
  apply (mem_infinitesimalStabilizer_iff_at_point _ (ConnectedBaseChange.Construction.geometrically_connected_baseChange G hG) g A).mpr
  intro p hp
  exact (hle hp).2 (Infinitesimal.Action.Construction.rightInfinitesimal A) (Set.mem_singleton _)

end

/-! Entrywise field derivations of matrix products and inverses. -/

open scoped Classical

theorem matrix_derivation_mul
    {k K : Type*} [Field k] [Field K] [Algebra k K] {n : ℕ}
    (D : Derivation k K K) (A B : Matrix (Fin n) (Fin n) K) :
    (A * B).map D = A * B.map D + A.map D * B := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum,
    Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  exact mul_comm _ _

theorem matrix_derivation_one
    {k K : Type*} [Field k] [Field K] [Algebra k K] {n : ℕ}
    (D : Derivation k K K) : (1 : Matrix (Fin n) (Fin n) K).map D = 0 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.one_apply, Matrix.zero_apply]
  split_ifs <;> simp

theorem matrix_derivation_base
    {k K : Type*} [Field k] [Field K] [Algebra k K] {n : ℕ}
    (D : Derivation k K K) (C : Matrix (Fin n) (Fin n) k) :
    (C.map (algebraMap k K)).map D = 0 := by
  ext i j
  exact D.map_algebraMap _

theorem matrix_derivation_inverse
    {k K : Type} [Field k] [Field K] [Algebra k K] {n : ℕ}
    (D : Derivation k K K) (g : Algebraic.SL n K) :
    (((g⁻¹ : Algebraic.SL n K) : Matrix (Fin n) (Fin n) K)).map D =
      -(logarithmicMatrixDerivative D g * ((g⁻¹ : Algebraic.SL n K) : Matrix (Fin n) (Fin n) K)) := by
  have hgi : (g : Matrix (Fin n) (Fin n) K) *
      ((g⁻¹ : Algebraic.SL n K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hig : ((g⁻¹ : Algebraic.SL n K) : Matrix (Fin n) (Fin n) K) *
      (g : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hh := matrix_derivation_mul D (g : Matrix (Fin n) (Fin n) K)
    ((g⁻¹ : Algebraic.SL n K) : Matrix (Fin n) (Fin n) K)
  have hd : (g : Matrix (Fin n) (Fin n) K).map D =
      (g : Matrix (Fin n) (Fin n) K) * logarithmicMatrixDerivative D g :=
    (mul_logarithmicMatrixDerivative D g).symm
  rw [hgi, matrix_derivation_one, hd] at hh
  have he := congrArg (fun M : Matrix (Fin n) (Fin n) K =>
    ((g⁻¹ : Algebraic.SL n K) : Matrix (Fin n) (Fin n) K) * M) hh
  rw [Matrix.mul_zero, Matrix.mul_add, ← Matrix.mul_assoc, hig, Matrix.one_mul,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, hig, Matrix.one_mul] at he
  exact eq_neg_of_add_eq_zero_left he.symm

theorem matrix_derivation_conjugation_zero
    {k K : Type} [Field k] [Field K] [Algebra k K] {n : ℕ}
    (D : Derivation k K K) (g : Algebraic.SL n K) (C : Matrix (Fin n) (Fin n) k)
    (hC : logarithmicMatrixDerivative D g * C.map (algebraMap k K) =
      C.map (algebraMap k K) * logarithmicMatrixDerivative D g) :
    ((g : Matrix (Fin n) (Fin n) K) * C.map (algebraMap k K) *
      ((g⁻¹ : Algebraic.SL n K) : Matrix (Fin n) (Fin n) K)).map D = 0 := by
  have hd : (g : Matrix (Fin n) (Fin n) K).map D =
      (g : Matrix (Fin n) (Fin n) K) * logarithmicMatrixDerivative D g :=
    (mul_logarithmicMatrixDerivative D g).symm
  rw [matrix_derivation_mul, matrix_derivation_mul, matrix_derivation_base,
    Matrix.mul_zero, zero_add, matrix_derivation_inverse, hd]
  simp only [Matrix.mul_neg, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (C.map (algebraMap k K)), ← hC, Matrix.mul_assoc,
    neg_add_cancel]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixDerivation.Construction
