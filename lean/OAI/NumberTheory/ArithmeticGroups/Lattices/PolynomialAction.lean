import OAI.NumberTheory.ArithmeticGroups.Lattices.Algebraic

/-! # Polynomial Action -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.PolynomialAction.Construction

noncomputable section

/-! The finite-dimensional polynomial representations used to realize a
matrix algebraic group as a stabilizer. -/

open scoped Classical
open OAI.NumberTheory.ArithmeticGroups.Lattices.Algebraic _root_.MvPolynomial

theorem totalDegree_aeval_le_of_linear
    {σ τ k : Type*} [Field k]
    (v : σ → MvPolynomial τ k) (hv : ∀ i, (v i).totalDegree ≤ 1)
    (p : MvPolynomial σ k) : (aeval v p).totalDegree ≤ p.totalDegree := by
  have hmon : ∀ d : σ →₀ ℕ, ∀ c : k,
      (aeval v (monomial d c)).totalDegree ≤ d.sum (fun _ e => e) := by
    intro d c
    rw [aeval_monomial]
    apply (totalDegree_mul _ _).trans
    simp only [algebraMap_eq, totalDegree_C, zero_add]
    apply (totalDegree_finsetProd d.support _).trans
    apply Finset.sum_le_sum
    intro i _
    exact (totalDegree_pow (v i) (d i)).trans (by simpa using Nat.mul_le_mul_left (d i) (hv i))
  conv_lhs => rw [p.as_sum, map_sum]
  apply totalDegree_finsetSum_le
  intro d hd
  exact (hmon d (p.coeff d)).trans (le_totalDegree hd)

def rightTranslate {k : Type} [Field k] {n : ℕ}
    (g : Matrix (Fin n) (Fin n) k) : Algebraic.CoordinatePolynomial n k →ₐ[k] Algebraic.CoordinatePolynomial n k :=
  aeval (fun ij : Fin n × Fin n => ∑ l, X (ij.1, l) * C (g l ij.2))

@[simp] theorem rightTranslate_X {k : Type} [Field k] {n : ℕ}
    (g : Matrix (Fin n) (Fin n) k) (i j : Fin n) :
    rightTranslate g (X (i, j)) = ∑ l, X (i, l) * C (g l j) := by
  simp [rightTranslate]

@[simp] theorem rightTranslate_C {k : Type} [Field k] {n : ℕ}
    (g : Matrix (Fin n) (Fin n) k) (c : k) : rightTranslate g (C c) = C c := by
  simp [rightTranslate]

theorem rightTranslate_one {k : Type} [Field k] {n : ℕ} :
    rightTranslate (1 : Matrix (Fin n) (Fin n) k) = AlgHom.id k _ := by
  ext ij : 1
  rcases ij with ⟨i, j⟩
  simp [rightTranslate, Matrix.one_apply]

theorem rightTranslate_mul {k : Type} [Field k] {n : ℕ}
    (g h : Matrix (Fin n) (Fin n) k) :
    rightTranslate (g * h) = (rightTranslate g).comp (rightTranslate h) := by
  ext ij : 1
  rcases ij with ⟨i, j⟩
  simp only [AlgHom.comp_apply, rightTranslate_X, map_sum, map_mul, rightTranslate_C,
    Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro m _
  simp [mul_assoc]

theorem rightTranslate_totalDegree_le {k : Type} [Field k] {n : ℕ}
    (g : Matrix (Fin n) (Fin n) k) (p : Algebraic.CoordinatePolynomial n k) :
    (rightTranslate g p).totalDegree ≤ p.totalDegree := by
  apply totalDegree_aeval_le_of_linear
  intro ij
  apply totalDegree_finsetSum_le
  intro l _
  exact (totalDegree_mul _ _).trans (by simp)

theorem rightTranslate_evaluate {k K : Type} [Field k] [Field K] {n : ℕ}
    (ι : k →+* K) (x : Algebraic.SL n K) (g : Algebraic.SL n k) (p : Algebraic.CoordinatePolynomial n k) :
    Algebraic.evaluateMatrix ι x (rightTranslate (g : Matrix (Fin n) (Fin n) k) p) =
      Algebraic.evaluateMatrix ι (x * Matrix.SpecialLinearGroup.map ι g) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [Algebraic.evaluateMatrix]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p ij hp =>
      rcases ij with ⟨i, j⟩
      simp only [map_mul]
      rw [hp]
      congr 1
      simp [Algebraic.evaluateMatrix, Matrix.mul_apply]

theorem rightTranslate_inverse_left {k : Type} [Field k] {n : ℕ}
    (g : Algebraic.SL n k) (p : Algebraic.CoordinatePolynomial n k) :
    rightTranslate ((g⁻¹ : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k)
      (rightTranslate (g : Matrix (Fin n) (Fin n) k) p) = p := by
  have hm := congrArg (fun f : Algebraic.CoordinatePolynomial n k →ₐ[k] Algebraic.CoordinatePolynomial n k => f p)
    (rightTranslate_mul ((g⁻¹ : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k)
      (g : Matrix (Fin n) (Fin n) k))
  simpa only [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, rightTranslate_one, AlgHom.id_apply,
    AlgHom.comp_apply] using hm.symm

def rightTranslateEquiv {k : Type} [Field k] {n : ℕ} (g : Algebraic.SL n k) :
    Algebraic.CoordinatePolynomial n k ≃ₐ[k] Algebraic.CoordinatePolynomial n k where
  toFun := rightTranslate (g : Matrix (Fin n) (Fin n) k)
  invFun := rightTranslate ((g⁻¹ : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k)
  left_inv := rightTranslate_inverse_left g
  right_inv p := by simpa only [inv_inv] using rightTranslate_inverse_left g⁻¹ p
  map_mul' := map_mul _
  map_add' := map_add _
  commutes' := (rightTranslate (g : Matrix (Fin n) (Fin n) k)).commutes

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.PolynomialAction.Construction
