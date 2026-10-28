import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.Action

/-! # Left Translation -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.LeftTranslation.Construction

noncomputable section

/-! Left translation of coordinate polynomials commutes with the
infinitesimal right action. -/

open scoped Classical
open _root_.MvPolynomial

def leftTranslate {k : Type} [Field k] {n : ℕ}
    (g : Matrix (Fin n) (Fin n) k) : Algebraic.CoordinatePolynomial n k →ₐ[k] Algebraic.CoordinatePolynomial n k :=
  MvPolynomial.aeval (fun ij : Fin n × Fin n => ∑ l, C (g ij.1 l) * X (l, ij.2))

@[simp] theorem leftTranslate_X {k : Type} [Field k] {n : ℕ}
    (g : Matrix (Fin n) (Fin n) k) (i j : Fin n) :
    leftTranslate g (X (i, j)) = ∑ l, C (g i l) * X (l, j) := by simp [leftTranslate]

@[simp] theorem leftTranslate_C {k : Type} [Field k] {n : ℕ}
    (g : Matrix (Fin n) (Fin n) k) (c : k) : leftTranslate g (C c) = C c := by
  simp [leftTranslate]

theorem leftTranslate_evaluate {k K : Type} [Field k] [Field K] {n : ℕ}
    (ι : k →+* K) (x : Algebraic.SL n K) (g : Algebraic.SL n k) (p : Algebraic.CoordinatePolynomial n k) :
    Algebraic.evaluateMatrix ι x (leftTranslate (g : Matrix (Fin n) (Fin n) k) p) =
      Algebraic.evaluateMatrix ι (Matrix.SpecialLinearGroup.map ι g * x) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [Algebraic.evaluateMatrix]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p ij hp =>
      rcases ij with ⟨i, j⟩
      simp only [map_mul]
      rw [hp]
      congr 1
      simp [Algebraic.evaluateMatrix, leftTranslate_X, Matrix.mul_apply]

theorem leftTranslate_mem_vanishingIdeal {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (g : Algebraic.SL n k) (hg : g ∈ G.subgroup k (RingHom.id k))
    (p : Algebraic.CoordinatePolynomial n k) (hp : p ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G) :
    leftTranslate (g : Matrix (Fin n) (Fin n) k) p ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G := by
  intro K _ ι x
  rw [leftTranslate_evaluate]
  have hm : Matrix.SpecialLinearGroup.map ι g ∈ G.subgroup K ι := by
    have h : Matrix.SpecialLinearGroup.map ι g ∈ G.subgroup K (ι.comp (RingHom.id k)) :=
      (G.map (RingHom.id k) ι ⟨g, hg⟩).property
    rwa [RingHom.comp_id] at h
  exact hp K ι ⟨Matrix.SpecialLinearGroup.map ι g * x.val, (G.subgroup K ι).mul_mem hm x.property⟩

theorem rightInfinitesimal_C_mul {k : Type} [Field k] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) k) (c : k) (p : Algebraic.CoordinatePolynomial n k) :
    Infinitesimal.Action.Construction.rightInfinitesimal A (C c * p) = C c * Infinitesimal.Action.Construction.rightInfinitesimal A p := by
  rw [Derivation.leibniz, Infinitesimal.Action.Construction.rightInfinitesimal_C, smul_zero, add_zero, smul_eq_mul]

theorem rightInfinitesimal_leftTranslate_X {k : Type} [Field k] {n : ℕ}
    (g A : Matrix (Fin n) (Fin n) k) (i j : Fin n) :
    Infinitesimal.Action.Construction.rightInfinitesimal A (leftTranslate g (X (i, j))) =
      leftTranslate g (Infinitesimal.Action.Construction.rightInfinitesimal A (X (i, j))) := by
  simp only [leftTranslate_X, Infinitesimal.Action.Construction.rightInfinitesimal_X, map_sum, rightInfinitesimal_C_mul,
    map_mul, leftTranslate_C, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro m _
  ring

theorem rightInfinitesimal_leftTranslate {k : Type} [Field k] {n : ℕ}
    (g A : Matrix (Fin n) (Fin n) k) (p : Algebraic.CoordinatePolynomial n k) :
    Infinitesimal.Action.Construction.rightInfinitesimal A (leftTranslate g p) = leftTranslate g (Infinitesimal.Action.Construction.rightInfinitesimal A p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p ij hp =>
      rcases ij with ⟨i, j⟩
      simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, hp,
        rightInfinitesimal_leftTranslate_X]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.LeftTranslation.Construction
