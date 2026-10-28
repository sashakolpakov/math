import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Diagonal Eigen -/

namespace OAI.RepresentationTheory.Theta.Geometric.DiagonalEigen

noncomputable section

/-! Simultaneous eigenspaces of a diagonal field action have precisely
the coordinates carrying that character. -/

open scoped Classical

variable {R k I : Type*} [Ring R] [Field k] (χ : I → R →+* k) (τ : R →+* k)

def diagonalEigenSpace : Submodule k (I → k) where
  carrier := {v | ∀ a i, χ i a * v i = τ a * v i}
  zero_mem' := by simp
  add_mem' := by
    intro u v hu hv a i
    change χ i a * (u i + v i) = τ a * (u i + v i)
    rw [mul_add, mul_add, hu a i, hv a i]
  smul_mem' := by
    intro c v hv a i
    change χ i a * (c * v i) = τ a * (c * v i)
    calc
      _ = c * (χ i a * v i) := by ring
      _ = c * (τ a * v i) := by rw [hv a i]
      _ = _ := by ring

theorem mem_diagonalEigenSpace (v : I → k) :
    v ∈ diagonalEigenSpace χ τ ↔ ∀ i, χ i ≠ τ → v i = 0 := by
  constructor
  · intro hv i hi
    by_contra hn
    apply hi
    apply RingHom.ext
    intro a
    exact mul_right_cancel₀ hn (hv a i)
  · intro hv a i
    by_cases hi : χ i = τ
    · rw [hi]
    · rw [hv i hi, mul_zero, mul_zero]

def diagonalEigenEquiv : ({i : I // χ i = τ} → k) ≃ₗ[k] diagonalEigenSpace χ τ where
  toFun v := ⟨fun i => if h : χ i = τ then v ⟨i, h⟩ else 0,
    (mem_diagonalEigenSpace χ τ _).mpr (by intro i hi; simp only [hi, ↓reduceDIte])⟩
  invFun v i := v.val i.val
  left_inv v := by funext i; simp only [i.property, ↓reduceDIte]
  right_inv v := by
    apply Subtype.ext
    funext i
    by_cases hi : χ i = τ
    · simp only [hi, ↓reduceDIte]
    · simpa only [hi, ↓reduceDIte] using
        ((mem_diagonalEigenSpace χ τ v.val).mp v.property i hi).symm
  map_add' u v := by
    apply Subtype.ext
    funext i
    by_cases hi : χ i = τ <;> simp [hi]
  map_smul' c v := by
    apply Subtype.ext
    funext i
    by_cases hi : χ i = τ <;> simp [hi]

theorem diagonalEigen_finrank [Fintype I] :
    Module.finrank k (diagonalEigenSpace χ τ) = Fintype.card {i : I // χ i = τ} := by
  rw [← (diagonalEigenEquiv χ τ).finrank_eq, Module.finrank_pi]

end

end OAI.RepresentationTheory.Theta.Geometric.DiagonalEigen
