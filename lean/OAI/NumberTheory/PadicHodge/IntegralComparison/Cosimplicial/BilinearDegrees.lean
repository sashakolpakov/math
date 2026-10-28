import OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.BilinearCup

/-! # Bilinear Degrees -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.BilinearDegrees.Cup

noncomputable section

/-! Degree casts for bilinear Alexander–Whitney products. -/

open _root_.CategoryTheory
open scoped Simplicial

universe u v

variable {R : Type u} [CommRing R]
  (A B C : CosimplicialObject (ModuleCat.{v} R))

def degreeCast {m n : ℕ} (h : m = n) : A.obj ⦋m⦌ ≃ₗ[R] A.obj ⦋n⦌ :=
  h ▸ LinearEquiv.refl R (A.obj ⦋m⦌)

variable (μ : ∀ n : SimplexCategory, A.obj n →ₗ[R] B.obj n →ₗ[R] C.obj n)

theorem degreeCast_cup {p q n : ℕ} (h : p + q = n)
    (x : A.obj ⦋p⦌) (y : B.obj ⦋q⦌) :
    degreeCast C h (BilinearCup.cup A B C μ p q x y) =
      μ ⦋n⦌ (A.map (SimplexCategory.subinterval 0 p (by omega : 0 + p ≤ n)) x)
        (B.map (SimplexCategory.subinterval p q (by omega : p + q ≤ n)) y) := by
  subst n
  rfl

theorem differential_cup_cast
    (hμ : ∀ {m n : SimplexCategory} (f : m ⟶ n) (x : A.obj m) (y : B.obj m),
      C.map f (μ m x y) = μ n (A.map f x) (B.map f y))
    (p q : ℕ) (x : A.obj ⦋p⦌) (y : B.obj ⦋q⦌) :
    BilinearCup.differential C (p + q) (BilinearCup.cup A B C μ p q x y) =
      degreeCast C (by omega : (p + 1) + q = p + q + 1)
        (BilinearCup.cup A B C μ (p + 1) q (BilinearCup.differential A p x) y) +
      (-1 : ℤ) ^ p • degreeCast C (by omega : p + (q + 1) = p + q + 1)
        (BilinearCup.cup A B C μ p (q + 1) x (BilinearCup.differential B q y)) := by
  rw [BilinearCup.differential_cup A B C μ hμ, degreeCast_cup, degreeCast_cup]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.BilinearDegrees.Cup
