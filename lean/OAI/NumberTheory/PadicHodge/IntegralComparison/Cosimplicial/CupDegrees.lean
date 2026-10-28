import OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.Cup

/-! # Cup Degrees -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.CupDegrees

noncomputable section

/-! Degree transport for the native cosimplicial cup product. The
Leibniz rule is expressed using the actual cup operations in both terms. -/

open _root_.CategoryTheory
open scoped Simplicial

universe u

variable (A : CosimplicialObject CommRingCat.{u})

def degreeCast {m n : ℕ} (h : m = n) : A.obj ⦋m⦌ ≃+* A.obj ⦋n⦌ := by
  subst n
  exact RingEquiv.refl _

theorem degreeCast_subinterval {a p m n : ℕ} (h : m = n)
    (hm : a + p ≤ m) (hn : a + p ≤ n) (x : A.obj ⦋p⦌) :
    degreeCast A h (A.map (SimplexCategory.subinterval a p hm) x) =
      A.map (SimplexCategory.subinterval a p hn) x := by
  subst n
  rfl

theorem degreeCast_cup {p q n : ℕ} (h : p + q = n)
    (x : A.obj ⦋p⦌) (y : A.obj ⦋q⦌) :
    degreeCast A h (Cup.cup A x y) =
      A.map (SimplexCategory.subinterval 0 p (by omega : 0 + p ≤ n)) x *
        A.map (SimplexCategory.subinterval p q (by omega : p + q ≤ n)) y := by
  unfold Cup.cup AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion
  rw [map_mul, degreeCast_subinterval, degreeCast_subinterval]

theorem differential_cup_cast (p q : ℕ) (x : A.obj ⦋p⦌) (y : A.obj ⦋q⦌) :
    Cup.differential A (p + q) (Cup.cup A x y) =
      degreeCast A (by omega : (p + 1) + q = p + q + 1)
        (Cup.cup A (Cup.differential A p x) y) +
      (-1 : ℤ) ^ p • degreeCast A (by omega : p + (q + 1) = p + q + 1)
        (Cup.cup A x (Cup.differential A q y)) := by
  rw [Cup.differential_cup, degreeCast_cup, degreeCast_cup]

theorem differential_zsmul (n : ℕ) (r : ℤ) (x : A.obj ⦋n⦌) :
    Cup.differential A n (r • x) = r • Cup.differential A n x := by
  simp only [Cup.differential, map_zsmul, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]

theorem cup_zero_left {p q : ℕ} (y : A.obj ⦋q⦌) :
    Cup.cup A (0 : A.obj ⦋p⦌) y = 0 := by
  simp only [Cup.cup, map_zero, zero_mul]

theorem cup_zero_right {p q : ℕ} (x : A.obj ⦋p⦌) :
    Cup.cup A x (0 : A.obj ⦋q⦌) = 0 := by
  simp only [Cup.cup, map_zero, mul_zero]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.CupDegrees
