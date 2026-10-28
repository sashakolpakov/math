import OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.CupDegrees
import OAI.AlgebraicTopology.Products.Cup

/-! # Cup Algebra -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.CupAlgebra

noncomputable section

/-! Associativity and the constant-one unit of the native cosimplicial
Alexander–Whitney product, with degree transport made explicit. -/

open _root_.CategoryTheory
open scoped Simplicial

open OAI.AlgebraicTopology.Products.Cup

universe u

variable (A : CosimplicialObject CommRingCat.{u})

theorem cup_assoc {p q r : ℕ}
    (x : A.obj ⦋p⦌) (y : A.obj ⦋q⦌) (z : A.obj ⦋r⦌) :
    CupDegrees.degreeCast A (Nat.add_assoc p q r) (Cup.cup A (Cup.cup A x y) z) =
      Cup.cup A x (Cup.cup A y z) := by
  rw [CupDegrees.degreeCast_cup]
  simp only [Cup.cup, AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion, AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion, map_mul,
    ← CommRingCat.comp_apply, ← A.map_comp, AlgebraicTopology.Products.Cup.subinterval_comp,
    Nat.zero_add, Nat.add_zero, mul_assoc]

@[simp]
theorem one_cup {p : ℕ} (x : A.obj ⦋p⦌) :
    CupDegrees.degreeCast A (Nat.zero_add p) (Cup.cup A (1 : A.obj ⦋0⦌) x) = x := by
  rw [CupDegrees.degreeCast_cup]
  simp only [map_one, one_mul, AlgebraicTopology.Products.Cup.subinterval_zero_self, A.map_id, CommRingCat.id_apply]

@[simp]
theorem cup_one {p : ℕ} (x : A.obj ⦋p⦌) :
    Cup.cup A x (1 : A.obj ⦋0⦌) = x := by
  simp only [Cup.cup, AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion, AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion, map_one, mul_one]
  change A.map (SimplexCategory.subinterval 0 p (by omega : 0 + p ≤ p)) x = x
  rw [AlgebraicTopology.Products.Cup.subinterval_zero_self, A.map_id]
  rfl

@[simp]
theorem differential_one_zero : Cup.differential A 0 (1 : A.obj ⦋0⦌) = 0 := by
  simp [Cup.differential, Fin.sum_univ_two]

theorem complex_d_one_zero : (Cup.complex A).d 0 1 (1 : A.obj ⦋0⦌) = 0 := by
  rw [Cup.complex_d_apply, differential_one_zero]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.CupAlgebra
