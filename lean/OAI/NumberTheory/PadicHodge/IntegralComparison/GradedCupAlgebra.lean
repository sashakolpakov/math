import OAI.NumberTheory.PadicHodge.IntegralComparison.GradedCupTransport
import Mathlib.Algebra.DirectSum.Algebra

/-! # Graded Cup Algebra -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.GradedCupAlgebra

noncomputable section

/-! Any family of actual modules with a unital associative graded cup
product has its direct-sum algebra. The package records only those
module structures, maps, and their explicit algebra laws. -/

open scoped DirectSum

universe u v

structure Data (R : Type u) [CommRing R] where
  H : ℕ → Type v
  [addCommGroup : ∀ n, AddCommGroup (H n)]
  [module : ∀ n, Module R (H n)]
  cup : ∀ i j, H i →ₗ[R] H j →ₗ[R] H (i + j)
  one : H 0
  one_cup : ∀ i (x : H i),
    GradedCupTransport.degreeCast R H (Nat.zero_add i) (cup 0 i one x) = x
  cup_one : ∀ i (x : H i), cup i 0 x one = x
  assoc : ∀ i j k (x : H i) (y : H j) (z : H k),
    GradedCupTransport.degreeCast R H (Nat.add_assoc i j k)
      (cup (i + j) k (cup i j x y) z) = cup i (j + k) x (cup j k y z)
  square_zero : ∀ x : H 1, cup 1 1 x x = 0

attribute [instance] Data.addCommGroup Data.module

variable {R : Type u} [CommRing R] (D : Data.{u,v} R)

theorem graded_eq_of_degreeCast {m n : ℕ} (h : m = n) (x : D.H m) (y : D.H n)
    (he : GradedCupTransport.degreeCast R D.H h x = y) :
    (GradedMonoid.mk m x : GradedMonoid D.H) = GradedMonoid.mk n y := by
  subst n
  exact congrArg (GradedMonoid.mk m) he

instance gradedMul : GradedMonoid.GMul D.H where
  mul := fun {i j} x y => D.cup i j x y

instance gradedOne : GradedMonoid.GOne D.H where
  one := D.one

instance gradedRing : DirectSum.GRing D.H where
  mul := fun {i j} x y => D.cup i j x y
  one := D.one
  mul_zero := fun {_ _} x => (D.cup _ _ x).map_zero
  zero_mul := by
    intro i j y
    exact DFunLike.congr_fun (D.cup i j).map_zero y
  mul_add := fun {_ _} x y z => (D.cup _ _ x).map_add y z
  add_mul := by
    intro i j x y z
    exact DFunLike.congr_fun ((D.cup i j).map_add x y) z
  one_mul := by
    rintro ⟨i, x⟩
    exact graded_eq_of_degreeCast D (Nat.zero_add i) _ _ (D.one_cup i x)
  mul_one := by
    rintro ⟨i, x⟩
    exact congrArg (GradedMonoid.mk i) (D.cup_one i x)
  mul_assoc := by
    rintro ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩
    exact graded_eq_of_degreeCast D (Nat.add_assoc i j k) _ _ (D.assoc i j k x y z)
  natCast := fun n => n • D.one
  natCast_zero := zero_nsmul _
  natCast_succ := fun n => by simp only [add_nsmul, one_nsmul]
  intCast := fun n => n • D.one
  intCast_ofNat := fun n => by simp
  intCast_negSucc_ofNat := fun n => by simp

instance gradedAlgebra : DirectSum.GAlgebra R D.H where
  toFun :=
    { toFun := fun r => r • D.one
      map_zero' := zero_smul _ _
      map_add' := fun r s => add_smul r s _ }
  map_one := one_smul _ _
  map_mul := by
    intro r s
    apply congrArg (GradedMonoid.mk 0)
    change (r * s) • D.one = D.cup 0 0 (r • D.one) (s • D.one)
    simp only [map_smul, LinearMap.smul_apply, D.cup_one, smul_smul]
    rw [mul_comm]
  commutes := by
    rintro r ⟨i, x⟩
    apply graded_eq_of_degreeCast D (Nat.zero_add i)
    change GradedCupTransport.degreeCast R D.H (Nat.zero_add i)
      (D.cup 0 i (r • D.one) x) = D.cup i 0 x (r • D.one)
    simp only [map_smul, LinearMap.smul_apply]
    rw [D.one_cup, D.cup_one]
  smul_def := by
    rintro r ⟨i, x⟩
    symm
    apply graded_eq_of_degreeCast D (Nat.zero_add i)
    change GradedCupTransport.degreeCast R D.H (Nat.zero_add i)
      (D.cup 0 i (r • D.one) x) = r • x
    simp only [map_smul, LinearMap.smul_apply]
    rw [D.one_cup]

abbrev total : Type v := ⨁ n : ℕ, D.H n

def inclusion (n : ℕ) : D.H n →ₗ[R] total D := DirectSum.lof R ℕ D.H n

def component (n : ℕ) : total D →ₗ[R] D.H n := DirectSum.component R ℕ D.H n

theorem inclusion_cup {i j : ℕ} (x : D.H i) (y : D.H j) :
    inclusion D (i + j) (D.cup i j x y) = inclusion D i x * inclusion D j y :=
  (DirectSum.of_mul_of x y).symm

theorem inclusion_one : inclusion D 0 D.one = 1 := rfl

theorem inclusion_square_zero (x : D.H 1) : inclusion D 1 x * inclusion D 1 x = 0 := by
  rw [← inclusion_cup, D.square_zero, map_zero]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.GradedCupAlgebra
