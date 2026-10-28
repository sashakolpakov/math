import OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.ModuleCupAlgebra
import Mathlib.Algebra.DirectSum.Algebra

/-! # Cohomology Ring -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.CohomologyRing

noncomputable section

/-! The direct sum of the actual cohomology modules carries the
Alexander–Whitney algebra structure. Its multiplication is the native
bilinear cup product on each pair of degrees. -/

open _root_.CategoryTheory
open scoped DirectSum Simplicial

open OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.ModuleComplex OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.ModuleCupAlgebra

universe u v

variable {R : Type u} [CommRing R] (A : CosimplicialObject (CommAlgCat.{v} R))

abbrev cohomology (n : ℕ) : Type v := (ModuleComplex.complex A).homology n

theorem graded_eq_of_degreeCast {m n : ℕ} (h : m = n)
    (x : cohomology A m) (y : cohomology A n) (he : ModuleCupAlgebra.cohomologyDegreeCast A h x = y) :
    (GradedMonoid.mk m x : GradedMonoid (cohomology A)) = GradedMonoid.mk n y := by
  subst n
  exact congrArg (GradedMonoid.mk m) he

instance gradedMul : GradedMonoid.GMul (cohomology A) where
  mul := fun {i j} x y => ModuleCup.cohomologyCup A i j x y

instance gradedOne : GradedMonoid.GOne (cohomology A) where
  one := ModuleCupAlgebra.cohomologyOne A

instance gradedRing : DirectSum.GRing (cohomology A) where
  mul := fun {i j} x y => ModuleCup.cohomologyCup A i j x y
  one := ModuleCupAlgebra.cohomologyOne A
  mul_zero := fun {_ _} x => (ModuleCup.cohomologyCup A _ _ x).map_zero
  zero_mul := by
    intro i j y
    exact DFunLike.congr_fun (ModuleCup.cohomologyCup A i j).map_zero y
  mul_add := fun {_ _} x y z => (ModuleCup.cohomologyCup A _ _ x).map_add y z
  add_mul := by
    intro i j x y z
    exact DFunLike.congr_fun ((ModuleCup.cohomologyCup A i j).map_add x y) z
  one_mul := by
    rintro ⟨i, x⟩
    exact graded_eq_of_degreeCast A (Nat.zero_add i) _ _ (ModuleCupAlgebra.cohomologyOne_cup A x)
  mul_one := by
    rintro ⟨i, x⟩
    exact congrArg (GradedMonoid.mk i) (ModuleCupAlgebra.cohomologyCup_one A x)
  mul_assoc := by
    rintro ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩
    exact graded_eq_of_degreeCast A (Nat.add_assoc i j k) _ _ (ModuleCupAlgebra.cohomologyCup_assoc A x y z)
  natCast := fun n => n • ModuleCupAlgebra.cohomologyOne A
  natCast_zero := zero_nsmul _
  natCast_succ := fun n => by simp only [add_nsmul, one_nsmul]
  intCast := fun n => n • ModuleCupAlgebra.cohomologyOne A
  intCast_ofNat := fun n => by simp
  intCast_negSucc_ofNat := fun n => by simp

instance gradedAlgebra : DirectSum.GAlgebra R (cohomology A) where
  toFun :=
    { toFun := fun r => r • ModuleCupAlgebra.cohomologyOne A
      map_zero' := zero_smul _ _
      map_add' := fun r s => add_smul r s _ }
  map_one := one_smul _ _
  map_mul := by
    intro r s
    apply congrArg (GradedMonoid.mk 0)
    change (r * s) • ModuleCupAlgebra.cohomologyOne A =
      ModuleCup.cohomologyCup A 0 0 (r • ModuleCupAlgebra.cohomologyOne A) (s • ModuleCupAlgebra.cohomologyOne A)
    simp only [map_smul, LinearMap.smul_apply, ModuleCupAlgebra.cohomologyCup_one, smul_smul]
    rw [mul_comm]
  commutes := by
    rintro r ⟨i, x⟩
    apply graded_eq_of_degreeCast A (Nat.zero_add i)
    change ModuleCupAlgebra.cohomologyDegreeCast A (Nat.zero_add i)
      (ModuleCup.cohomologyCup A 0 i (r • ModuleCupAlgebra.cohomologyOne A) x) = ModuleCup.cohomologyCup A i 0 x (r • ModuleCupAlgebra.cohomologyOne A)
    simp only [map_smul, LinearMap.smul_apply]
    rw [ModuleCupAlgebra.cohomologyOne_cup, ModuleCupAlgebra.cohomologyCup_one]
  smul_def := by
    rintro r ⟨i, x⟩
    symm
    apply graded_eq_of_degreeCast A (Nat.zero_add i)
    change ModuleCupAlgebra.cohomologyDegreeCast A (Nat.zero_add i)
      (ModuleCup.cohomologyCup A 0 i (r • ModuleCupAlgebra.cohomologyOne A) x) = r • x
    simp only [map_smul, LinearMap.smul_apply]
    rw [ModuleCupAlgebra.cohomologyOne_cup]

abbrev total : Type v := ⨁ n : ℕ, cohomology A n

def inclusion (n : ℕ) : cohomology A n →ₗ[R] total A :=
  DirectSum.lof R ℕ (cohomology A) n

def component (n : ℕ) : total A →ₗ[R] cohomology A n :=
  DirectSum.component R ℕ (cohomology A) n

theorem inclusion_cup {p q : ℕ} (x : cohomology A p) (y : cohomology A q) :
    inclusion A (p + q) (ModuleCup.cohomologyCup A p q x y) = inclusion A p x * inclusion A q y :=
  (DirectSum.of_mul_of x y).symm

theorem inclusion_one : inclusion A 0 (ModuleCupAlgebra.cohomologyOne A) = 1 := rfl

theorem inclusion_square_zero [Invertible (2 : A.obj ⦋1⦌)] [Invertible (2 : A.obj ⦋2⦌)]
    (x : cohomology A 1) : inclusion A 1 x * inclusion A 1 x = 0 := by
  rw [← inclusion_cup, ModuleCup.cup_self_eq_zero, map_zero]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.CohomologyRing
