import Mathlib.Tactic.Abel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.VectorKernelFiniteGeneration
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Exponent Finite Generation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.ExponentFiniteGeneration

noncomputable section

/-! Exponents of determinant monomials with equal degree in every
marked-point coordinate block form a finitely generated additive monoid. -/
open scoped BigOperators Classical
universe u v
variable {κ : Type u} [Fintype κ] {ι : Type v}

def monomialMultiDegree (w : κ → ι → ℕ) (a : κ → ℕ) (i : ι) : ℕ :=
  ∑ k, a k * w k i

theorem monomialMultiDegree_add (w : κ → ι → ℕ) (a b : κ → ℕ) (i : ι) :
    monomialMultiDegree w (a + b) i = monomialMultiDegree w a i + monomialMultiDegree w b i := by
  simp only [monomialMultiDegree, Pi.add_apply, add_mul, Finset.sum_add_distrib]

def degreeBalanceHom (w : κ → ι → ℕ) : (κ → ℕ) →+ (ι × ι → ℤ) where
  toFun a ij := (monomialMultiDegree w a ij.1 : ℤ) - monomialMultiDegree w a ij.2
  map_zero' := by
    funext ij
    simp only [monomialMultiDegree, Pi.zero_apply, zero_mul, Finset.sum_const_zero, Nat.cast_zero, sub_self]
  map_add' a b := by
    funext ij
    change ((monomialMultiDegree w (a + b) ij.1 : ℕ) : ℤ) - monomialMultiDegree w (a + b) ij.2 = _
    rw [monomialMultiDegree_add, monomialMultiDegree_add, Nat.cast_add, Nat.cast_add]
    simp only [Pi.add_apply]
    abel

def balancedExponentMonoid (w : κ → ι → ℕ) : AddSubmonoid (κ → ℕ) :=
  AddMonoidHom.mker (degreeBalanceHom w)

theorem mem_balancedExponentMonoid_iff (w : κ → ι → ℕ) (a : κ → ℕ) :
    a ∈ balancedExponentMonoid w ↔ ∀ i j, monomialMultiDegree w a i = monomialMultiDegree w a j := by
  constructor
  · intro h i j
    have hzero : degreeBalanceHom w a = 0 := h
    have he := congrFun hzero (i, j)
    change (monomialMultiDegree w a i : ℤ) - monomialMultiDegree w a j = 0 at he
    exact Int.ofNat_inj.mp (sub_eq_zero.mp he)
  · intro h
    change degreeBalanceHom w a = 0
    funext ij
    change (monomialMultiDegree w a ij.1 : ℤ) - monomialMultiDegree w a ij.2 = 0
    rw [h ij.1 ij.2, sub_self]

theorem balancedExponentMonoid_fg (w : κ → ι → ℕ) : (balancedExponentMonoid w).FG :=
  VectorKernelFiniteGeneration.natVectorHomKernel_fg (degreeBalanceHom w)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.ExponentFiniteGeneration
