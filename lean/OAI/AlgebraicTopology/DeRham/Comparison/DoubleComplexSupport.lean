import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections
import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexRows

/-! # Double Complex Support -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexSupport.DoubleComplex

noncomputable section

/-!
# Finite horizontal support in an actual total complex

These lemmas concern mathlib's coproduct totalization, with horizontal degree
first. They will be used to eliminate positive horizontal components by
subtracting genuine total boundaries.
-/

open _root_.CategoryTheory

universe u v

variable {R : Type u} [Ring R]
  (K : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

/-- An element of total degree `n` has no component above horizontal degree `m`. -/
def SupportedTo (n m : ℕ) (x : (K.total (ComplexShape.up ℕ)).X n) : Prop :=
  ∀ p q (h : p + q = n), m < p → DoubleComplexProjections.DoubleComplex.πTotal K p q n h x = 0

theorem supportedTo_degree (n : ℕ) (x : (K.total (ComplexShape.up ℕ)).X n) :
    SupportedTo K n n x := by
  intro p q h hp
  omega

theorem supportedTo_zero (n m : ℕ) :
    SupportedTo K n m 0 := by
  intro p q h _
  exact map_zero _

theorem SupportedTo.mono {n m k : ℕ} {x : (K.total (ComplexShape.up ℕ)).X n}
    (hx : SupportedTo K n m x) (hmk : m ≤ k) : SupportedTo K n k x := by
  intro p q h hp
  exact hx p q h (by omega)

theorem SupportedTo.add {n m : ℕ} {x y : (K.total (ComplexShape.up ℕ)).X n}
    (hx : SupportedTo K n m x) (hy : SupportedTo K n m y) :
    SupportedTo K n m (x + y) := by
  intro p q h hp
  rw [map_add, hx p q h hp, hy p q h hp, zero_add]

theorem SupportedTo.sub {n m : ℕ} {x y : (K.total (ComplexShape.up ℕ)).X n}
    (hx : SupportedTo K n m x) (hy : SupportedTo K n m y) :
    SupportedTo K n m (x - y) := by
  intro p q h hp
  rw [map_sub, hx p q h hp, hy p q h hp, sub_zero]

theorem project_iota_self (p q n : ℕ) (h : p + q = n) (x : (K.X p).X q) :
    DoubleComplexProjections.DoubleComplex.πTotal K p q n h (K.ιTotal (ComplexShape.up ℕ) p q n h x) = x :=
  ConcreteCategory.congr_hom (DoubleComplexProjections.DoubleComplex.iota_πTotal_self K p q n h) x

theorem project_iota_ne (a b p q n : ℕ) (hab : a + b = n) (hpq : p + q = n)
    (hne : (a, b) ≠ (p, q)) (x : (K.X a).X b) :
    DoubleComplexProjections.DoubleComplex.πTotal K p q n hpq (K.ιTotal (ComplexShape.up ℕ) a b n hab x) = 0 :=
  ConcreteCategory.congr_hom (DoubleComplexProjections.DoubleComplex.iota_πTotal_ne K a b p q n hab hpq hne) x

theorem supportedTo_iota (p q n : ℕ) (h : p + q = n) (x : (K.X p).X q) :
    SupportedTo K n p (K.ιTotal (ComplexShape.up ℕ) p q n h x) := by
  intro a b hab ha
  exact project_iota_ne K p q a b n h hab (by
    intro heq
    have := Prod.mk.inj heq
    omega) x

/-- If only the zeroth column is present, the element is its zeroth-column inclusion. -/
theorem SupportedTo.eq_iota_zero {n : ℕ} {x : (K.total (ComplexShape.up ℕ)).X n}
    (hx : SupportedTo K n 0 x) :
    x = K.ιTotal (ComplexShape.up ℕ) 0 n n (by simp)
      (DoubleComplexProjections.DoubleComplex.πTotal K 0 n n (by simp) x) := by
  apply DoubleComplexProjections.DoubleComplex.total_element_ext K n
  intro p q hpq
  by_cases hp : p = 0
  · subst p
    have hq : q = n := by omega
    subst q
    exact (project_iota_self K 0 n n (by simp) _).symm
  · rw [hx p q hpq (Nat.pos_of_ne_zero hp)]
    exact (project_iota_ne K 0 n p q n (by simp) hpq (by
      intro heq
      exact hp (Prod.mk.inj heq).1.symm) _).symm

/-- Subtracting a boundary does not change the next differential. -/
theorem differential_sub_boundary (n : ℕ)
    (x : (K.total (ComplexShape.up ℕ)).X (n + 1))
    (y : (K.total (ComplexShape.up ℕ)).X n) :
    (K.total (ComplexShape.up ℕ)).d (n + 1) (n + 2)
        (x - (K.total (ComplexShape.up ℕ)).d n (n + 1) y) =
      (K.total (ComplexShape.up ℕ)).d (n + 1) (n + 2) x := by
  rw [map_sub]
  have hz := ConcreteCategory.congr_hom
    ((K.total (ComplexShape.up ℕ)).d_comp_d n (n + 1) (n + 2)) y
  change (K.total (ComplexShape.up ℕ)).d (n + 1) (n + 2)
      ((K.total (ComplexShape.up ℕ)).d n (n + 1) y) = 0 at hz
  rw [hz, sub_zero]

end

end OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexSupport.DoubleComplex
