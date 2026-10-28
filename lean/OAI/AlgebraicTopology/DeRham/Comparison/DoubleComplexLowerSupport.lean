import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexSupport
import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexDifferential

/-! # Double Complex Lower Support -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexLowerSupport.DoubleComplex

noncomputable section

/-!
# Lower horizontal support in an actual total complex

These statements use the native coproduct totalization. A lower support bound
records the vanishing of all columns to its left. At the first possible column,
the horizontal term of the total differential vanishes, leaving the signed
vertical differential.
-/

open _root_.CategoryTheory

universe u v

variable {R : Type u} [Ring R]
  (K : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

/-- An element of total degree `n` has no component below horizontal degree `m`. -/
def SupportedFrom (n m : ℕ) (x : (K.total (ComplexShape.up ℕ)).X n) : Prop :=
  ∀ p q (h : p + q = n), p < m → DoubleComplexProjections.DoubleComplex.πTotal K p q n h x = 0

theorem supportedFrom_zero (n m : ℕ) : SupportedFrom K n m 0 := by
  intro p q h _
  exact map_zero _

/-- The zero lower bound imposes no restriction. -/
theorem supportedFrom_zero_degree (n : ℕ) (x : (K.total (ComplexShape.up ℕ)).X n) :
    SupportedFrom K n 0 x := by
  intro p q h hp
  omega

theorem SupportedFrom.mono {n m k : ℕ} {x : (K.total (ComplexShape.up ℕ)).X n}
    (hx : SupportedFrom K n m x) (hkm : k ≤ m) : SupportedFrom K n k x := by
  intro p q h hp
  exact hx p q h (by omega)

theorem SupportedFrom.add {n m : ℕ} {x y : (K.total (ComplexShape.up ℕ)).X n}
    (hx : SupportedFrom K n m x) (hy : SupportedFrom K n m y) :
    SupportedFrom K n m (x + y) := by
  intro p q h hp
  rw [map_add, hx p q h hp, hy p q h hp, zero_add]

theorem SupportedFrom.sub {n m : ℕ} {x y : (K.total (ComplexShape.up ℕ)).X n}
    (hx : SupportedFrom K n m x) (hy : SupportedFrom K n m y) :
    SupportedFrom K n m (x - y) := by
  intro p q h hp
  rw [map_sub, hx p q h hp, hy p q h hp, sub_zero]

/-- In the first quadrant, no column above the total degree can occur. -/
theorem SupportedFrom.eq_zero {n : ℕ} {x : (K.total (ComplexShape.up ℕ)).X n}
    (hx : SupportedFrom K n (n + 1) x) : x = 0 := by
  apply DoubleComplexProjections.DoubleComplex.total_element_ext K n
  intro p q h
  rw [hx p q h (by omega), map_zero]

theorem supportedFrom_iota (p q n : ℕ) (h : p + q = n) (x : (K.X p).X q) :
    SupportedFrom K n p (K.ιTotal (ComplexShape.up ℕ) p q n h x) := by
  intro a b hab ha
  exact DoubleComplexSupport.DoubleComplex.project_iota_ne K p q a b n h hab (by
    intro heq
    have := (Prod.mk.inj heq).1
    omega) x

/-- A total differential never lowers horizontal degree. -/
theorem supportedFrom_d_iota (p q n : ℕ) (h : p + q = n) (x : (K.X p).X q) :
    SupportedFrom K (n + 1) p
      ((K.total (ComplexShape.up ℕ)).d n (n + 1)
        (K.ιTotal (ComplexShape.up ℕ) p q n h x)) := by
  intro a b hab ha
  exact DoubleComplexDifferential.DoubleComplex.project_d_iota_ne K p q a b n h hab (by
    intro heq
    have := (Prod.mk.inj heq).1
    omega) (by
    intro heq
    have := (Prod.mk.inj heq).1
    omega) x

/-- Vanishing of the first possible component raises the lower support bound. -/
theorem SupportedFrom.succ {n m : ℕ} {x : (K.total (ComplexShape.up ℕ)).X n}
    (hx : SupportedFrom K n m x) (q : ℕ) (h : m + q = n)
    (hz : DoubleComplexProjections.DoubleComplex.πTotal K m q n h x = 0) : SupportedFrom K n (m + 1) x := by
  intro p r hpr hp
  by_cases hpm : p = m
  · subst p
    have hr : r = q := by omega
    subst r
    exact hz
  · exact hx p r hpr (by omega)

/-- At the lowest supported column, only the signed vertical term survives. -/
theorem project_d_of_supportedFrom (p q n : ℕ) (h : p + q = n)
    (x : (K.total (ComplexShape.up ℕ)).X n) (hx : SupportedFrom K n p x) :
    DoubleComplexProjections.DoubleComplex.πTotal K p (q + 1) (n + 1) (by omega)
        ((K.total (ComplexShape.up ℕ)).d n (n + 1) x) =
      ((-1 : ℤ) ^ p) • (K.X p).d q (q + 1) (DoubleComplexProjections.DoubleComplex.πTotal K p q n h x) := by
  cases p with
  | zero =>
    simpa only [pow_zero, one_smul] using DoubleComplexDifferential.DoubleComplex.project_d_zero_succ K q n (by omega) x
  | succ p =>
    rw [DoubleComplexDifferential.DoubleComplex.project_d_succ_succ K p q n (by omega) x,
      hx p (q + 1) (by omega) (by omega), map_zero, zero_add]

end

end OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexLowerSupport.DoubleComplex
