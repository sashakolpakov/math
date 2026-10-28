import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexSigns
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Data.Finset.NatAntidiagonal

/-! # Double Complex Projections -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex

noncomputable section

/-!
# Projections from the actual total complex

The degree `n` object is mathlib's coproduct over pairs `p + q = n`.
The maps below use its universal property, and the finite antidiagonal gives
the identity as a sum of component projections followed by inclusions.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive
open scoped BigOperators

universe u v

variable {R : Type u} [Ring R]
  (K : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

/-- Projection from the actual total-complex coproduct to one of its summands. -/
def πTotal (p q n : ℕ) (_h : p + q = n) :
    (K.total (ComplexShape.up ℕ)).X n ⟶ (K.X p).X q :=
  K.totalDesc (fun a b _ =>
    if ha : a = p then
      if hb : b = q then (K.XXIsoOfEq _ _ _ ha hb).hom else 0
    else 0)

/-- Projection extended by zero when the component has the wrong total degree. -/
def πTotalOrZero (p q n : ℕ) :
    (K.total (ComplexShape.up ℕ)).X n ⟶ (K.X p).X q :=
  if h : p + q = n then πTotal K p q n h else 0

theorem πTotalOrZero_eq (p q n : ℕ) (h : p + q = n) :
    πTotalOrZero K p q n = πTotal K p q n h := by
  simp only [πTotalOrZero, dite_eq_left h]

theorem πTotalOrZero_eq_zero (p q n : ℕ) (h : p + q ≠ n) :
    πTotalOrZero K p q n = 0 := by
  simp only [πTotalOrZero, dite_eq_right h]

/-- The matching coproduct inclusion followed by projection is the identity. -/
@[reassoc (attr := simp)]
theorem iota_πTotal_self (p q n : ℕ) (h : p + q = n) :
    K.ιTotal (ComplexShape.up ℕ) p q n h ≫ πTotal K p q n h =
      𝟙 ((K.X p).X q) := by
  simp [πTotal]

/-- Distinct bidegrees have zero inclusion-projection composite. -/
@[reassoc]
theorem iota_πTotal_ne (a b p q n : ℕ) (hab : a + b = n) (hpq : p + q = n)
    (hne : (a, b) ≠ (p, q)) :
    K.ιTotal (ComplexShape.up ℕ) a b n hab ≫ πTotal K p q n hpq = 0 := by
  by_cases ha : a = p
  · subst a
    have hb : b ≠ q := by
      intro hb
      exact hne (by simp only [hb])
    simp [πTotal, hb]
  · simp [πTotal, ha]

@[reassoc (attr := simp)]
theorem iota_πTotalOrZero_self (p q n : ℕ) (h : p + q = n) :
    K.ιTotal (ComplexShape.up ℕ) p q n h ≫ πTotalOrZero K p q n =
      𝟙 ((K.X p).X q) := by
  rw [πTotalOrZero_eq K p q n h, iota_πTotal_self]

@[reassoc]
theorem iota_πTotalOrZero_ne (a b p q n : ℕ) (hab : a + b = n)
    (hne : (a, b) ≠ (p, q)) :
    K.ιTotal (ComplexShape.up ℕ) a b n hab ≫ πTotalOrZero K p q n = 0 := by
  by_cases hpq : p + q = n
  · rw [πTotalOrZero_eq K p q n hpq]
    exact iota_πTotal_ne K a b p q n hab hpq hne
  · rw [πTotalOrZero_eq_zero K p q n hpq, comp_zero]

/-- The finite sum of projection-inclusion composites is the identity of the
actual total-complex object. -/
theorem sum_πTotalOrZero_iota (n : ℕ) :
    (∑ pq ∈ Finset.antidiagonal n,
      πTotalOrZero K pq.1 pq.2 n ≫
        K.ιTotalOrZero (ComplexShape.up ℕ) pq.1 pq.2 n) =
      𝟙 ((K.total (ComplexShape.up ℕ)).X n) := by
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  rw [comp_sum, Category.comp_id]
  rw [Finset.sum_eq_single (p, q)]
  · rw [← Category.assoc, iota_πTotalOrZero_self K p q n hpq,
      Category.id_comp, K.ιTotalOrZero_eq (ComplexShape.up ℕ) p q n hpq]
  · intro ab _ hab
    rw [← Category.assoc,
      iota_πTotalOrZero_ne K p q ab.1 ab.2 n hpq (by simpa using hab.symm),
      zero_comp]
  · intro hnot
    exact False.elim (hnot (Finset.mem_antidiagonal.mpr hpq))

/-- Every element is reconstructed by its finitely many homogeneous components. -/
theorem sum_iota_πTotalOrZero_apply (n : ℕ) (x : (K.total (ComplexShape.up ℕ)).X n) :
    (∑ pq ∈ Finset.antidiagonal n,
      K.ιTotalOrZero (ComplexShape.up ℕ) pq.1 pq.2 n (πTotalOrZero K pq.1 pq.2 n x)) =
      x := by
  have h := congrArg (fun f : (K.total (ComplexShape.up ℕ)).X n ⟶
      (K.total (ComplexShape.up ℕ)).X n => f.hom x) (sum_πTotalOrZero_iota K n)
  simpa only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using h

/-- The component projections are jointly injective on elements. -/
theorem total_element_ext (n : ℕ) {x y : (K.total (ComplexShape.up ℕ)).X n}
    (h : ∀ p q (hpq : p + q = n), πTotal K p q n hpq x = πTotal K p q n hpq y) :
    x = y := by
  rw [← sum_iota_πTotalOrZero_apply K n x, ← sum_iota_πTotalOrZero_apply K n y]
  apply Finset.sum_congr rfl
  intro pq hpq
  have heq := Finset.mem_antidiagonal.mp hpq
  rw [πTotalOrZero_eq K pq.1 pq.2 n heq]
  exact congrArg (K.ιTotalOrZero (ComplexShape.up ℕ) pq.1 pq.2 n) (h pq.1 pq.2 heq)

/-- The component projections are also jointly monic as morphisms. -/
theorem total_hom_ext (n : ℕ) {M : ModuleCat.{v} R}
    {f g : M ⟶ (K.total (ComplexShape.up ℕ)).X n}
    (h : ∀ p q (hpq : p + q = n), f ≫ πTotal K p q n hpq = g ≫ πTotal K p q n hpq) :
    f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply total_element_ext K n
  intro p q hpq
  exact congrArg (fun t : M ⟶ (K.X p).X q => t x) (h p q hpq)

end

end OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex
