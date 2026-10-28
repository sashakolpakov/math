import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexSupport
import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexDifferential

/-! # Double Complex Normalization -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexNormalization.DoubleComplex

noncomputable section

/-!
# Finite elimination in a first-quadrant total complex

Exactness in positive horizontal degrees allows us to remove the rightmost
component by subtracting a total boundary. Iteration is finite in every total
degree. The conclusion is an actual equality in mathlib's total complex.
-/

open _root_.CategoryTheory

universe u v

variable {R : Type u} [Ring R]
  (K : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

/-- The rightmost component is a horizontal cycle if the next differential
is supported in the zeroth column. -/
theorem horizontal_component_closed (n p q : ℕ) (hpq : p + q = n)
    (x : (K.total (ComplexShape.up ℕ)).X n)
    (hx : DoubleComplexSupport.DoubleComplex.SupportedTo K n p x)
    (hd : DoubleComplexSupport.DoubleComplex.SupportedTo K (n + 1) 0 ((K.total (ComplexShape.up ℕ)).d n (n + 1) x)) :
    ((K.d p (p + 1)).f q) (DoubleComplexProjections.DoubleComplex.πTotal K p q n hpq x) = 0 := by
  cases q with
  | zero =>
    have h := ConcreteCategory.congr_hom
      (DoubleComplexDifferential.DoubleComplex.d_πTotal_succ_zero K p n (by omega)) x
    change DoubleComplexProjections.DoubleComplex.πTotal K (p + 1) 0 (n + 1) _
        ((K.total (ComplexShape.up ℕ)).d n (n + 1) x) =
      ((K.d p (p + 1)).f 0) (DoubleComplexProjections.DoubleComplex.πTotal K p 0 n _ x) at h
    rw [hd (p + 1) 0 _ (by omega)] at h
    exact h.symm
  | succ q =>
    have h := ConcreteCategory.congr_hom
      (DoubleComplexDifferential.DoubleComplex.d_πTotal_succ_succ K p q n (by omega)) x
    change DoubleComplexProjections.DoubleComplex.πTotal K (p + 1) (q + 1) (n + 1) _
        ((K.total (ComplexShape.up ℕ)).d n (n + 1) x) =
      ((K.d p (p + 1)).f (q + 1)) (DoubleComplexProjections.DoubleComplex.πTotal K p (q + 1) n _ x) +
        ((-1 : ℤ) ^ (p + 1)) •
          ((K.X (p + 1)).d q (q + 1) (DoubleComplexProjections.DoubleComplex.πTotal K (p + 1) q n _ x)) at h
    rw [hd (p + 1) (q + 1) _ (by omega),
      hx (p + 1) q _ (by omega), map_zero, smul_zero, add_zero] at h
    exact h.symm

/-- A primitive in the last occupied horizontal degree removes that degree
without creating any larger one. -/
theorem lower_support
    (hexact : ∀ p q : ℕ, (K.flip.X q).ExactAt (p + 1))
    (n m : ℕ) (hm : m ≤ n)
    (x : (K.total (ComplexShape.up ℕ)).X (n + 1))
    (hx : DoubleComplexSupport.DoubleComplex.SupportedTo K (n + 1) (m + 1) x)
    (hd : DoubleComplexSupport.DoubleComplex.SupportedTo K (n + 2) 0
      ((K.total (ComplexShape.up ℕ)).d (n + 1) (n + 2) x)) :
    ∃ y : (K.total (ComplexShape.up ℕ)).X n,
      DoubleComplexSupport.DoubleComplex.SupportedTo K (n + 1) m (x - (K.total (ComplexShape.up ℕ)).d n (n + 1) y) := by
  let q := n - m
  have hmq : m + q = n := Nat.add_sub_of_le hm
  have hmq' : (m + 1) + q = n + 1 := by omega
  have hc := horizontal_component_closed K (n + 1) (m + 1) q hmq' x hx hd
  obtain ⟨c, hc⟩ := DoubleComplexRows.DoubleComplex.row_primitive K m q (hexact m q)
    (DoubleComplexProjections.DoubleComplex.πTotal K (m + 1) q (n + 1) hmq' x) hc
  refine ⟨K.ιTotal (ComplexShape.up ℕ) m q n hmq c, ?_⟩
  intro a b hab ha
  rw [map_sub]
  by_cases hatop : a = m + 1
  · subst a
    have hb : b = q := by omega
    subst b
    have hproj := ConcreteCategory.congr_hom
      (DoubleComplexDifferential.DoubleComplex.iota_d_πTotal_horizontal K m q n hmq) c
    change DoubleComplexProjections.DoubleComplex.πTotal K (m + 1) q (n + 1) _
        ((K.total (ComplexShape.up ℕ)).d n (n + 1)
          (K.ιTotal (ComplexShape.up ℕ) m q n hmq c)) =
      ((K.d m (m + 1)).f q) c at hproj
    rw [hproj, hc, sub_self]
  · have habove : m + 1 < a := by omega
    rw [hx a b hab habove]
    have hproj := ConcreteCategory.congr_hom
      (DoubleComplexDifferential.DoubleComplex.iota_d_πTotal_ne K m q a b n hmq hab (by
        intro heq
        exact hatop (Prod.mk.inj heq).1.symm) (by
        intro heq
        have := (Prod.mk.inj heq).1
        omega)) c
    change DoubleComplexProjections.DoubleComplex.πTotal K a b (n + 1) hab
        ((K.total (ComplexShape.up ℕ)).d n (n + 1)
          (K.ιTotal (ComplexShape.up ℕ) m q n hmq c)) = 0 at hproj
    rw [hproj, sub_zero]

/-- Repeated elimination leaves a horizontal cycle in the zeroth column,
plus an actual total boundary. -/
theorem normalize_supported_succ
    (hexact : ∀ p q : ℕ, (K.flip.X q).ExactAt (p + 1))
    (n m : ℕ) (x : (K.total (ComplexShape.up ℕ)).X (n + 1))
    (hx : DoubleComplexSupport.DoubleComplex.SupportedTo K (n + 1) m x)
    (hd : DoubleComplexSupport.DoubleComplex.SupportedTo K (n + 2) 0
      ((K.total (ComplexShape.up ℕ)).d (n + 1) (n + 2) x)) :
    ∃ b : (K.X 0).X (n + 1), ((K.d 0 1).f (n + 1)) b = 0 ∧
      ∃ y : (K.total (ComplexShape.up ℕ)).X n,
        x = K.ιTotal (ComplexShape.up ℕ) 0 (n + 1) (n + 1) (by simp) b +
          (K.total (ComplexShape.up ℕ)).d n (n + 1) y := by
  induction m generalizing x with
  | zero =>
    refine ⟨DoubleComplexProjections.DoubleComplex.πTotal K 0 (n + 1) (n + 1) (by simp) x,
      horizontal_component_closed K (n + 1) 0 (n + 1) (by simp) x hx hd, 0, ?_⟩
    simpa only [map_zero, add_zero] using DoubleComplexSupport.DoubleComplex.SupportedTo.eq_iota_zero K hx
  | succ m ih =>
    by_cases hm : m ≤ n
    · obtain ⟨z, hz⟩ := lower_support K hexact n m hm x hx hd
      have hd' : DoubleComplexSupport.DoubleComplex.SupportedTo K (n + 2) 0
          ((K.total (ComplexShape.up ℕ)).d (n + 1) (n + 2)
            (x - (K.total (ComplexShape.up ℕ)).d n (n + 1) z)) := by
        rw [DoubleComplexSupport.DoubleComplex.differential_sub_boundary]
        exact hd
      obtain ⟨b, hb, y, hy⟩ := ih (x - (K.total (ComplexShape.up ℕ)).d n (n + 1) z) hz hd'
      refine ⟨b, hb, y + z, ?_⟩
      rw [map_add, ← add_assoc, ← hy]
      exact (sub_add_cancel x _).symm
    · exact ih x (DoubleComplexSupport.DoubleComplex.SupportedTo.mono K (DoubleComplexSupport.DoubleComplex.supportedTo_degree K (n + 1) x) (by omega)) hd

/-- In any nonnegative degree, a total cochain whose differential lies in
column zero is a horizontal cycle in column zero modulo a total boundary. -/
theorem normalize
    (hexact : ∀ p q : ℕ, (K.flip.X q).ExactAt (p + 1))
    (n : ℕ) (x : (K.total (ComplexShape.up ℕ)).X n)
    (hd : DoubleComplexSupport.DoubleComplex.SupportedTo K (n + 1) 0
      ((K.total (ComplexShape.up ℕ)).d n (n + 1) x)) :
    ∃ b : (K.X 0).X n, ((K.d 0 1).f n) b = 0 ∧
      ∃ y : (K.total (ComplexShape.up ℕ)).X n.pred,
        x = K.ιTotal (ComplexShape.up ℕ) 0 n n (by simp) b +
          (K.total (ComplexShape.up ℕ)).d n.pred n y := by
  cases n with
  | zero =>
    have hx := DoubleComplexSupport.DoubleComplex.supportedTo_degree K 0 x
    refine ⟨DoubleComplexProjections.DoubleComplex.πTotal K 0 0 0 rfl x,
      horizontal_component_closed K 0 0 0 rfl x hx hd, 0, ?_⟩
    simpa only [map_zero, add_zero] using DoubleComplexSupport.DoubleComplex.SupportedTo.eq_iota_zero K hx
  | succ n =>
    exact normalize_supported_succ K hexact n (n + 1) x
      (DoubleComplexSupport.DoubleComplex.supportedTo_degree K (n + 1) x) hd

end

end OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexNormalization.DoubleComplex
