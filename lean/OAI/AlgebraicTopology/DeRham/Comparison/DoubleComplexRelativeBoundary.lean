import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexSigns

/-! # Double Complex Relative Boundary -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexRelativeBoundary.DoubleComplex

/-!
# Relative cycles and subtraction of relative boundaries

These are elementwise identities for actual module cochain maps. They are
the elementary algebra behind the comparison of total complexes, and apply
without any exactness or quasi-isomorphism hypothesis.
-/

open _root_.CategoryTheory

universe u v w

/-- Every sign occurring in the total differential acts as an involution. -/
theorem sign_zsmul_involutive {V : Type w} [AddCommGroup V] (p : ℕ) :
    Function.Involutive (fun x : V => ((-1 : ℤ) ^ p) • x) := by
  intro x
  change ((-1 : ℤ) ^ p) • (((-1 : ℤ) ^ p) • x) = x
  rw [smul_smul, ← mul_pow]
  simp

theorem sign_zsmul_eq_zero_iff {V : Type w} [AddCommGroup V] (p : ℕ) (x : V) :
    ((-1 : ℤ) ^ p) • x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have h := congrArg (fun y : V => ((-1 : ℤ) ^ p) • y) hx
    simpa only [sign_zsmul_involutive p x, smul_zero] using h
  · rintro rfl
    exact smul_zero _

variable {R : Type u} [Ring R]
  {C D : CochainComplex (ModuleCat.{v} R) ℕ} (f : C ⟶ D)

/-- Subtracting a relative boundary preserves both equations of a relative
cycle. The incoming predecessor is allowed to be zero at the endpoint. -/
theorem relative_cycle_sub_boundary (n : ℕ)
    (x : C.X (n + 1)) (y : D.X n) (a : C.X n) (b : D.X n.pred)
    (hx : C.d (n + 1) (n + 2) x = 0)
    (hxy : f.f (n + 1) x = D.d n (n + 1) y) :
    C.d (n + 1) (n + 2) (x - C.d n (n + 1) a) = 0 ∧
      f.f (n + 1) (x - C.d n (n + 1) a) =
        D.d n (n + 1) (y - f.f n a + D.d n.pred n b) := by
  have hC := ConcreteCategory.congr_hom (C.d_comp_d n (n + 1) (n + 2)) a
  have hD := ConcreteCategory.congr_hom (D.d_comp_d n.pred n (n + 1)) b
  have hf := ConcreteCategory.congr_hom (f.comm n (n + 1)) a
  change C.d (n + 1) (n + 2) (C.d n (n + 1) a) = 0 at hC
  change D.d n (n + 1) (D.d n.pred n b) = 0 at hD
  change D.d n (n + 1) (f.f n a) = f.f (n + 1) (C.d n (n + 1) a) at hf
  constructor
  · rw [map_sub, hx, hC, sub_zero]
  · rw [map_sub, map_add, map_sub, hxy, hf, hD, add_zero]

/-- Primitives for the reduced relative cycle combine with the subtracted
primitive to give a primitive for the original pair. -/
theorem relative_boundary_add (n : ℕ)
    (x : C.X (n + 1)) (y : D.X n)
    (a a' : C.X n) (b b' : D.X n.pred)
    (hx : x - C.d n (n + 1) a = C.d n (n + 1) a')
    (hy : y - f.f n a + D.d n.pred n b = f.f n a' - D.d n.pred n b') :
    x = C.d n (n + 1) (a' + a) ∧
      y = f.f n (a' + a) - D.d n.pred n (b' + b) := by
  constructor
  · rw [map_add, ← hx, sub_add_cancel]
  · calc
      y = (y - f.f n a + D.d n.pred n b) + f.f n a - D.d n.pred n b := by abel
      _ = (f.f n a' - D.d n.pred n b') + f.f n a - D.d n.pred n b := by rw [hy]
      _ = f.f n (a' + a) - D.d n.pred n (b' + b) := by
        rw [map_add, map_add]
        abel

end OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexRelativeBoundary.DoubleComplex
