import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.Reflection
import Mathlib

/-! # Quadratic Cancellation Eq -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.QuadraticCancellationEq.QuadraticCancellation

noncomputable section

/-! Cancellation of a nonzero one-dimensional quadratic summand over the
rationals. Reflections align the distinguished vectors before restricting
the given isometry to their orthogonal complements. -/

open QuadraticMap

variable {V W : Type*} [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W]

private def reflection (Q : QuadraticForm ℚ V) (v : V) (hv : Q v ≠ 0) :
    Q.IsometryEquiv Q where
  toLinearEquiv := Hermitian.Reflection.hermitianReflection (RingHom.id ℚ) (Q.associated) v
    (by simpa only [associated_eq_self_apply] using hv)
  map_app' x := by
    change Q (Hermitian.Reflection.hermitianReflection (RingHom.id ℚ) (Q.associated) v
      (by simpa only [associated_eq_self_apply] using hv) x) = Q x
    have h := Hermitian.Reflection.hermitianReflection_preserves (RingHom.id ℚ) (Q.associated)
      (fun x y => QuadraticMap.associated_isSymm ℚ Q x y) v
      (by simpa only [associated_eq_self_apply] using hv) x x
    simpa only [associated_eq_self_apply] using h

private theorem reflection_sub (Q : QuadraticForm ℚ V) (x y : V)
    (hxy : Q x = Q y) (hv : Q (x - y) ≠ 0) :
    reflection Q (x - y) hv x = y := by
  have hnorm : Q.associated (x - y) (x - y) =
      2 * (Q.associated x x - Q.associated x y) := by
    simp only [map_sub, LinearMap.sub_apply]
    rw [QuadraticMap.associated_isSymm ℚ Q y x, associated_eq_self_apply,
      associated_eq_self_apply, ← hxy]
    ring
  have hd : Q.associated (x - y) (x - y) ≠ 0 := by
    simpa only [associated_eq_self_apply] using hv
  have hc : 2 * (Q.associated x (x - y) /
      Q.associated (x - y) (x - y)) = 1 := by
    rw [map_sub, ← mul_div_assoc]
    exact (div_eq_one_iff_eq hd).2 hnorm.symm
  change x - (2 * (Q.associated x (x - y) /
    Q.associated (x - y) (x - y))) • (x - y) = y
  rw [hc, one_smul]
  abel

theorem exists_isometry_map (Q : QuadraticForm ℚ V) (x y : V)
    (hxy : Q x = Q y) (hx : Q x ≠ 0) :
    ∃ e : Q.IsometryEquiv Q, e x = y := by
  by_cases hv : Q (x - y) ≠ 0
  · exact ⟨reflection Q (x - y) hv, reflection_sub Q x y hxy hv⟩
  have hz : Q (x - y) = 0 := not_ne_iff.mp hv
  have hp : Q (x - -y) ≠ 0 := by
    intro hn
    have hm : Q (x - y) + Q (x + y) = 4 * Q x := by
      rw [← associated_eq_self_apply ℚ Q (x - y),
        ← associated_eq_self_apply ℚ Q (x + y)]
      simp only [map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply]
      rw [associated_eq_self_apply, associated_eq_self_apply, ← hxy]
      ring
    have hn' : Q (x + y) = 0 := by simpa only [sub_neg_eq_add] using hn
    rw [hz, hn'] at hm
    exact hx (by linarith)
  let e : Q.IsometryEquiv Q := reflection Q (x - -y) hp
  let neg : Q.IsometryEquiv Q :=
    { toLinearEquiv := LinearEquiv.neg ℚ
      map_app' := Q.map_neg }
  refine ⟨e.trans neg, ?_⟩
  have he : e x = -y := reflection_sub Q x (-y) (by simpa using hxy) hp
  change -(e x) = y
  rw [he, neg_neg]

/-- A scalar quadratic form, with its coefficient kept explicit. -/
def scalar (c : ℚ) : QuadraticForm ℚ ℚ := c • QuadraticMap.sq

@[simp] theorem scalar_apply (c x : ℚ) : scalar c x = c * x ^ 2 := by
  simp [scalar, QuadraticMap.sq_apply, pow_two]

private theorem fst_eq_zero (Q : QuadraticForm ℚ V) (R : QuadraticForm ℚ W)
    (c : ℚ) (hc : c ≠ 0)
    (e : ((scalar c).prod Q).IsometryEquiv ((scalar c).prod R))
    (he : e (1, 0) = (1, 0)) (x : V) : (e (0, x)).1 = 0 := by
  have h0 := e.map_app (0, x)
  have h1 := e.map_app ((1, 0) + (0, x))
  rw [map_add, he] at h1
  simp only [prod_apply, scalar_apply, zero_add, map_zero, add_zero, one_pow,
    mul_one, Prod.fst_add, Prod.snd_add] at h0 h1
  have hz : c * (e (0, x)).1 = 0 := by nlinarith [h0, h1]
  exact (mul_eq_zero.mp hz).resolve_left hc

theorem cancel_scalar (Q : QuadraticForm ℚ V) (R : QuadraticForm ℚ W)
    (c : ℚ) (hc : c ≠ 0)
    (h : ((scalar c).prod Q).Equivalent ((scalar c).prod R)) : Q.Equivalent R := by
  obtain ⟨e⟩ := h
  obtain ⟨r, hr⟩ := exists_isometry_map ((scalar c).prod R) (e (1, 0)) (1, 0)
    (by rw [e.map_app]; simp) (by rw [e.map_app]; simpa using hc)
  let f := e.trans r
  have hf : f (1, 0) = (1, 0) := hr
  have hfi : f.symm (1, 0) = (1, 0) := by
    rw [← hf, f.symm_apply_apply]
  have hf0 := fst_eq_zero Q R c hc f hf
  have hfi0 := fst_eq_zero R Q c hc f.symm hfi
  refine ⟨{
    toFun := fun x => (f (0, x)).2
    invFun := fun y => (f.symm (0, y)).2
    left_inv := by
      intro x
      have hpair : (0, (f (0, x)).2) = f (0, x) := by
        ext
        · exact (hf0 x).symm
        · rfl
      change (f.symm (0, (f (0, x)).2)).2 = x
      rw [hpair, f.symm_apply_apply]
    right_inv := by
      intro y
      have hpair : (0, (f.symm (0, y)).2) = f.symm (0, y) := by
        ext
        · exact (hfi0 y).symm
        · rfl
      change (f (0, (f.symm (0, y)).2)).2 = y
      rw [hpair, f.apply_symm_apply]
    map_add' := by
      intro x y
      have hpair : ((0 : ℚ), x + y) = (0, x) + (0, y) := by simp
      rw [hpair, map_add]
      rfl
    map_smul' := by
      intro a x
      have hpair : ((0 : ℚ), a • x) = a • (0, x) := by simp
      rw [hpair, map_smul]
      rfl
    map_app' := by
      intro x
      have h := f.map_app (0, x)
      simpa only [prod_apply, hf0 x, scalar_apply,
        zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add] using h }⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.QuadraticCancellationEq.QuadraticCancellation
