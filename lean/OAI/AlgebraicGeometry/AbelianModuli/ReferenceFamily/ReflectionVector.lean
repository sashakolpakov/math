import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.Reflection
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

/-! # Reflection Vector -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReflectionVector

noncomputable section

/-! An actual Hermitian reflection moves equal-norm vectors with a
symmetric cross pairing. Over the complex numbers, a constructed unit
phase always gives a nonisotropic reflection vector for negative unit
vectors. -/

section General

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (σ : k →+* k) (B : V →ₗ[k] V →ₛₗ[σ] k)

theorem hermitianReflection_sub_apply (x y : V)
    (hdiag : B x x = B y y) (hcross : B x y = B y x)
    (hv : B (x - y) (x - y) ≠ 0) :
    Hermitian.Reflection.hermitianReflection σ B (x - y) hv x = y := by
  have hc : 2 * B x (x - y) = B (x - y) (x - y) := by
    simp only [map_sub, LinearMap.sub_apply]
    rw [hdiag, hcross]
    ring
  change x - (2 * (B x (x - y) / B (x - y) (x - y))) • (x - y) = y
  rw [← mul_div_assoc, hc, div_self hv, one_smul]
  abel

end General

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] ℂ)

theorem exists_reflection_between_negative_unit_vectors
    (hB : ∀ x y, B x y = star (B y x)) (x y : V)
    (hx : B x x = -1) (hy : B y y = -1) :
    ∃ u : ℂ, ‖u‖ = 1 ∧
      ∃ (v : V) (hv : B v v ≠ 0),
        Hermitian.Reflection.hermitianReflection (starRingEnd ℂ) B v hv x = u • y := by
  obtain ⟨c, hc, hcz⟩ := Complex.exists_norm_eq_mul_self (B x y)
  let u := star c
  have hu : ‖u‖ = 1 := by simpa [u] using hc
  have hleft (a : ℂ) (z : V) : B (a • y) z = a * B y z := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  have hright (z : V) (a : ℂ) : B z (a • y) = star a * B z y :=
    (B z).map_smul' a y
  have hp : B x (u • y) = (‖B x y‖ : ℂ) := by
    rw [hright]
    change star (star c) * B x y = (‖B x y‖ : ℂ)
    rw [star_star]
    exact hcz.symm
  have huu : u * star u = 1 := by
    simpa [hu] using Complex.mul_conj' u
  have hyy : B (u • y) (u • y) = -1 := by
    rw [hleft, hright, hy, ← mul_assoc, huu, one_mul]
  have hyx : B (u • y) x = (‖B x y‖ : ℂ) := by
    rw [hB (u • y) x, hp]
    simp
  let v := x - u • y
  have hq : B v v = -2 - 2 * (‖B x y‖ : ℂ) := by
    dsimp only [v]
    simp only [map_sub, LinearMap.sub_apply, hx, hyy, hp, hyx]
    ring
  have hv : B v v ≠ 0 := by
    intro hz
    have hr := congrArg Complex.re (hq.symm.trans hz)
    simp at hr
    linarith [norm_nonneg (B x y)]
  refine ⟨u, hu, v, hv, ?_⟩
  exact hermitianReflection_sub_apply (starRingEnd ℂ) B x (u • y)
    (hx.trans hyy.symm) (hp.trans hyx.symm) hv

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReflectionVector
