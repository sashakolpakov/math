import Mathlib

/-! # Cauchy Kernel -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CauchyKernel.CM

noncomputable section

/-! Smooth dependence of the multivariable Cauchy kernel in the sup norm.
This supplies the regularity step for holomorphic quotient maps without
assuming that their derivatives are continuous. -/

open scoped Classical ContDiff

variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

def denominator (a : C(T, ℂ)) (z : ℂ) : C(T, ℂ) := a - ContinuousMap.const T z

omit [CompactSpace T] in
theorem denominator_isUnit (a : C(T, ℂ)) (z : ℂ) (h : ∀ t, a t ≠ z) :
    IsUnit (denominator a z) := by
  apply (ContinuousMap.isUnit_iff_forall_ne_zero _).mpr
  intro t
  exact sub_ne_zero.mpr (h t)

theorem inverse_denominator_contDiffAt (a : C(T, ℂ)) (z : ℂ)
    (h : ∀ t, a t ≠ z) :
    ContDiffAt ℂ ∞ (fun w => Ring.inverse (denominator a w)) z := by
  obtain ⟨u, hu⟩ := denominator_isUnit a z h
  have hi : ContDiffAt ℂ ∞ Ring.inverse (denominator a z) :=
    hu ▸ contDiffAt_ringInverse ℂ u
  have hk : ContDiffAt ℂ ∞ (ContinuousMap.const T : ℂ → C(T, ℂ)) z :=
    (show ℂ →L[ℂ] C(T, ℂ) from ContinuousLinearMap.const ℂ T).contDiff.contDiffAt
  exact hi.comp z (contDiffAt_const.sub hk)

omit [CompactSpace T] in
theorem inverse_denominator_apply (a : C(T, ℂ)) (z : ℂ)
    (h : ∀ t, a t ≠ z) (t : T) :
    Ring.inverse (denominator a z) t = (a t - z)⁻¹ := by
  obtain ⟨u, hu⟩ := denominator_isUnit a z h
  rw [← hu, Ring.inverse_unit]
  have he : (u.val t) * ((↑(u⁻¹) : C(T, ℂ)) t) = 1 := by
    exact congrArg (fun f : C(T, ℂ) => f t) u.val_inv
  have hz : u.val t = a t - z := congrArg (fun f : C(T, ℂ) => f t) hu
  rw [hz] at he
  apply mul_left_cancel₀ (sub_ne_zero.mpr (h t))
  rw [he, mul_inv_cancel₀ (sub_ne_zero.mpr (h t))]

/-- Applying a bounded integration operator to the double Cauchy kernel
gives a smooth function of both complex parameters simultaneously. -/
theorem double_kernel_contDiffAt
    (a b F : C(T, ℂ)) (integrate : C(T, ℂ) →L[ℂ] ℂ) (z : ℂ × ℂ)
    (ha : ∀ t, a t ≠ z.1) (hb : ∀ t, b t ≠ z.2) :
    ContDiffAt ℂ ∞ (fun w : ℂ × ℂ => integrate
      (Ring.inverse (denominator a w.1) * Ring.inverse (denominator b w.2) * F)) z := by
  apply integrate.contDiff.contDiffAt.comp z
  exact (((inverse_denominator_contDiffAt a z.1 ha).comp z contDiffAt_fst).mul
    ((inverse_denominator_contDiffAt b z.2 hb).comp z contDiffAt_snd)).mul contDiffAt_const

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CauchyKernel.CM
