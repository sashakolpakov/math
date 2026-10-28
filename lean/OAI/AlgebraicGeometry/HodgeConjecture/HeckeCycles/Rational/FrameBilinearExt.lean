import Mathlib

/-! # Frame Bilinear Ext -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.FrameBilinearExt.CM

/-! Complex bilinear forms are determined on a specified rational frame.
The frame is an actual coordinate equivalence, with no density assumption. -/

open scoped Classical

variable {I U V : Type*} [Fintype I] [DecidableEq I]
  [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℂ V]
  (q : U ≃ₗ[ℚ] (I → ℚ)) (e : V ≃ₗ[ℂ] (I → ℂ)) (r : U → V)
  (hr : ∀ x, e (r x) = fun i => (q x i : ℂ))

include hr

omit [Fintype I] [DecidableEq I] in
theorem inverse_rational (x : I → ℚ) :
    e.symm (fun i => (x i : ℂ)) = r (q.symm x) := by
  apply e.injective
  rw [LinearEquiv.apply_symm_apply, hr, LinearEquiv.apply_symm_apply]

theorem ext (B D : LinearMap.BilinForm ℂ V)
    (h : ∀ x y, B (r x) (r y) = D (r x) (r y)) : B = D := by
  have hs (i : I) : (Pi.single i (1 : ℂ) : I → ℂ) =
      fun j => ((Pi.single i (1 : ℚ) : I → ℚ) j : ℂ) := by
    funext j
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  have heq : B.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap =
      D.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap := by
    apply (Pi.basisFun ℂ I).ext
    intro i
    apply (Pi.basisFun ℂ I).ext
    intro j
    simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, Pi.basisFun_apply, hs,
      inverse_rational q e r hr]
    exact h _ _
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  have hxy := LinearMap.congr_fun (LinearMap.congr_fun heq (e x)) (e y)
  simpa only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using hxy

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.FrameBilinearExt.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.FrameBilinearExt.CM.Linear

/-! Complex linear maps are determined on an actual rational frame. -/

open scoped Classical

variable {I U V W : Type*} [Fintype I] [DecidableEq I]
  [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]
  (q : U ≃ₗ[ℚ] (I → ℚ)) (e : V ≃ₗ[ℂ] (I → ℂ)) (r : U → V)
  (hr : ∀ x, e (r x) = fun i => (q x i : ℂ))

include hr in
theorem ext (A B : V →ₗ[ℂ] W) (h : ∀ x, A (r x) = B (r x)) : A = B := by
  have hs (i : I) : (Pi.single i (1 : ℂ) : I → ℂ) =
      fun j => ((Pi.single i (1 : ℚ) : I → ℚ) j : ℂ) := by
    funext j
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  have heq : A.comp e.symm.toLinearMap = B.comp e.symm.toLinearMap := by
    apply (Pi.basisFun ℂ I).ext
    intro i
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Pi.basisFun_apply, hs,
      inverse_rational q e r hr]
    exact h _
  apply LinearMap.ext
  intro x
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using
    LinearMap.congr_fun heq (e x)

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.FrameBilinearExt.CM.Linear

end

end OAI
