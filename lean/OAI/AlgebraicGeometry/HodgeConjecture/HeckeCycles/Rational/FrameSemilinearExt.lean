import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.FrameBilinearExt

/-! # Frame Semilinear Ext -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.FrameSemilinearExt.CM

noncomputable section

/-! Conjugate-linear maps are determined on the actual rational frame. -/

open scoped Classical

variable {I U V W : Type*} [Fintype I] [DecidableEq I]
  [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]
  (q : U ≃ₗ[ℚ] (I → ℚ)) (e : V ≃ₗ[ℂ] (I → ℂ)) (r : U → V)
  (hr : ∀ x, e (r x) = fun i => (q x i : ℂ))

include hr in
theorem ext (A B : V →ₗ⋆[ℂ] W) (h : ∀ x, A (r x) = B (r x)) : A = B := by
  have hs (i : I) : (Pi.single i (1 : ℂ) : I → ℂ) =
      fun j => ((Pi.single i (1 : ℚ) : I → ℚ) j : ℂ) := by
    funext j
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  have heq : A.comp e.symm.toLinearMap = B.comp e.symm.toLinearMap := by
    apply (Pi.basisFun ℂ I).ext
    intro i
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Pi.basisFun_apply, hs,
      FrameBilinearExt.CM.inverse_rational q e r hr]
    exact h _
  apply LinearMap.ext
  intro x
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using
    LinearMap.congr_fun heq (e x)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.FrameSemilinearExt.CM
