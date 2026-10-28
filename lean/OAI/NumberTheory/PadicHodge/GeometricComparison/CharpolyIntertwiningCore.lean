import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-! # Charpoly Intertwining Core -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CharpolyIntertwiningCore.CharpolyIntertwining

noncomputable section

/-! An actual equivalence intertwining two operators identifies their characteristic polynomials. -/

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]

theorem charpoly (e : V ≃ₗ[K] W) (T : Module.End K V) (U : Module.End K W)
    (h : e.toLinearMap.comp T = U.comp e.toLinearMap) : T.charpoly = U.charpoly := by
  have he : e.conj T = U := by
    ext w
    change e (T (e.symm w)) = U w
    have hw := LinearMap.congr_fun h (e.symm w)
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using hw
  exact (e.charpoly_conj T).symm.trans (congrArg LinearMap.charpoly he)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CharpolyIntertwiningCore.CharpolyIntertwining
