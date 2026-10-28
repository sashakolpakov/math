import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-! # Exterior Power Congr -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ExteriorPowerCongr.ExteriorBaseChange

noncomputable section

/-! Linear equivalences induce the canonical equivalence of exterior powers. -/

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N]

def powerCongr (n : ℕ) (e : M ≃ₗ[R] N) : ⋀[R]^n M ≃ₗ[R] ⋀[R]^n N :=
  LinearEquiv.ofBijective (exteriorPower.map n e.toLinearMap)
    ⟨exteriorPower.map_injective e.symm.toLinearMap (by
      ext x
      exact e.symm_apply_apply x), exteriorPower.map_surjective e.surjective⟩

theorem powerCongr_ιMulti (n : ℕ) (e : M ≃ₗ[R] N) (v : Fin n → M) :
    powerCongr n e (exteriorPower.ιMulti R n v) = exteriorPower.ιMulti R n (fun i => e (v i)) :=
  exteriorPower.map_apply_ιMulti e.toLinearMap v

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ExteriorPowerCongr.ExteriorBaseChange
