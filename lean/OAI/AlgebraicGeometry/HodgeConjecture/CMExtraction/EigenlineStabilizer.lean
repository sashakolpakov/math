import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.Algebra.Group.Subgroup.Ker

/-! # Eigenline Stabilizer -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.EigenlineStabilizer.TestTransport

noncomputable section

/-! The subgroup preserving a specified vector up to a nonzero scalar. -/

open scoped Classical

variable {Γ K V : Type*} [Group Γ] [Field K] [AddCommGroup V] [Module K V]
  (ρ : Γ →* (V ≃ₗ[K] V)) (v : V)

def eigenlineStabilizer : Subgroup Γ where
  carrier := {g | ∃ c : Kˣ, ρ g v = (c : K) • v}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro a b ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c * d, ?_⟩
    rw [map_mul]
    change ρ a (ρ b v) = _
    rw [hd, map_smul, hc, smul_smul, Units.val_mul, mul_comm]
  inv_mem' := by
    rintro g ⟨c, hc⟩
    refine ⟨c⁻¹, ?_⟩
    rw [map_inv]
    change (ρ g).symm v = (c⁻¹ : Kˣ).val • v
    apply (ρ g).injective
    rw [LinearEquiv.apply_symm_apply, map_smul, hc, smul_smul]
    simp

theorem eigenlineStabilizer_of_scalar (g : Γ) (c : K) (hc : c ≠ 0)
    (h : ρ g v = c • v) : g ∈ eigenlineStabilizer ρ v :=
  ⟨Units.mk0 c hc, h⟩

theorem scalar_ne_zero_of_equiv (g : Γ) (hv : v ≠ 0) (c : K)
    (h : ρ g v = c • v) : c ≠ 0 := by
  intro hc
  rw [hc, zero_smul] at h
  exact hv ((ρ g).map_eq_zero_iff.mp h)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.EigenlineStabilizer.TestTransport
