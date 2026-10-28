import Mathlib

/-! # Eighth Phase Subgroup -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.EighthPhaseSubgroup.Realization

noncomputable section

/-! The eighth-root stabilizer of a vector is a subgroup. -/

def eighthPhaseStabilizer {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : G →* (V ≃ₗ[ℂ] V)) (f : V) : Subgroup G where
  carrier := {g | ∃ ξ : ℂ, ξ ^ 8 = 1 ∧ ρ g f = ξ • f}
  one_mem' := ⟨1, by norm_num, by simp⟩
  mul_mem' := by
    rintro g h ⟨ξ, hξ, hg⟩ ⟨η, hη, hh⟩
    refine ⟨ξ * η, by rw [mul_pow, hξ, hη, mul_one], ?_⟩
    rw [map_mul]
    change ρ g (ρ h f) = _
    rw [hh, map_smul, hg, smul_smul, mul_comm]
  inv_mem' := by
    rintro g ⟨ξ, hξ, hg⟩
    have hne : ξ ≠ 0 := by
      intro hz
      rw [hz, zero_pow (by decide)] at hξ
      exact zero_ne_one hξ
    refine ⟨ξ⁻¹, by rw [inv_pow, hξ, inv_one], ?_⟩
    rw [map_inv]
    change (ρ g).symm f = ξ⁻¹ • f
    apply (ρ g).injective
    rw [(ρ g).apply_symm_apply, map_smul, hg, smul_smul, inv_mul_cancel₀ hne, one_smul]

end

end OAI.RepresentationTheory.Hecke.RadialDilation.EighthPhaseSubgroup.Realization
