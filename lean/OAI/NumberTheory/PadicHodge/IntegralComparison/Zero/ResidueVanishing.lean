import Mathlib.RingTheory.Nakayama

/-! # Residue Vanishing -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Zero.ResidueVanishing

/-! A finite module vanishes when its actual residue module vanishes. -/

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [Module.Finite R M] [AddCommGroup N] [Module R N] [Subsingleton N]

theorem subsingleton (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson)
    (g : M →ₗ[R] N) (hk : LinearMap.ker g = I • (⊤ : Submodule R M)) : Subsingleton M := by
  have hz : LinearMap.ker g = ⊤ := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_top, iff_true]
    exact Subsingleton.elim _ _
  have hb : (⊤ : Submodule R M) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I ⊤ Module.Finite.fg_top (hz.symm.trans hk).le hI
  apply subsingleton_of_forall_eq 0
  intro x
  exact (Submodule.mem_bot R).mp (hb ▸ (Submodule.mem_top : x ∈ (⊤ : Submodule R M)))

end OAI.NumberTheory.PadicHodge.IntegralComparison.Zero.ResidueVanishing
