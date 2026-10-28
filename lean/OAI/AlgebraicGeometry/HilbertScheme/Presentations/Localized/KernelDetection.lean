import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Module.LocalizedModule.Submodule

/-! # Kernel Detection -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.KernelDetection

noncomputable section

/-! The localization of a linear map is injective exactly when the
localization of its actual kernel is zero. -/

universe u v w
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

theorem localizedMap_injective_iff_subsingleton_kernel (S : Submonoid R) (f : M →ₗ[R] N) :
    Function.Injective (LocalizedModule.map S f) ↔ Subsingleton (LocalizedModule S f.ker) := by
  have hex : Function.Exact f.ker.subtype f := by
    intro m
    constructor
    · intro hm
      exact ⟨⟨m, hm⟩, rfl⟩
    · rintro ⟨z, rfl⟩
      exact z.property
  have he := LocalizedModule.map_exact S f.ker.subtype f hex
  constructor
  · intro h
    apply subsingleton_of_forall_eq 0
    intro z
    apply LocalizedModule.map_injective S f.ker.subtype f.ker.subtype_injective
    rw [map_zero]
    apply h
    rw [map_zero]
    exact (he _).mpr ⟨z, rfl⟩
  · intro h
    let := h
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro m hm
    obtain ⟨z, rfl⟩ := (he m).mp hm
    rw [Subsingleton.elim z 0, map_zero]
    exact Submodule.zero_mem _

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.KernelDetection
