import OAI.AlgebraicGeometry.HilbertScheme.Presentations.NilpotentModuleDetection
import Mathlib.RingTheory.Flat.Equalizer

/-! # Nilpotent Linear Map Lifting -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.NilpotentLinearMapLifting

noncomputable section

/-! A map which is surjective modulo a nilpotent ideal is surjective.
If its target is flat, bijectivity modulo that ideal lifts as well. -/

open TensorProduct

universe u v w
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

theorem nilpotent_surjective_of_reduction (I : Ideal R) (hI : IsNilpotent I)
    (f : M →ₗ[R] N) (hf : Function.Surjective (f.lTensor (R ⧸ I))) :
    Function.Surjective f := by
  let Q := N ⧸ f.range
  let q : N →ₗ[R] Q := f.range.mkQ
  have hq : Function.Surjective q := f.range.mkQ_surjective
  have hqf : q.comp f = 0 := by
    ext x
    exact (Submodule.Quotient.mk_eq_zero f.range).mpr ⟨x, rfl⟩
  have hz (z : (R ⧸ I) ⊗[R] Q) : z = 0 := by
    obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective (R ⧸ I) hq z
    obtain ⟨x, rfl⟩ := hf y
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hqf, LinearMap.lTensor_zero,
      LinearMap.zero_apply]
  let : Subsingleton ((R ⧸ I) ⊗[R] Q) := ⟨fun x y => (hz x).trans (hz y).symm⟩
  let : Subsingleton Q := NilpotentModuleDetection.nilpotent_quotientTensor_subsingleton Q I hI
  apply LinearMap.range_eq_top.mp
  exact Submodule.Quotient.subsingleton_iff.mp inferInstance

theorem nilpotent_bijective_of_reduction [Module.Flat R N]
    (I : Ideal R) (hI : IsNilpotent I) (f : M →ₗ[R] N)
    (hf : Function.Bijective (f.lTensor (R ⧸ I))) : Function.Bijective f := by
  have hs := nilpotent_surjective_of_reduction I hI f hf.2
  have hi := LinearMap.lTensor_injective_of_exact_of_flat f hs f.ker.subtype
    f.ker.subtype_injective (LinearMap.exact_subtype_ker_map f) (R ⧸ I)
  have hz (z : (R ⧸ I) ⊗[R] f.ker) : z = 0 := by
    apply hi
    rw [map_zero]
    apply hf.1
    rw [map_zero, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
      LinearMap.comp_ker_subtype, LinearMap.lTensor_zero, LinearMap.zero_apply]
  let : Subsingleton ((R ⧸ I) ⊗[R] f.ker) := ⟨fun x y => (hz x).trans (hz y).symm⟩
  let : Subsingleton f.ker := NilpotentModuleDetection.nilpotent_quotientTensor_subsingleton f.ker I hI
  refine ⟨(injective_iff_map_eq_zero f).mpr ?_, hs⟩
  intro x hx
  exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : f.ker) 0)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.NilpotentLinearMapLifting
