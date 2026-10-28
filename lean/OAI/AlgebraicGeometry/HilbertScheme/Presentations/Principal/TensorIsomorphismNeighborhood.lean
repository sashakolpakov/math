import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Principal.LinearIsomorphismNeighborhood
import Mathlib.RingTheory.Localization.BaseChange

/-! # Tensor Isomorphism Neighborhood -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Principal.TensorIsomorphismNeighborhood

noncomputable section

/-! The principal-neighborhood isomorphism criterion in actual tensor
base-change coordinates, suitable for affine scheme pullbacks. -/

open TensorProduct

universe u v w t
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

theorem tensor_localization_bijective_iff (S : Submonoid R)
    (A : Type t) [CommRing A] [Algebra R A] [IsLocalization S A] (f : M →ₗ[R] N) :
    Function.Bijective (f.lTensor A) ↔ Function.Bijective (LocalizedModule.map S f) := by
  let i := TensorProduct.mk R A M 1
  let j := TensorProduct.mk R A N 1
  have he : IsLocalizedModule.map S i j f = f.lTensor A := by
    apply IsLocalizedModule.ext S i (IsLocalizedModule.map_units j)
    apply LinearMap.ext
    intro m
    rw [LinearMap.comp_apply, IsLocalizedModule.map_apply]
    rfl
  rw [← he]
  exact IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective i j

theorem exists_principalOpen_tensor_isomorphism (f : M →ₗ[R] N)
    [Module.Finite R f.ker] [Module.Finite R (N ⧸ f.range)]
    (p : PrimeSpectrum R)
    (hp : Function.Bijective (f.lTensor (Localization.AtPrime p.asIdeal))) :
    ∃ r ∉ p.asIdeal, Function.Bijective (f.lTensor (Localization.Away r)) := by
  obtain ⟨r, hr, hf⟩ := LinearIsomorphismNeighborhood.exists_principalOpen_linear_isomorphism f p
    ((tensor_localization_bijective_iff p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal) f).mp hp)
  exact ⟨r, hr, (tensor_localization_bijective_iff (Submonoid.powers r) (Localization.Away r) f).mpr hf⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Principal.TensorIsomorphismNeighborhood
