import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ModuleSupportAnnihilation
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! # Supported Regular Module Vanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SupportedRegularModuleVanishing

noncomputable section

/-! A finite module supported where a regular scalar vanishes must be zero. The same criterion applies to finite submodules of flat modules over a Noetherian ring. -/
universe u v
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

theorem regular_power_smul_eq_zero {r : R} (hreg : IsSMulRegular M r)
    (n : ℕ) (x : M) (hx : r ^ n • x = 0) : x = 0 := by
  induction n with
  | zero => simpa only [pow_zero, one_smul] using hx
  | succ n ih =>
    apply ih
    apply hreg.right_eq_zero_of_smul
    simpa only [pow_succ', mul_smul] using hx

theorem finiteSupportedModule_subsingleton_of_regularElement
    [IsNoetherianRing R] [Module.Finite R M]
    (I : Ideal R) (hSupport : Module.support R M ⊆ PrimeSpectrum.zeroLocus (I : Set R))
    (r : R) (hr : r ∈ I) (hreg : IsSMulRegular M r) : Subsingleton M := by
  obtain ⟨n, hn⟩ := HilbertConstruction.Finite.ModuleSupportAnnihilation.finiteModule_support_subset_exists_power_annihilating I hSupport
  have hz (x : M) : x = 0 :=
    regular_power_smul_eq_zero hreg n x (hn (r ^ n) (Ideal.pow_mem_pow hr n) x)
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

theorem finiteFlatSubmodule_subsingleton_of_supported_regularElement
    [IsNoetherianRing R] [Module.Finite R M] [Module.Flat R M]
    (N : Submodule R M) (I : Ideal R)
    (hSupport : Module.support R N ⊆ PrimeSpectrum.zeroLocus (I : Set R))
    (r : R) (hr : r ∈ I) (hreg : IsSMulRegular R r) : Subsingleton N := by
  have hM : IsSMulRegular M r :=
    ((TensorProduct.rid R M).isSMulRegular_congr r).mp (hreg.lTensor M)
  exact finiteSupportedModule_subsingleton_of_regularElement I hSupport r hr (hM.submodule N r)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SupportedRegularModuleVanishing
