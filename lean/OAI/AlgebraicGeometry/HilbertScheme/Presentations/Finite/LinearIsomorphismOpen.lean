import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.KernelDetection
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Linear Isomorphism Open -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.LinearIsomorphismOpen

noncomputable section

/-! The isomorphism locus of a linear map with finite kernel and cokernel
is the complement of their supports and is therefore open. -/

open _root_.TopologicalSpace

universe u v w
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

theorem localizedLinearIsomorphismLocus_eq (f : M →ₗ[R] N) :
    {p : PrimeSpectrum R | Function.Bijective (LocalizedModule.map p.asIdeal.primeCompl f)} =
      (Module.support R f.ker ∪ Module.support R (N ⧸ f.range))ᶜ := by
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_union, not_or,
    Module.notMem_support_iff, Function.Bijective,
    Localized.KernelDetection.localizedMap_injective_iff_subsingleton_kernel,
    LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker]

theorem isOpen_localizedLinearIsomorphismLocus (f : M →ₗ[R] N)
    [Module.Finite R f.ker] [Module.Finite R (N ⧸ f.range)] :
    IsOpen {p : PrimeSpectrum R | Function.Bijective (LocalizedModule.map p.asIdeal.primeCompl f)} := by
  rw [localizedLinearIsomorphismLocus_eq, Module.support_eq_zeroLocus, Module.support_eq_zeroLocus]
  exact ((PrimeSpectrum.isClosed_zeroLocus _).union (PrimeSpectrum.isClosed_zeroLocus _)).isOpen_compl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.LinearIsomorphismOpen
