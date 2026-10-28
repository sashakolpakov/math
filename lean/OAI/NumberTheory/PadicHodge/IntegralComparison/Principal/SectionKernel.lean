import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Section Kernel -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionKernel

/-! A principal localization turns an annihilator of the quotient
section kernel into the literal equality of the localized ideals. -/

universe u v w
variable {A : Type u} [CommRing A] {S : Type v} [CommRing S] [Algebra A S]
  {R : Type w} [CommRing R] (s : A) [IsLocalization.Away s S]
  (ε : A →+* R) (η : S →+* R) (hη : η.comp (algebraMap A S) = ε)
  (I : Ideal A) (hI : I ≤ RingHom.ker ε)
  (hs : ∀ x, ε x = 0 → s * x ∈ I)

include hI hs in
theorem map_kernel : (RingHom.ker ε).map (algebraMap A S) = I.map (algebraMap A S) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change algebraMap A S x ∈ I.map (algebraMap A S)
    have h := Ideal.mem_map_of_mem (algebraMap A S) (hs x hx)
    rw [map_mul] at h
    exact ((I.map (algebraMap A S)).unit_mul_mem_iff_mem
      (IsLocalization.Away.algebraMap_isUnit s)).mp h
  · exact Ideal.map_mono hI

include hη hI hs in
theorem kernel : RingHom.ker η = I.map (algebraMap A S) := by
  have h : (RingHom.ker η).under A = RingHom.ker ε := by
    change (RingHom.ker η).comap (algebraMap A S) = RingHom.ker ε
    rw [RingHom.comap_ker, hη]
  calc
    RingHom.ker η = ((RingHom.ker η).under A).map (algebraMap A S) :=
      (IsLocalization.map_under (Submonoid.powers s) S (RingHom.ker η)).symm
    _ = (RingHom.ker ε).map (algebraMap A S) := congrArg (Ideal.map (algebraMap A S)) h
    _ = I.map (algebraMap A S) := map_kernel s ε I hI hs

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionKernel
