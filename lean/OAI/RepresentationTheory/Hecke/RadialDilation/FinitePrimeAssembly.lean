import OAI.RepresentationTheory.Hecke.RadialDilation.FinitePrimeProduct
import OAI.RepresentationTheory.Hecke.RadialDilation.FinitePowerSubgroup

/-! # Finite Prime Assembly -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.FinitePrimeAssembly.Realization

noncomputable section

/-! Assemble finite local powers with a fixed complementary symplectic subgroup. -/

open scoped Classical
open IsDedekindDomain

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem finitePrimePart_pow (g : Theta.PoissonAutomorphyNormalizationData.Sp ι Theta.PoissonAutomorphyNormalizationData.AQf) (v : HeightOneSpectrum ℤ) (N : ℕ) :
    FinitePrimeProduct.Realization.finitePrimePart (g ^ N) v = FinitePrimeProduct.Realization.finitePrimePart g v ^ N := by
  unfold FinitePrimeProduct.Realization.finitePrimePart
  rw [map_pow, map_pow]

theorem finite_prime_power_assembly (H : Subgroup (Theta.PoissonAutomorphyNormalizationData.Sp ι Theta.PoissonAutomorphyNormalizationData.AQf)) (g : Theta.PoissonAutomorphyNormalizationData.Sp ι Theta.PoissonAutomorphyNormalizationData.AQf)
    (S : Finset (HeightOneSpectrum ℤ))
    (htail : FiniteMaskedGenerators.Realization.finiteMaskSymplectic (S : Set (HeightOneSpectrum ℤ))ᶜ g ∈ H)
    (hlocal : ∀ v ∈ S, ∃ m : ℕ, 0 < m ∧ FinitePrimeProduct.Realization.finitePrimePart g v ^ m ∈ H) :
    ∃ N : ℕ, 0 < N ∧ g ^ N ∈ H := by
  obtain ⟨N, hN, hpow⟩ := FinitePowerSubgroup.Realization.common_positive_power_mem_subgroup H
    (fun v : S => FinitePrimeProduct.Realization.finitePrimePart g v.val) (fun v => hlocal v.val v.property)
  have hS : FiniteMaskedGenerators.Realization.finiteMaskSymplectic (S : Set (HeightOneSpectrum ℤ)) (g ^ N) ∈ H := by
    apply FinitePrimeProduct.Realization.finiteMaskSymplectic_mem_of_prime_parts
    intro v hv
    rw [finitePrimePart_pow]
    exact hpow ⟨v, hv⟩
  have htailN : FiniteMaskedGenerators.Realization.finiteMaskSymplectic (S : Set (HeightOneSpectrum ℤ))ᶜ (g ^ N) ∈ H := by
    rw [map_pow]
    exact H.pow_mem htail N
  refine ⟨N, hN, ?_⟩
  have h := H.mul_mem hS htailN
  rwa [FiniteMaskedGenerators.Realization.finiteMaskSymplectic_partition] at h

end

end OAI.RepresentationTheory.Hecke.RadialDilation.FinitePrimeAssembly.Realization
