import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Flat.Basic

/-! # Flat Algebra Local Basis -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FlatAlgebraLocalBasis

noncomputable section

/-! Finitely presented flat modules admit actual finite bases on basic neighborhoods, with the basis size prescribed by the stalk rank. -/
universe u v

theorem finiteFlat_exists_localModuleBasis
    {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] [Module.Flat R M] (p : PrimeSpectrum R)
    {n : ℕ} (hn : Module.rankAtStalk M p = n) :
    ∃ a : R, a ∉ p.asIdeal ∧
      Nonempty (Module.Basis (Fin n) (Localization.Away a) (LocalizedModule.Away a M)) := by
  let Rₚ := Localization.AtPrime p.asIdeal
  let Mₚ := LocalizedModule.AtPrime p.asIdeal M
  have : Module.Free Rₚ Mₚ := Module.free_of_flat_of_isLocalRing
  have hb : Nonempty (Module.Basis (Fin n) Rₚ Mₚ) := by
    have hn' : Module.finrank Rₚ Mₚ = n := hn
    rw [← hn']
    exact ⟨Module.finBasis Rₚ Mₚ⟩
  obtain ⟨b⟩ := hb
  obtain ⟨a, ha, b', _⟩ := Module.FinitePresentation.exists_basis_localizedModule_powers
    p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) Rₚ b
  exact ⟨a, ha, ⟨b'⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FlatAlgebraLocalBasis
