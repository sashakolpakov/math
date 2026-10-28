import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OpenCover
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-! # Free Cover -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.FreeCover

noncomputable section

/-! A finite étale algebra has a finite principal cover on which its
actual base-changed coordinate algebra is free. -/

open scoped TensorProduct

universe u

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Algebra.Etale A B] [Module.Finite A B]

theorem exists_at_prime (p : PrimeSpectrum A) :
    ∃ r ∉ p.asIdeal,
      Module.Free (Localization.Away r) (Localization.Away r ⊗[A] B) := by
  let : Module.FinitePresentation A B :=
    Module.FinitePresentation.of_finite_of_finitePresentation A B
  let : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl B) := Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hfree, _⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl B)
    (Localization.AtPrime p.asIdeal)
  let : Module.Free (Localization.Away r) (LocalizedModule.Away r B) := hfree
  exact ⟨r, hr, Module.Free.of_equiv (LocalizedModule.equivTensorProduct (.powers r) B)⟩

theorem exists_finite_cover :
    ∃ s : Finset A, Ideal.span (s : Set A) = ⊤ ∧
      ∀ r ∈ s, Module.Free (Localization.Away r) (Localization.Away r ⊗[A] B) := by
  obtain ⟨s, hs, hspan⟩ := Principal.OpenCover.finite_unit_family
    (fun r : A => Module.Free (Localization.Away r) (Localization.Away r ⊗[A] B)) (by
      intro p
      obtain ⟨r, hr, hf⟩ := exists_at_prime A B p
      exact ⟨r, hf, hr⟩)
  exact ⟨s, hspan, hs⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.FreeCover
