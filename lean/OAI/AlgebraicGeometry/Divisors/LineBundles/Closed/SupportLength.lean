import OAI.AlgebraicGeometry.Divisors.LineBundles.LocalIntersectionFiniteness
import Mathlib.RingTheory.Support

/-! # Support Length -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportLength.BundleCycles

noncomputable section

/-!
# LineBundleCycles: finite length from support at the closed point

For a finite module over a Noetherian local ring, vanishing at every
other prime forces the annihilator radical to be the maximal ideal.
The actual annihilator quotient then supplies finite module length.
-/

variable {R M : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]

theorem moduleLength_ne_top_of_closed_support
    (hs : ∀ p ∈ Module.support R M, p.asIdeal = IsLocalRing.maximalIdeal R) :
    Module.length R M ≠ ⊤ := by
  by_cases hM : Subsingleton M
  · let closedSupportSubsingleton : Subsingleton M := hM
    rw [Module.length_eq_zero]
    exact ENat.zero_ne_top
  have hI : Module.annihilator R M ≠ ⊤ :=
    fun h => hM (Module.annihilator_eq_top_iff.mp h)
  have hIm : Module.annihilator R M ≤ IsLocalRing.maximalIdeal R :=
    IsLocalRing.le_maximalIdeal hI
  have hrad : (Module.annihilator R M).radical = IsLocalRing.maximalIdeal R := by
    apply le_antisymm
    · exact (Ideal.radical_mono hIm).trans_eq
        (inferInstance : (IsLocalRing.maximalIdeal R).IsPrime).radical
    · rw [Ideal.radical_eq_sInf]
      apply le_sInf
      rintro P ⟨hIP, hP⟩
      have hp : (⟨P, hP⟩ : PrimeSpectrum R) ∈ Module.support R M :=
        Module.mem_support_iff_of_finite.mpr hIP
      exact le_of_eq (hs ⟨P, hP⟩ hp).symm
  apply EquationFiniteLength.BundleCycles.moduleLength_ne_top_of_killedIdeal (Module.annihilator R M)
    (LocalIntersectionFiniteness.BundleCycles.finiteLength_quotient_of_radical_maximal _ hrad)
  intro m r
  exact Module.mem_annihilator.mp r.2 m

theorem moduleLength_ne_top_of_localizations_zero
    (hs : ∀ p : PrimeSpectrum R, p.asIdeal ≠ IsLocalRing.maximalIdeal R →
      Subsingleton (LocalizedModule p.asIdeal.primeCompl M)) :
    Module.length R M ≠ ⊤ := by
  apply moduleLength_ne_top_of_closed_support
  intro p hp
  by_contra hpm
  exact (Module.notMem_support_iff.mpr (hs p hpm)) hp

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportLength.BundleCycles
