import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AmitsurDegreeOne
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.LinearAlgebra.DFinsupp

/-! # Principal Cover Flat -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PrincipalCoverFlat.Construction

noncomputable section

/-! Finite principal affine covers give faithfully flat product algebras. -/

universe u v

variable (R : Type u) [CommRing R] {ι : Type v} [Finite ι] (f : ι → R)

omit [Finite ι] in
theorem principalCover_exists_notMem (hf : Ideal.span (Set.range f) = ⊤)
    (p : PrimeSpectrum R) : ∃ i, f i ∉ p.asIdeal := by
  by_contra! h
  have hs : Ideal.span (Set.range f) ≤ p.asIdeal :=
    Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact h i)
  rw [hf] at hs
  exact p.isPrime.ne_top (top_le_iff.mp hs)

theorem flat_pi_of_finite (B : ι → Type*) [∀ i, CommRing (B i)]
    [∀ i, Algebra R (B i)] [∀ i, Module.Flat R (B i)] : Module.Flat R (∀ i, B i) := by
  let := Fintype.ofFinite ι
  exact Module.Flat.of_linearEquiv (DFinsupp.linearEquivFunOnFintype (R := R)).symm

omit [Finite ι] in
theorem principalCover_comap_surjective (hf : Ideal.span (Set.range f) = ⊤) :
    Function.Surjective (PrimeSpectrum.comap
      (algebraMap R (∀ i, Localization.Away (f i)))) := by
  intro p
  obtain ⟨i, hi⟩ := principalCover_exists_notMem R f hf p
  have hp : p ∈ Set.range (PrimeSpectrum.comap
      (algebraMap R (Localization.Away (f i)))) := by
    rw [PrimeSpectrum.localization_away_comap_range _ (f i)]
    exact hi
  obtain ⟨q, hq⟩ := hp
  refine ⟨PrimeSpectrum.comap (Pi.evalRingHom (fun i ↦ Localization.Away (f i)) i) q, ?_⟩
  exact hq

theorem faithfullyFlat_principalCover (hf : Ideal.span (Set.range f) = ⊤) :
    Module.FaithfullyFlat R (∀ i, Localization.Away (f i)) := by
  let : Module.Flat R (∀ i, Localization.Away (f i)) :=
    flat_pi_of_finite R (fun i ↦ Localization.Away (f i))
  exact Module.FaithfullyFlat.of_comap_surjective (principalCover_comap_surjective R f hf)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PrincipalCoverFlat.Construction
