import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.IdealLocalizationZero
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Principal.PrimeLocalization
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Ring.Hom.InjSurj

/-! # Reduced Principal Domain -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ReducedPrincipalDomain

noncomputable section

/-! Around a minimal prime of a reduced Noetherian ring there is a
principal open whose coordinate ring is a domain. -/

universe u
variable {R : Type u} [CommRing R] [IsReduced R] [IsNoetherianRing R]

theorem reduced_minimalPrime_principal_domain (p : Ideal R) (hp : p ∈ minimalPrimes R) :
    ∃ s : R, s ∉ p ∧ IsDomain (Localization.Away s) := by
  let : p.IsPrime := hp.1.1
  let K := Localization.AtPrime p
  let : Ring.KrullDimLE 0 K := Ring.KrullDimLE.of_isLocalization p hp K
  let : Field K := Ring.KrullDimLE.isField_of_isReduced.toField
  have hk (x : R) : algebraMap R K x = 0 ↔ x ∈ p := by
    apply not_iff_not.mp
    exact isUnit_iff_ne_zero.symm.trans (IsLocalization.AtPrime.isUnit_to_map_iff K p x)
  have hp0 : p.map (algebraMap R K) = ⊥ := by
    apply (Ideal.map_eq_bot_iff_le_ker _).mpr
    intro x hx
    exact (hk x).mpr hx
  obtain ⟨s, hs⟩ := Finite.IdealLocalizationZero.finite_ideal_localization_zero p.primeCompl K p
    (IsNoetherian.noetherian p) hp0
  let A := Localization.Away s.val
  let φ : A →+* K := Principal.PrimeLocalization.principalToPrimeMap p s.val s.property
  have hφmap (r : R) : φ (algebraMap R A r) = algebraMap R K r :=
    Principal.PrimeLocalization.principalToPrimeMap_algebraMap p s.val s.property r
  have hφ : Function.Injective φ := by
    apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers s.val) φ).mpr
    intro x y
    constructor
    · exact congrArg φ
    · intro hxy
      have hxy' := (hφmap x).symm.trans (hxy.trans (hφmap y))
      have hmem : x - y ∈ p := (hk (x - y)).mp (by rw [map_sub, hxy', sub_self])
      have hzero : algebraMap R A (x - y) = 0 :=
        (Ideal.map_eq_bot_iff_le_ker _).mp hs hmem
      rwa [map_sub, sub_eq_zero] at hzero
  exact ⟨s.val, s.property, Function.Injective.isDomain φ hφ⟩

theorem exists_reduced_principal_domain [Nontrivial R] :
    ∃ s : R, s ≠ 0 ∧ IsDomain (Localization.Away s) := by
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes (R := R) (I := ⊥) bot_ne_top
  obtain ⟨s, hs, hS⟩ := reduced_minimalPrime_principal_domain p hp
  exact ⟨s, fun h => hs (h ▸ p.zero_mem), hS⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ReducedPrincipalDomain
