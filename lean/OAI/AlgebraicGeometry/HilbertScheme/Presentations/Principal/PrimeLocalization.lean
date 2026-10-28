import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Integer

/-! # Prime Localization -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Principal.PrimeLocalization

noncomputable section

/-! Finite families of elements in a prime localization lift to one
principal localization whose open set contains that prime. -/

universe u v
variable {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime]

def principalToPrimeMap (s : A) (hs : s ∉ p) :
    Localization.Away s →+* Localization.AtPrime p :=
  IsLocalization.Away.lift s
    (IsLocalization.map_units (Localization.AtPrime p) (⟨s, hs⟩ : p.primeCompl))

@[simp] theorem principalToPrimeMap_algebraMap (s : A) (hs : s ∉ p) (a : A) :
    principalToPrimeMap p s hs (algebraMap A (Localization.Away s) a) =
      algebraMap A (Localization.AtPrime p) a := IsLocalization.Away.lift_eq _ _ _

theorem finite_primeLocalization_lift {κ : Type v} [Finite κ]
    (x : κ → Localization.AtPrime p) :
    ∃ (s : A) (hs : s ∉ p) (y : κ → Localization.Away s),
      ∀ i, principalToPrimeMap p s hs (y i) = x i := by
  classical
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite p.primeCompl x
  choose a ha using hs
  refine ⟨s.val, s.property, fun i => IsLocalization.mk' (Localization.Away s.val) (a i)
    (⟨s.val, Submonoid.mem_powers s.val⟩ : Submonoid.powers s.val), fun i => ?_⟩
  unfold principalToPrimeMap IsLocalization.Away.lift
  apply (IsLocalization.lift_mk'_spec _ _ _ _).mpr
  simpa only [Algebra.smul_def] using ha i

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Principal.PrimeLocalization
