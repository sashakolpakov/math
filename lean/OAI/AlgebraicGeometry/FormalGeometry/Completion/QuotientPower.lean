import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-! # Quotient Power -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.QuotientPower.Construction

noncomputable section

/-! # Completion: the actual closed homeomorphisms between successive infinitesimal bases -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The spectrum map from a smaller positive infinitesimal neighborhood to a larger one. -/
def quotientPowerMap {m n : ℕ} (h : m ≤ n) :
    Spec (CommRingCat.of (R ⧸ I ^ m)) ⟶ Spec (CommRingCat.of (R ⧸ I ^ n)) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorPow I h))

instance quotientPowerMap_isClosedImmersion {m n : ℕ} (h : m ≤ n) :
    IsClosedImmersion (quotientPowerMap I h) :=
  IsClosedImmersion.spec_of_surjective _
    (Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right h))

/-- Positive powers of an ideal have the same prime spectrum support. -/
theorem quotientPowerMap_surjective {m n : ℕ} (hm : 0 < m) (h : m ≤ n) :
    Surjective (quotientPowerMap I h) := by
  constructor
  change Function.Surjective (PrimeSpectrum.comap (Ideal.Quotient.factorPow I h))
  rw [← Set.range_eq_univ, range_comap_of_surjective _ _
    (Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right h))]
  apply Set.eq_univ_iff_forall.mpr
  intro q
  change RingHom.ker (Ideal.Quotient.factorPow I h) ≤ q.asIdeal
  rw [Ideal.Quotient.factor_ker, Ideal.map_le_iff_le_comap]
  apply (Ideal.pow_le_self (Nat.ne_zero_of_lt hm)).trans
  apply Ideal.IsPrime.le_of_pow_le (n := n)
  intro r hr
  change Ideal.Quotient.mk (I ^ n) r ∈ q.asIdeal
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr]
  exact q.asIdeal.zero_mem

/-- The underlying spaces of positive infinitesimal bases are canonically homeomorphic. -/
def quotientPowerHomeomorph {m n : ℕ} (hm : 0 < m) (h : m ≤ n) :
    Spec (CommRingCat.of (R ⧸ I ^ m)) ≃ₜ Spec (CommRingCat.of (R ⧸ I ^ n)) :=
  (quotientPowerMap I h).isClosedEmbedding.isEmbedding.toHomeomorphOfSurjective
    (quotientPowerMap_surjective I hm h).surj

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.QuotientPower.Construction
