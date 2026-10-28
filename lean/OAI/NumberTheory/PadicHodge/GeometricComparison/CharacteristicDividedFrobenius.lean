import Mathlib.RingTheory.DividedPowers.DPMorphism
import OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius

/-! # Characteristic Divided Frobenius -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CharacteristicDividedFrobenius.CharacteristicPDividedFrobenius

noncomputable section

/-! In characteristic p, Frobenius kills every divided-power ideal and
is a morphism of its original divided powers. -/

universe u
variable (p : ℕ) [Fact p.Prime] {A : Type u} [CommRing A]
  (hp : (p : A) = 0) {I : Ideal A} (δ : DividedPowers I)

include δ in
theorem ideal_zero (x : A) (hx : x ∈ I) : AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.powerRingHom p Fact.out A hp x = 0 := by
  change x ^ p = 0
  exact DividedPowers.nilpotent_of_mem_dpIdeal (Fact.out : p.Prime).ne_zero
    (fun _ => by rw [nsmul_eq_mul, hp, zero_mul]) δ hx

def map : DividedPowers.DPMorphism δ δ where
  toRingHom := AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.powerRingHom p Fact.out A hp
  ideal_comp := Ideal.map_le_iff_le_comap.mpr (fun x hx => by
    change AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.powerRingHom p Fact.out A hp x ∈ I
    rw [ideal_zero p hp δ x hx]
    exact I.zero_mem)
  dpow_comp := by
    intro n x hx
    by_cases hn : n = 0
    · subst n
      rw [δ.dpow_zero hx, map_one, ideal_zero p hp δ x hx, δ.dpow_zero I.zero_mem]
    · rw [ideal_zero p hp δ x hx, δ.dpow_eval_zero hn,
        ideal_zero p hp δ (δ.dpow n x) (δ.dpow_mem hn hx)]

theorem apply (x : A) : map p hp δ x = x ^ p := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CharacteristicDividedFrobenius.CharacteristicPDividedFrobenius
