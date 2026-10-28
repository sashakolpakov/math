import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.CenterDescent
import Mathlib.RingTheory.LocalProperties.Basic

/-! # Flat Containment -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.FlatContainment.Construction

noncomputable section

/-! Ideal containment descends from actual pointed flat charts. -/

universe u

theorem flat_map_ideal_containment_at_prime
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat)
    (J K p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (hq : q.comap f = p) (h : J.map f ≤ K.map f) :
    J.map (algebraMap R (Localization.AtPrime p)) ≤
      K.map (algebraMap R (Localization.AtPrime p)) := by
  have he : (J ⊔ K).map f = K.map f := by rw [Ideal.map_sup, sup_eq_right.mpr h]
  have hl := Etale.CenterDescent.Construction.flat_map_ideal_equality_at_prime f hf (J ⊔ K) K p q hq he
  rw [Ideal.map_sup] at hl
  exact sup_eq_right.mp hl

theorem ideal_le_of_pointed_flat_charts
    {R : Type u} [CommRing R] (J K : Ideal R)
    (h : ∀ p : PrimeSpectrum R,
      ∃ (S : CommRingCat.{u}) (f : R →+* S), f.Flat ∧
        ∃ q : PrimeSpectrum S, PrimeSpectrum.comap f q = p ∧ J.map f ≤ K.map f) :
    J ≤ K := by
  apply Ideal.le_of_localization_maximal
  intro p hp
  let : p.IsMaximal := hp
  obtain ⟨S, f, hf, q, hq, hJK⟩ := h ⟨p, inferInstance⟩
  exact flat_map_ideal_containment_at_prime f hf J K p q.asIdeal
    (congrArg PrimeSpectrum.asIdeal hq) hJK

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.FlatContainment.Construction
