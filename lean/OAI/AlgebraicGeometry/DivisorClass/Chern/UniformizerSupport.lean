import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmoothDVR
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! # Uniformizer Support -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.UniformizerSupport

noncomputable section

/-!
# ChernClass: a local uniformizer defines the actual prime support nearby

Finite generation lets one clear the finitely many localization denominators
of an ideal containment. For a DVR uniformizer, the localized principal
ideal is the maximal ideal. Consequently its zero locus on a genuine
principal neighborhood is exactly the original prime support.
-/

universe u

variable {R : Type u} [CommRing R]

/-- A finitely generated ideal containment at a prime has one common
denominator outside that prime, obtained from its actual generators. -/
theorem exists_common_localization_denominator (P I J : Ideal R) [P.IsPrime]
    (hJ : J.FG)
    (h : J.map (algebraMap R (Localization.AtPrime P)) ≤
      I.map (algebraMap R (Localization.AtPrime P))) :
    ∃ b : R, b ∉ P ∧ ∀ a ∈ J, b * a ∈ I := by
  classical
  obtain ⟨s, hs⟩ := hJ
  have hd (a : s) : ∃ b : P.primeCompl, (b : R) * a.val ∈ I := by
    have ha : a.val ∈ J := hs ▸ Ideal.subset_span a.property
    have hm := h (Ideal.mem_map_of_mem (algebraMap R (Localization.AtPrime P)) ha)
    obtain ⟨b, hb, hba⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff P.primeCompl (Localization.AtPrime P) I a.val).mp hm
    exact ⟨⟨b, hb⟩, hba⟩
  choose b hb using hd
  let c : R := ∏ a : s, (b a : R)
  have hc : c ∉ P := by
    change c ∈ P.primeCompl
    exact Submonoid.prod_mem _ (fun a _ => (b a).property)
  refine ⟨c, hc, ?_⟩
  intro a ha
  rw [← hs] at ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
      have hdvd : (b ⟨a, ha⟩ : R) ∣ c :=
        Finset.dvd_prod_of_mem (fun t : s => (b t : R)) (Finset.mem_univ (⟨a, ha⟩ : s))
      obtain ⟨d, hd⟩ := hdvd
      rw [hd, mul_right_comm]
      exact I.mul_mem_right d (hb ⟨a, ha⟩)
  | zero => simpa only [mul_zero] using I.zero_mem
  | add a b ha hb ia ib =>
      rw [mul_add]
      exact I.add_mem ia ib
  | smul r a ha ia =>
      change c * (r * a) ∈ I
      rw [mul_left_comm]
      exact I.mul_mem_left r ia

/-- A genuine local uniformizer cuts out the actual prime support on
some principal neighborhood of that prime. -/
theorem uniformizer_prime_support_neighborhood [IsNoetherianRing R]
    (P : Ideal R) [P.IsPrime]
    [IsDomain (Localization.AtPrime P)] [IsDiscreteValuationRing (Localization.AtPrime P)]
    (p : R) (hp : Irreducible (algebraMap R (Localization.AtPrime P) p)) :
    ∃ b : R, b ∉ P ∧ ∀ (Q : Ideal R), Q.IsPrime → b ∉ Q → (p ∈ Q ↔ P ≤ Q) := by
  have hpP : p ∈ P := by
    by_contra h
    exact hp.not_isUnit (IsLocalization.map_units (Localization.AtPrime P) (⟨p, h⟩ : P.primeCompl))
  have he : P.map (algebraMap R (Localization.AtPrime P)) =
      (Ideal.span {p}).map (algebraMap R (Localization.AtPrime P)) := by
    rw [Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_singleton]
    exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hp
  obtain ⟨b, hb, hm⟩ := exists_common_localization_denominator P (Ideal.span {p}) P
    (IsNoetherian.noetherian P) he.le
  refine ⟨b, hb, ?_⟩
  intro Q hQ hbQ
  constructor
  · intro hpQ a ha
    have hmul : b * a ∈ Q := (Ideal.span_singleton_le_iff_mem Q).mpr hpQ (hm a ha)
    exact (hQ.mem_or_mem hmul).resolve_left hbQ
  · intro hPQ
    exact hPQ hpP

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.UniformizerSupport
