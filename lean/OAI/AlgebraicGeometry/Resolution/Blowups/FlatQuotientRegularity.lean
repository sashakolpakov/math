import OAI.AlgebraicGeometry.Resolution.Blowups.ChartFlatBaseChange
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Flat Quotient Regularity -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.FlatQuotientRegularity.Construction

noncomputable section

/-! Flat base change preserves regularity modulo an ideal and therefore transverse ideal quotients. -/

universe u

theorem flat_extended_quotient_module {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] (I : Ideal R) : Module.Flat (R ⧸ I) (S ⧸ I.map (algebraMap R S)) := by
  let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I
  exact Module.Flat.of_linearEquiv e.toLinearEquiv

theorem flat_extended_quotient_regular {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] (I : Ideal R) (c : R) (hc : IsRegular (Ideal.Quotient.mk I c)) :
    IsRegular (Ideal.Quotient.mk (I.map (algebraMap R S)) (algebraMap R S c)) := by
  let : Module.Flat (R ⧸ I) (S ⧸ I.map (algebraMap R S)) := flat_extended_quotient_module I
  exact ChartFlatBaseChange.Construction.flat_algebraMap_regular (S := S ⧸ I.map (algebraMap R S)) (Ideal.Quotient.mk I c) hc

theorem ideal_colon_eq_of_quotient_regular {R : Type u} [CommRing R]
    (I : Ideal R) (c : R) (hc : IsRegular (Ideal.Quotient.mk I c)) : I.colon (Ideal.span {c} : Set R) = I := by
  apply le_antisymm
  · intro a ha
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply hc.right
    change Ideal.Quotient.mk I a * Ideal.Quotient.mk I c = 0 * Ideal.Quotient.mk I c
    rw [zero_mul, ← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_colon_span_singleton.mp ha)
  · exact Ideal.le_colon

theorem flat_map_colon_eq_of_quotient_regular {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] (I : Ideal R) (c : R) (hc : IsRegular (Ideal.Quotient.mk I c)) :
    (I.map (algebraMap R S)).colon (Ideal.span {algebraMap R S c} : Set S) = I.map (algebraMap R S) :=
  ideal_colon_eq_of_quotient_regular _ _ (flat_extended_quotient_regular I c hc)

theorem quotient_regular_of_ideal_colon_eq {R : Type u} [CommRing R]
    (I : Ideal R) (c : R) (h : I.colon (Ideal.span {c} : Set R) = I) :
    IsRegular (Ideal.Quotient.mk I c) := by
  have hinj : Function.Injective (fun x : R ⧸ I => x * Ideal.Quotient.mk I c) := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    change Ideal.Quotient.mk I a * Ideal.Quotient.mk I c =
      Ideal.Quotient.mk I b * Ideal.Quotient.mk I c at hxy
    apply Ideal.Quotient.eq.mpr
    have hm : (a - b) * c ∈ I := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_mul, map_sub, sub_mul, hxy, sub_self]
    have hc : a - b ∈ I.colon (Ideal.span {c} : Set R) := Ideal.mem_colon_span_singleton.mpr hm
    exact h ▸ hc
  refine ⟨?_, hinj⟩
  intro x y hxy
  exact hinj (by simpa only [mul_comm] using hxy)

theorem flat_map_colon_self {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] (I : Ideal R) (c : R) (h : I.colon (Ideal.span {c} : Set R) = I) :
    (I.map (algebraMap R S)).colon (Ideal.span {algebraMap R S c} : Set S) = I.map (algebraMap R S) :=
  flat_map_colon_eq_of_quotient_regular I c (quotient_regular_of_ideal_colon_eq I c h)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.FlatQuotientRegularity.Construction
