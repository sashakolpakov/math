import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Ideal.IsPrincipal
import Mathlib.RingTheory.LocalRing.Basic

/-! # Principal -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.Principal.Construction.PrincipalDescent

/-! Principal ideals descend from a faithfully flat local domain. -/

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [IsLocalRing S]
variable [Algebra R S] [Module.FaithfullyFlat R S]

omit [Module.FaithfullyFlat R S] in
theorem exists_generator_of_map (I : Ideal R) {c : S} (hc : c ≠ 0)
    (hI : I.map (algebraMap R S) = Ideal.span {c}) :
    ∃ a ∈ I, Ideal.span {algebraMap R S a} = Ideal.span {c} := by
  classical
  by_contra! h
  have hle : I.map (algebraMap R S) ≤
      IsLocalRing.maximalIdeal S * Ideal.span {c} := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    have hm : algebraMap R S a ∈ Ideal.span {c} := hI ▸ Ideal.mem_map_of_mem _ ha
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hm
    have hbu : ¬ IsUnit b := by
      intro hu
      apply h a ha
      rw [← hb]
      exact Ideal.span_singleton_mul_left_unit hu c
    exact Ideal.mem_mul_span_singleton.mpr ⟨b, hbu, hb⟩
  have hm : c ∈ IsLocalRing.maximalIdeal S * Ideal.span {c} :=
    hle (hI.symm ▸ Ideal.subset_span (Set.mem_singleton c))
  obtain ⟨b, hb, he⟩ := Ideal.mem_mul_span_singleton.mp hm
  have hb1 : b = 1 := (mul_right_cancel₀ hc) (he.trans (one_mul c).symm)
  exact (IsLocalRing.maximalIdeal S).one_notMem (hb1 ▸ hb)

theorem isPrincipal (I : Ideal R) (hI : (I.map (algebraMap R S)).IsPrincipal) :
    I.IsPrincipal := by
  classical
  by_cases hz : I.map (algebraMap R S) = ⊥
  · have he : I = ⊥ := by
      apply Ideal.map_injective_of_faithfullyFlat (B := S)
      simpa using hz
    rw [he]
    infer_instance
  obtain ⟨c, hc⟩ := hI
  change I.map (algebraMap R S) = Ideal.span {c} at hc
  have hc0 : c ≠ 0 := by
    intro h
    apply hz
    rw [hc, h]
    simp
  obtain ⟨a, _, ha⟩ := exists_generator_of_map I hc0 hc
  refine ⟨a, ?_⟩
  apply Ideal.map_injective_of_faithfullyFlat (B := S)
  simpa [Ideal.map_span, hc] using ha.symm

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.Principal.Construction.PrincipalDescent
