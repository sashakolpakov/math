import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Finiteness.Ideal

/-! # Local Containment Neighborhood -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.LocalContainmentNeighborhood.Construction

noncomputable section

section

/-! Finite local ideal containments hold on an actual affine open neighborhood. -/

variable {R : Type*} [CommRing R]

/-- A finite ideal containment at a prime has one common denominator
outside that prime. -/
theorem exists_common_ideal_denominator (J K q : Ideal R) [q.IsPrime] (hJ : J.FG)
    (h : J.map (algebraMap R (Localization.AtPrime q)) ≤ K.map (algebraMap R (Localization.AtPrime q))) :
    ∃ f ∉ q, ∀ x ∈ J, f * x ∈ K := by
  classical
  obtain ⟨s, hs⟩ := hJ
  have hex : ∀ t : s, ∃ d ∉ q, d * t.val ∈ K := by
    intro t
    have ht : t.val ∈ J := hs ▸ Ideal.subset_span t.property
    simpa only [Ideal.mem_primeCompl_iff] using
      (IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl (Localization.AtPrime q) K t.val).mp
        (h (Ideal.mem_map_of_mem _ ht))
  choose d hd hdK using hex
  let f := ∏ t : s, d t
  have hf : f ∉ q := by
    exact (q.primeCompl.prod_mem (fun t _ => hd t))
  refine ⟨f, hf, ?_⟩
  have hle : J ≤ K.colon (Ideal.span {f}) := by
    rw [← hs]
    apply Ideal.span_le.mpr
    intro x hx
    apply Ideal.mem_colon_span_singleton.mpr
    let t : s := ⟨x, hx⟩
    obtain ⟨v, hv⟩ := Finset.dvd_prod_of_mem d (Finset.mem_univ t)
    have he : f = d t * v := hv
    rw [he]
    convert K.mul_mem_left v (hdK t) using 1
    change x * (d t * v) = v * (d t * x)
    ring
  intro x hx
  simpa only [mul_comm x f] using Ideal.mem_colon_span_singleton.mp (hle hx)

/-- The localization at that common denominator is an actual affine open
neighborhood on which the ideal containment holds. -/
theorem exists_neighborhood_ideal_containment (J K q : Ideal R) [q.IsPrime] (hJ : J.FG)
    (h : J.map (algebraMap R (Localization.AtPrime q)) ≤ K.map (algebraMap R (Localization.AtPrime q))) :
    ∃ f ∉ q, J.map (algebraMap R (Localization.Away f)) ≤ K.map (algebraMap R (Localization.Away f)) := by
  obtain ⟨f, hf, hmul⟩ := exists_common_ideal_denominator J K q hJ h
  refine ⟨f, hf, ?_⟩
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  change algebraMap R (Localization.Away f) x ∈ K.map (algebraMap R (Localization.Away f))
  apply (Ideal.unit_mul_mem_iff_mem _ (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away f) f)).mp
  rw [← map_mul]
  exact Ideal.mem_map_of_mem _ (hmul x hx)

/-- In particular, local divisibility by a prescribed ideal power can be
spread to an actual open neighborhood without changing the exponent. -/
theorem exists_neighborhood_ideal_power_containment (J K q : Ideal R) [q.IsPrime] (hJ : J.FG)
    (n : ℕ) (h : J.map (algebraMap R (Localization.AtPrime q)) ≤
      K.map (algebraMap R (Localization.AtPrime q)) ^ n) :
    ∃ f ∉ q, J.map (algebraMap R (Localization.Away f)) ≤
      K.map (algebraMap R (Localization.Away f)) ^ n := by
  rw [← Ideal.map_pow] at h
  obtain ⟨f, hf, hle⟩ := exists_neighborhood_ideal_containment J (K ^ n) q hJ h
  exact ⟨f, hf, by simpa only [Ideal.map_pow] using hle⟩

end

/-! Finite ideal equalities spread from a local ring to an actual affine neighborhood. -/

variable {R T : Type*} [CommRing R] [CommRing T]

theorem ideal_map_le_of_unit_common_denominator (φ : R →+* T) (J K : Ideal R)
    (f : R) (hf : IsUnit (φ f)) (h : ∀ x ∈ J, f * x ∈ K) : J.map φ ≤ K.map φ := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  change φ x ∈ K.map φ
  apply (Ideal.unit_mul_mem_iff_mem _ hf).mp
  rw [← map_mul]
  exact Ideal.mem_map_of_mem _ (h x hx)

/-- Two finite ideals equal at a prime are equal on a principal affine
open containing that prime. The open is constructed by clearing denominators
for both inclusions. -/
theorem exists_neighborhood_ideal_equality (J K q : Ideal R) [q.IsPrime]
    (hJ : J.FG) (hK : K.FG)
    (h : J.map (algebraMap R (Localization.AtPrime q)) = K.map (algebraMap R (Localization.AtPrime q))) :
    ∃ f ∉ q, J.map (algebraMap R (Localization.Away f)) = K.map (algebraMap R (Localization.Away f)) := by
  obtain ⟨f, hf, hJK⟩ := exists_common_ideal_denominator J K q hJ h.le
  obtain ⟨g, hg, hKJ⟩ := exists_common_ideal_denominator K J q hK h.ge
  refine ⟨f * g, q.primeCompl.mul_mem hf hg, le_antisymm ?_ ?_⟩
  · apply ideal_map_le_of_unit_common_denominator _ J K (f * g)
      (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (f * g)) (f * g))
    intro x hx
    convert K.mul_mem_left g (hJK x hx) using 1
    ring
  · apply ideal_map_le_of_unit_common_denominator _ K J (f * g)
      (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (f * g)) (f * g))
    intro x hx
    rw [mul_assoc]
    exact J.mul_mem_left f (hKJ x hx)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.LocalContainmentNeighborhood.Construction
