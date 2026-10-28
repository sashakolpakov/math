import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.Polynomial.FieldDivision

/-! # Generic Polynomial GCD -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.GenericPolynomialGCD.Constructions.GenericGCD

noncomputable section

/-!
# Clearing denominators in a generic polynomial gcd

Over an integral domain, a polynomial ideal becomes principal over the
fraction field. Clearing denominators gives a nonzero polynomial and
explicit nonzero scalar multipliers relating it to the original ideal.
-/

open Set _root_.Polynomial
open scoped nonZeroDivisors

variable {A K : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]

attribute [local instance] Polynomial.algebra Polynomial.isLocalization

theorem clear_mapped_ideal_membership (I : Ideal A[X]) (p : A[X])
    (hp : p.map (algebraMap A K) ∈ I.map (Polynomial.mapRingHom (algebraMap A K))) :
    ∃ a : A, a ≠ 0 ∧ C a * p ∈ I := by
  obtain ⟨c, hc, hcp⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (A⁰.map C) K[X] I p).mp hp
  obtain ⟨a, ha, rfl⟩ := hc
  exact ⟨a, nonZeroDivisors.ne_zero ha, hcp⟩

theorem clear_mapped_divisibility (p q : A[X])
    (h : p.map (algebraMap A K) ∣ q.map (algebraMap A K)) :
    ∃ a : A, a ≠ 0 ∧ p ∣ C a * q := by
  have hm : q.map (algebraMap A K) ∈
      (Ideal.span ({p} : Set A[X])).map (Polynomial.mapRingHom (algebraMap A K)) := by
    rw [Ideal.map_span, Set.image_singleton]
    exact Ideal.mem_span_singleton.mpr h
  obtain ⟨a, ha, haq⟩ := clear_mapped_ideal_membership (K := K) _ q hm
  exact ⟨a, ha, Ideal.mem_span_singleton.mp haq⟩

/-- The polynomial generator over the fraction field can be represented
over the original domain. Its divisibility and ideal membership both hold
after multiplying by nonzero scalars from that domain. -/
theorem exists_generic_generator (I : Ideal A[X]) (hI : I ≠ ⊥) :
    ∃ G : A[X], G ≠ 0 ∧
      (∃ a : A, a ≠ 0 ∧ C a * G ∈ I) ∧
      ∀ p ∈ I, ∃ a : A, a ≠ 0 ∧ G ∣ C a * p := by
  classical
  let K := FractionRing A
  let φ : A[X] →+* K[X] := Polynomial.mapRingHom (algebraMap A K)
  let J := I.map φ
  let q : K[X] := Submodule.IsPrincipal.generator J
  have hqspan : Ideal.span ({q} : Set K[X]) = J := Ideal.span_singleton_generator J
  have hq0 : q ≠ 0 := by
    intro hq
    have hJ : J = ⊥ := by rw [← hqspan, hq, Ideal.span_singleton_eq_bot.mpr rfl]
    apply hI
    apply le_antisymm ?_ bot_le
    intro p hp
    have hmap : φ p ∈ J := Ideal.mem_map_of_mem φ hp
    rw [hJ, Ideal.mem_bot] at hmap
    exact (Polynomial.map_injective (algebraMap A K) (IsFractionRing.injective A K))
      (by simpa only [φ, Polynomial.coe_mapRingHom, Polynomial.map_zero] using hmap)
  let G := IsLocalization.integerNormalization A⁰ q
  have hG0 : G ≠ 0 := by
    exact fun h => hq0 ((IsLocalization.integerNormalization_eq_zero_iff (M := A⁰) le_rfl q).mp h)
  obtain ⟨b, hb, hGb⟩ := IsLocalization.integerNormalization_spec A⁰ q
  have hGb' : φ G = C (algebraMap A K b) * q := by
    simpa only [φ, Polynomial.coe_mapRingHom, ← algebraMap_smul, Algebra.smul_def,
      Polynomial.algebraMap_apply] using hGb
  have hbunit : IsUnit (C (algebraMap A K b) : K[X]) :=
    isUnit_C.mpr (isUnit_iff_ne_zero.mpr ((IsFractionRing.to_map_eq_zero_iff (R := A) (K := K)).not.mpr
      (nonZeroDivisors.ne_zero hb)))
  have hGspan : Ideal.span ({φ G} : Set K[X]) = J := by
    rw [hGb', Ideal.span_singleton_mul_left_unit hbunit, hqspan]
  have hGJ : φ G ∈ J := hGspan ▸ Ideal.subset_span (mem_singleton _)
  refine ⟨G, hG0, clear_mapped_ideal_membership (K := K) I G hGJ, ?_⟩
  intro p hp
  apply clear_mapped_divisibility (K := K) G p
  apply Ideal.mem_span_singleton.mp
  change φ p ∈ Ideal.span ({φ G} : Set K[X])
  rw [hGspan]
  exact Ideal.mem_map_of_mem φ hp

/-- A finite polynomial family has one common-root polynomial away from the
vanishing of one nonzero coefficient-ring element. This statement holds for
every specialization to a field, and preserves the generator's degree. -/
theorem exists_common_root_polynomial {ι : Type*} [Fintype ι] (P : ι → A[X])
    (hP : ∃ i, P i ≠ 0) :
    ∃ (G : A[X]) (c : A), c ≠ 0 ∧ G ≠ 0 ∧
      ∀ {F : Type*} [Field F] (φ : A →+* F), φ c ≠ 0 →
        (G.map φ).natDegree = G.natDegree ∧
        ∀ z : F, (∀ i, (P i).eval₂ φ z = 0) ↔ G.eval₂ φ z = 0 := by
  classical
  let I := Ideal.span (Set.range P)
  have hmem (i : ι) : P i ∈ I := Ideal.subset_span (mem_range_self i)
  have hI : I ≠ ⊥ := by
    intro h
    obtain ⟨i, hi⟩ := hP
    exact hi (Ideal.mem_bot.mp (h ▸ hmem i))
  obtain ⟨G, hG, ⟨a₀, ha₀, haG⟩, hdiv⟩ := exists_generic_generator I hI
  choose a ha hadiv using (fun i => hdiv (P i) (hmem i))
  let c := a₀ * (∏ i, a i) * G.leadingCoeff
  have hc : c ≠ 0 := mul_ne_zero (mul_ne_zero ha₀ (Finset.prod_ne_zero_iff.mpr (fun i _ => ha i)))
    (leadingCoeff_ne_zero.mpr hG)
  refine ⟨G, c, hc, hG, ?_⟩
  intro F _ φ hφ
  have hparts : φ a₀ * (∏ i, φ (a i)) * φ G.leadingCoeff ≠ 0 := by
    simpa only [c, map_mul, map_prod] using hφ
  have hlead : φ G.leadingCoeff ≠ 0 := (mul_ne_zero_iff.mp hparts).2
  have hφa₀ : φ a₀ ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hparts).1).1
  have hφa (i : ι) : φ (a i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hparts).1).2 i (Finset.mem_univ _)
  refine ⟨natDegree_map_of_leadingCoeff_ne_zero _ hlead, fun z => ?_⟩
  let ev : A[X] →+* F := Polynomial.eval₂RingHom φ z
  constructor
  · intro hz
    have hker : I ≤ RingHom.ker ev := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact hz i
    have hmul : φ a₀ * G.eval₂ φ z = 0 := by
      have h := hker haG
      change ev (C a₀ * G) = 0 at h
      simpa only [ev, Polynomial.coe_eval₂RingHom, eval₂_mul, eval₂_C] using h
    exact (mul_eq_zero.mp hmul).resolve_left hφa₀
  · intro hz i
    obtain ⟨H, hH⟩ := hadiv i
    have hmul : φ (a i) * (P i).eval₂ φ z = 0 := by
      have h := congrArg ev hH
      simpa only [ev, Polynomial.coe_eval₂RingHom, eval₂_mul, eval₂_C, hz, zero_mul] using h
    exact (mul_eq_zero.mp hmul).resolve_left (hφa i)

/-- Explicit finite polynomial identities form a certificate that can be
realized on a common neighborhood when the coefficient ring is a germ ring. -/
theorem exists_generic_certificate {ι : Type*} [Fintype ι] (P : ι → A[X])
    (hP : ∃ i, P i ≠ 0) :
    ∃ (G : A[X]) (a₀ : A) (B : ι → A[X]) (a : ι → A) (H : ι → A[X]),
      G ≠ 0 ∧ a₀ ≠ 0 ∧ (∀ i, a i ≠ 0) ∧
      (∑ i, B i * P i) = C a₀ * G ∧ ∀ i, C (a i) * P i = G * H i := by
  classical
  let I := Ideal.span (Set.range P)
  have hmem (i : ι) : P i ∈ I := Ideal.subset_span (mem_range_self i)
  have hI : I ≠ ⊥ := by
    intro h
    obtain ⟨i, hi⟩ := hP
    exact hi (Ideal.mem_bot.mp (h ▸ hmem i))
  obtain ⟨G, hG, ⟨a₀, ha₀, haG⟩, hdiv⟩ := exists_generic_generator I hI
  obtain ⟨B, hB⟩ := Ideal.mem_span_range_iff_exists_fun.mp haG
  choose a ha H hH using (fun i => hdiv (P i) (hmem i))
  exact ⟨G, a₀, B, a, H, hG, ha₀, ha, hB, hH⟩

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.GenericPolynomialGCD.Constructions.GenericGCD
