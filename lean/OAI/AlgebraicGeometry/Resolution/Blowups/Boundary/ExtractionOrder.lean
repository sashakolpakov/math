import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.FactorExtraction
import OAI.AlgebraicGeometry.Resolution.Blowups.LocalContainmentNeighborhood

/-! # Extraction Order -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.ExtractionOrder.Construction

noncomputable section

section

/-! Boundary factors extracted at a point give actual factorizations on affine neighborhoods. -/

variable {R ι : Type*} [CommRing R] [IsNoetherianRing R] [DecidableEq ι]

/-- Extract a finite boundary monomial at a prime and spread the resulting
factorization to an actual principal affine open through that prime. The
residual ideal is nonzero at the point and has no remaining boundary factor
there. All boundary equations and exponents come from the original affine ring. -/
theorem exists_boundary_factor_neighborhood (s : Finset ι) (z : ι → R)
    (J q : Ideal R) [q.IsPrime] (hz : ∀ i ∈ s, z i ∈ q)
    (hJ : J.map (algebraMap R (Localization.AtPrime q)) ≠ ⊥) :
    ∃ (a : ι → ℕ) (L : Ideal R) (f : R), f ∉ q ∧
      (∀ i ∉ s, a i = 0) ∧ J ≤ L ∧
      L.map (algebraMap R (Localization.AtPrime q)) ≠ ⊥ ∧
      (∀ i ∈ s, ¬ L.map (algebraMap R (Localization.AtPrime q)) ≤
        Ideal.span {algebraMap R (Localization.AtPrime q) (z i)}) ∧
      J.map (algebraMap R (Localization.AtPrime q)) =
        Ideal.span {algebraMap R (Localization.AtPrime q) (∏ i ∈ s, z i ^ a i)} *
          L.map (algebraMap R (Localization.AtPrime q)) ∧
      J.map (algebraMap R (Localization.Away f)) =
        Ideal.span {algebraMap R (Localization.Away f) (∏ i ∈ s, z i ^ a i)} *
          L.map (algebraMap R (Localization.Away f)) := by
  let T := Localization.AtPrime q
  let α := algebraMap R T
  have hzproper : ∀ i ∈ s, Ideal.span {α (z i)} ≠ ⊤ := by
    intro i hi
    have himem : α (z i) ∈ IsLocalRing.maximalIdeal T := by
      change z i ∈ (IsLocalRing.maximalIdeal T).under R
      rw [IsLocalization.AtPrime.under_maximalIdeal T q]
      exact hz i hi
    have hle := (Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal T)).mpr himem
    intro ht
    rw [ht] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal T).ne_top (top_le_iff.mp hle)
  obtain ⟨a, U, ha, hfactor, hJU, hU, hUbound⟩ :=
    FactorExtraction.Construction.exists_finite_boundary_factorization s (fun i => α (z i)) hzproper (J.map α) hJ
  let L := U.under R
  have hLmap : L.map α = U := IsLocalization.map_under q.primeCompl T U
  let c := ∏ i ∈ s, z i ^ a i
  have heq : J.map α = (Ideal.span {c} * L).map α := by
    rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton, hLmap]
    simpa only [c, map_prod, map_pow] using hfactor
  obtain ⟨f, hf, hfeq⟩ := LocalContainmentNeighborhood.Construction.exists_neighborhood_ideal_equality J (Ideal.span {c} * L) q
    (IsNoetherian.noetherian _) (IsNoetherian.noetherian _) heq
  refine ⟨a, L, f, hf, ha, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact hJU (Ideal.mem_map_of_mem α hx)
  · rwa [hLmap]
  · intro i hi
    rw [hLmap]
    exact hUbound i hi
  · rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton] at heq
    exact heq
  · rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton] at hfeq
    exact hfeq

end

/-! Removing positive boundary powers strictly lowers residual order at points on those boundaries. -/

variable {R ι : Type*} [CommRing R]

/-- The boundary monomial has at least the sum of its exponents as order
at every point lying on all of the chosen boundary equations. -/
theorem finite_boundary_product_mem_power (s : Finset ι) (z : ι → R) (a : ι → ℕ)
    (q : Ideal R) (hz : ∀ i ∈ s, z i ∈ q) :
    (∏ i ∈ s, z i ^ a i) ∈ q ^ (∑ i ∈ s, a i) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Ideal.prod_mem_prod
  intro i hi
  exact Ideal.pow_mem_pow (hz i hi) (a i)

/-- Removing any positive total boundary power gives strict residual-order
decrease relative to a bound on the original ideal. -/
theorem boundary_factor_removal_lowers_order (s : Finset ι) (z : ι → R) (a : ι → ℕ)
    (J L q : Ideal R) (hz : ∀ i ∈ s, z i ∈ q)
    (hfactor : J = Ideal.span {∏ i ∈ s, z i ^ a i} * L)
    (hpos : 0 < ∑ i ∈ s, a i) (m : ℕ) (hbound : ¬ J ≤ q ^ (m + 1)) :
    ¬ L ≤ q ^ m := by
  intro hL
  apply hbound
  have hM : Ideal.span {∏ i ∈ s, z i ^ a i} ≤ q ^ (∑ i ∈ s, a i) :=
    (Ideal.span_singleton_le_iff_mem _).mpr (finite_boundary_product_mem_power s z a q hz)
  rw [hfactor]
  have hprod := Ideal.mul_mono hM hL
  rw [← pow_add] at hprod
  exact hprod.trans (Ideal.pow_le_pow_right (by omega))

/-- Even when all boundary exponents vanish, removing a boundary factor
cannot increase order, since the residual ideal contains the original ideal. -/
theorem boundary_factor_removal_preserves_order_bound (J L : Ideal R) (c : R)
    (hfactor : J = Ideal.span {c} * L) (q : Ideal R) (m : ℕ)
    (hbound : ¬ J ≤ q ^ (m + 1)) : ¬ L ≤ q ^ (m + 1) := by
  intro hL
  apply hbound
  rw [hfactor]
  exact Ideal.mul_le_right.trans hL

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.ExtractionOrder.Construction
