import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.AuxiliaryIdeal
import Mathlib.Data.Finset.Card

/-! # Count Reduction -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CountReduction.Construction

noncomputable section

/-! The finite old-boundary count and the auxiliary ideals detecting its strata. -/

variable {R σ : Type*} [CommRing R]

/-- The ideal of a selected intersection of boundary equations. -/
def boundaryIntersectionIdeal (w : σ → R) (B : Finset σ) : Ideal R :=
  Ideal.span (Set.range (fun i : B => w i.val))

/-- The selected boundary components passing through a point. -/
def activeBoundaryComponents (w : σ → R) (B : Finset σ) (q : Ideal R) : Finset σ := by
  classical
  exact B.filter (fun i => w i ∈ q)

theorem boundaryIntersectionIdeal_le_iff (w : σ → R) (B : Finset σ) (q : Ideal R) :
    boundaryIntersectionIdeal w B ≤ q ↔ ∀ i ∈ B, w i ∈ q := by
  constructor
  · intro h i hi
    exact h (Ideal.subset_span ⟨⟨i, hi⟩, rfl⟩)
  · intro h
    apply Ideal.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact h i.val i.property

theorem boundaryIntersectionIdeal_le_iff_subset_active
    (w : σ → R) (A B : Finset σ) (hAB : A ⊆ B) (q : Ideal R) :
    boundaryIntersectionIdeal w A ≤ q ↔ A ⊆ activeBoundaryComponents w B q := by
  classical
  rw [boundaryIntersectionIdeal_le_iff]
  exact ⟨fun h i hi => Finset.mem_filter.mpr ⟨hAB hi, h i hi⟩,
    fun h i hi => (Finset.mem_filter.mp (h hi)).2⟩

/-- This prime-power test for a boundary ideal needs no smoothness hypothesis. -/
theorem ideal_pow_le_prime_pow_iff (L q : Ideal R) [q.IsPrime] (m : ℕ) (hm : 0 < m) :
    L ^ m ≤ q ^ m ↔ L ≤ q := by
  constructor
  · intro h
    exact Ideal.IsPrime.le_of_pow_le (h.trans (Ideal.pow_le_self (Nat.ne_of_gt hm)))
  · intro h
    exact pow_le_pow_left' h m

theorem boundaryAuxiliaryIdeal_prime_order_iff
    (J L q : Ideal R) [q.IsPrime] (m : ℕ) (hm : 0 < m) :
    AuxiliaryIdeal.Construction.boundaryAuxiliaryIdeal J L m ≤ q ^ m ↔ J ≤ q ^ m ∧ L ≤ q := by
  rw [AuxiliaryIdeal.Construction.boundaryAuxiliaryIdeal, sup_le_iff, ideal_pow_le_prime_pow_iff L q m hm]

/-- An intersection of at least `s` old components is detected by one of
the finitely many selected intersections of exactly `s` components. -/
theorem boundary_count_ge_iff (w : σ → R) (B : Finset σ) (q : Ideal R) (s : ℕ) :
    s ≤ (activeBoundaryComponents w B q).card ↔
      ∃ A ⊆ B, A.card = s ∧ boundaryIntersectionIdeal w A ≤ q := by
  classical
  constructor
  · intro h
    obtain ⟨A, hA, hcard⟩ := Finset.exists_subset_card_eq h
    have hAB : A ⊆ B := hA.trans (Finset.filter_subset _ _)
    exact ⟨A, hAB, hcard,
      (boundaryIntersectionIdeal_le_iff_subset_active w A B hAB q).mpr hA⟩
  · rintro ⟨A, hAB, hcard, hA⟩
    rw [← hcard]
    exact Finset.card_le_card
      ((boundaryIntersectionIdeal_le_iff_subset_active w A B hAB q).mp hA)

/-- The maximal boundary-count locus of a marked ideal is covered by its
actual boundary auxiliary ideals. -/
theorem boundary_count_auxiliary_cover
    (w : σ → R) (B : Finset σ) (J q : Ideal R) [q.IsPrime]
    (m s : ℕ) (hm : 0 < m) :
    (J ≤ q ^ m ∧ s ≤ (activeBoundaryComponents w B q).card) ↔
      ∃ A ⊆ B, A.card = s ∧
        AuxiliaryIdeal.Construction.boundaryAuxiliaryIdeal J (boundaryIntersectionIdeal w A) m ≤ q ^ m := by
  rw [boundary_count_ge_iff]
  constructor
  · rintro ⟨hJ, A, hAB, hcard, hA⟩
    exact ⟨A, hAB, hcard,
      (boundaryAuxiliaryIdeal_prime_order_iff J _ q m hm).mpr ⟨hJ, hA⟩⟩
  · rintro ⟨A, hAB, hcard, hH⟩
    obtain ⟨hJ, hA⟩ := (boundaryAuxiliaryIdeal_prime_order_iff J _ q m hm).mp hH
    exact ⟨hJ, A, hAB, hcard, hA⟩

/-- At a point where the old-boundary count is at most `s`, an auxiliary
problem indexed by `s` components determines all active old components. -/
theorem maximal_boundary_intersection_eq_active
    (w : σ → R) (A B : Finset σ) (hAB : A ⊆ B) (q : Ideal R) (s : ℕ)
    (hcard : A.card = s) (hbound : (activeBoundaryComponents w B q).card ≤ s)
    (hA : boundaryIntersectionIdeal w A ≤ q) : A = activeBoundaryComponents w B q := by
  apply Finset.eq_of_subset_of_card_le
    ((boundaryIntersectionIdeal_le_iff_subset_active w A B hAB q).mp hA)
  simpa only [hcard] using hbound

/-- Distinct maximal auxiliary intersections have disjoint high-order loci
where the old-boundary count is bounded by their cardinality. -/
theorem maximal_boundary_auxiliary_loci_disjoint
    (w : σ → R) (A D B : Finset σ) (hAB : A ⊆ B) (hDB : D ⊆ B)
    (J q : Ideal R) [q.IsPrime] (m s : ℕ) (hm : 0 < m)
    (hAcard : A.card = s) (hDcard : D.card = s)
    (hbound : (activeBoundaryComponents w B q).card ≤ s) (hAD : A ≠ D)
    (hA : AuxiliaryIdeal.Construction.boundaryAuxiliaryIdeal J (boundaryIntersectionIdeal w A) m ≤ q ^ m) :
    ¬ AuxiliaryIdeal.Construction.boundaryAuxiliaryIdeal J (boundaryIntersectionIdeal w D) m ≤ q ^ m := by
  intro hD
  have hAa := maximal_boundary_intersection_eq_active w A B hAB q s hAcard hbound
    ((boundaryAuxiliaryIdeal_prime_order_iff J _ q m hm).mp hA).2
  have hDa := maximal_boundary_intersection_eq_active w D B hDB q s hDcard hbound
    ((boundaryAuxiliaryIdeal_prime_order_iff J _ q m hm).mp hD).2
  exact hAD (hAa.trans hDa.symm)

/-- Clearing every auxiliary intersection of size `s` strictly lowers the
old-boundary count on the remaining high-order locus of the main ideal. -/
theorem boundary_count_drop_of_auxiliary_clearance
    (w : σ → R) (B : Finset σ) (J q : Ideal R) [q.IsPrime]
    (m s : ℕ) (hm : 0 < m) (hJ : J ≤ q ^ m)
    (hclear : ∀ A ⊆ B, A.card = s →
      ¬ AuxiliaryIdeal.Construction.boundaryAuxiliaryIdeal J (boundaryIntersectionIdeal w A) m ≤ q ^ m) :
    (activeBoundaryComponents w B q).card < s := by
  apply Nat.lt_of_not_ge
  intro hcount
  obtain ⟨A, hAB, hcard, hA⟩ :=
    (boundary_count_auxiliary_cover w B J q m s hm).mp ⟨hJ, hcount⟩
  exact hclear A hAB hcard hA

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CountReduction.Construction
