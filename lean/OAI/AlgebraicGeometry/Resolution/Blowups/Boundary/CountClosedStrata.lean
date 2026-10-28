import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CountReduction
import OAI.AlgebraicGeometry.Resolution.Blowups.ClosedWeightedOrder
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.ClosedOrder
import Mathlib.Data.Nat.Find
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Count Closed Strata -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CountClosedStrata.Construction

noncomputable section

/-! Attained old-boundary maxima and disjoint closed strata on an affine scheme. -/

section

variable {R σ : Type*} [CommRing R]

theorem activeBoundaryComponents_mono (w : σ → R) (B : Finset σ) {q r : Ideal R}
    (hqr : q ≤ r) : CountReduction.Construction.activeBoundaryComponents w B q ⊆ CountReduction.Construction.activeBoundaryComponents w B r := by
  classical
  intro i hi
  obtain ⟨hiB, hiq⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hiB, hqr hiq⟩

/-- On a nonempty affine closed locus, the old-boundary count attains a
finite maximum at a closed point. The same bound holds at every prime point. -/
theorem exists_closed_boundary_count_maximum
    (w : σ → R) (B : Finset σ) (F : Ideal R) (hF : F ≠ ⊤) :
    ∃ s ≤ B.card, ∃ q : Ideal R, q.IsMaximal ∧ F ≤ q ∧
      (CountReduction.Construction.activeBoundaryComponents w B q).card = s ∧
      ∀ r : Ideal R, r ≠ ⊤ → F ≤ r → (CountReduction.Construction.activeBoundaryComponents w B r).card ≤ s := by
  classical
  let P : ℕ → Prop := fun n => ∃ q : Ideal R, q.IsMaximal ∧ F ≤ q ∧
    (CountReduction.Construction.activeBoundaryComponents w B q).card = n
  obtain ⟨q, hq, hFq⟩ := Ideal.exists_le_maximal F hF
  let n := (CountReduction.Construction.activeBoundaryComponents w B q).card
  have hn : n ≤ B.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hP : P n := ⟨q, hq, hFq, rfl⟩
  let s := Nat.findGreatest P B.card
  obtain ⟨q', hq', hFq', hcard⟩ := Nat.findGreatest_spec hn hP
  refine ⟨s, Nat.findGreatest_le _, q', hq', hFq', hcard, ?_⟩
  intro r hr hFr
  obtain ⟨M, hM, hrM⟩ := Ideal.exists_le_maximal r hr
  apply (Finset.card_le_card (activeBoundaryComponents_mono w B hrM)).trans
  apply Nat.le_findGreatest (Finset.card_le_card (Finset.filter_subset _ _))
  exact ⟨M, hM, hFr.trans hrM, rfl⟩

/-- The closed locus where `F` vanishes on a selected boundary intersection. -/
def boundaryStratumIdeal (w : σ → R) (F : Ideal R) (A : Finset σ) : Ideal R :=
  F ⊔ CountReduction.Construction.boundaryIntersectionIdeal w A

/-- Distinct intersections of maximal cardinality cut out disjoint closed
subschemes of the locus defined by `F`. It suffices to bound closed points. -/
theorem maximal_boundary_stratum_ideals_comaximal
    (w : σ → R) (B A D : Finset σ) (F : Ideal R) (s : ℕ)
    (hbound : ∀ q : Ideal R, q.IsMaximal → F ≤ q →
      (CountReduction.Construction.activeBoundaryComponents w B q).card ≤ s)
    (hAB : A ⊆ B) (hDB : D ⊆ B) (hAcard : A.card = s) (hDcard : D.card = s)
    (hAD : A ≠ D) : boundaryStratumIdeal w F A ⊔ boundaryStratumIdeal w F D = ⊤ := by
  by_contra hproper
  obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal _ hproper
  have hA : boundaryStratumIdeal w F A ≤ q := le_sup_left.trans hle
  have hD : boundaryStratumIdeal w F D ≤ q := le_sup_right.trans hle
  have hFq : F ≤ q := le_sup_left.trans hA
  have hcount := hbound q hq hFq
  have hAa := CountReduction.Construction.maximal_boundary_intersection_eq_active w A B hAB q s hAcard hcount
    (le_sup_right.trans hA)
  have hDa := CountReduction.Construction.maximal_boundary_intersection_eq_active w D B hDB q s hDcard hcount
    (le_sup_right.trans hD)
  exact hAD (hAa.trans hDa.symm)

/-- The maximal boundary strata are disjoint as actual closed subsets of
the prime spectrum, including their non-closed points. -/
theorem maximal_boundary_strata_disjoint
    (w : σ → R) (B A D : Finset σ) (F : Ideal R) (s : ℕ)
    (hbound : ∀ q : Ideal R, q.IsMaximal → F ≤ q →
      (CountReduction.Construction.activeBoundaryComponents w B q).card ≤ s)
    (hAB : A ⊆ B) (hDB : D ⊆ B) (hAcard : A.card = s) (hDcard : D.card = s)
    (hAD : A ≠ D) :
    Disjoint (PrimeSpectrum.zeroLocus (boundaryStratumIdeal w F A : Set R))
      (PrimeSpectrum.zeroLocus (boundaryStratumIdeal w F D : Set R)) := by
  apply Set.disjoint_iff_inter_eq_empty.mpr
  rw [← PrimeSpectrum.zeroLocus_sup]
  exact PrimeSpectrum.zeroLocus_empty_iff_eq_top.mpr
    (maximal_boundary_stratum_ideals_comaximal w B A D F s hbound hAB hDB hAcard hDcard hAD)

end

variable {σ K S : Type*} [Field K] [IsAlgClosed K] [CharZero K] [CommRing S] [Finite σ]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]

include σ K in
/-- For the actual differential ideal defining the high-order locus,
the closed boundary strata are precisely the auxiliary marked problems
at every closed point. -/
theorem etale_boundary_stratum_order_iff
    (w : σ → S) (A : Finset σ) (J q : Ideal S) [q.IsMaximal] (m : ℕ) :
    boundaryStratumIdeal w (DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J m) A ≤ q ↔
      AuxiliaryIdeal.Construction.boundaryAuxiliaryIdeal J (CountReduction.Construction.boundaryIntersectionIdeal w A) (m + 1) ≤ q ^ (m + 1) := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  have horder : J ≤ q ^ (m + 1) ↔ DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J m ≤ q :=
    (ClosedWeightedOrder.Construction.closedPoint_local_order_iff J q (m + 1)).symm.trans
      (Blowups.Etale.ClosedOrder.Construction.etale_closedPoint_order_iff_differentialIdeal (σ := σ) (K := K) J q m)
  rw [boundaryStratumIdeal, sup_le_iff,
    CountReduction.Construction.boundaryAuxiliaryIdeal_prime_order_iff J _ q (m + 1) (Nat.zero_lt_succ m), horder]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CountClosedStrata.Construction
