import OAI.AlgebraicGeometry.Comparison.Betti.SupportedCochainSorting
import OAI.AlgebraicGeometry.Comparison.Betti.SupportedCochainContraction

/-! # Support Cochain Vanishing -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SupportCochainVanishing.Cech

noncomputable section

/-! Full-support cochain cohomology vanishes away from the top finite-cover degree. -/

variable {ι V : Type} [Fintype ι] [LinearOrder ι] [AddCommGroup V]

theorem fullSupportSorting_zero (q : ℕ) (hq : q + 1 ≠ Fintype.card ι)
    (s : SupportedCochains.Cech.supportedCechCochains V (Finset.univ : Finset ι) q) :
    SupportedCochainSorting.Cech.supportedCechSorting Finset.univ q s = 0 := by
  apply Subtype.ext
  funext t
  change TupleCochainBoundary.Cech.tupleCochainPairing q s.val (SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleAlternatingProjection q (Finsupp.single t 1)) = 0
  by_cases ht : Function.Injective t
  · have hN : ¬(Finset.univ : Finset ι) ⊆ Finset.univ.image t := by
      intro hN
      have hsurj : Function.Surjective t := by
        intro i
        obtain ⟨k, _, hk⟩ := Finset.mem_image.mp (hN (Finset.mem_univ i))
        exact ⟨k, hk⟩
      apply hq
      simpa only [Fintype.card_fin] using Fintype.card_congr (Equiv.ofBijective t ⟨ht, hsurj⟩)
    exact TupleCochainBoundary.Cech.tupleCochainPairing_supported_zero Finset.univ q s t _
      (SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleAlternatingProjection_supportedBy q (Finsupp.single t 1) (Set.range t)
        (SheafCohomology.Projective.CechTupleAlternatingHomotopy.CechTupleChain.supportedBy_single t 1 Set.Subset.rfl)) hN
  · rw [SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleAlternatingProjection_single, one_smul,
      SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleAlternatingProjectionBasis_of_not_injective t ht, map_zero]

theorem fullSupportCycle_has_primitive (q : ℕ) (hq : q + 2 ≠ Fintype.card ι)
    (s : SupportedCochains.Cech.supportedCechCochains V (Finset.univ : Finset ι) (q + 1))
    (hs : SupportedCochains.Cech.supportedCechDifferential Finset.univ (q + 1) s = 0) :
    ∃ t : SupportedCochains.Cech.supportedCechCochains V (Finset.univ : Finset ι) q,
      SupportedCochains.Cech.supportedCechDifferential Finset.univ q t = s := by
  refine ⟨-SupportedCochainSorting.Cech.supportedCechSortingHomotopy Finset.univ q s, ?_⟩
  rw [map_neg, SupportedCochainSorting.Cech.supportedCechSorting_cycle Finset.univ q s hs,
    fullSupportSorting_zero (q + 1) hq s, zero_sub, neg_neg]

theorem supportedCechCycle_has_primitive_of_card_ne (N : Finset ι) (q : ℕ)
    (hq : q + 2 ≠ Fintype.card ι) (s : SupportedCochains.Cech.supportedCechCochains V N (q + 1))
    (hs : SupportedCochains.Cech.supportedCechDifferential N (q + 1) s = 0) :
    ∃ t : SupportedCochains.Cech.supportedCechCochains V N q, SupportedCochains.Cech.supportedCechDifferential N q t = s := by
  by_cases hN : N = Finset.univ
  · subst N
    exact fullSupportCycle_has_primitive q hq s hs
  · have hex : ∃ i, i ∉ N := by
      by_contra h
      apply hN
      apply Finset.ext
      intro i
      constructor
      · intro _
        exact Finset.mem_univ i
      · intro _
        by_contra hi
        exact h ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hex
    exact SupportedCochainContraction.Cech.supportedCechCycle_has_primitive N i hi q s hs

end

end OAI.AlgebraicGeometry.Comparison.Betti.SupportCochainVanishing.Cech
