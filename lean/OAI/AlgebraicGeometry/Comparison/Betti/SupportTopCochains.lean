import OAI.AlgebraicGeometry.Comparison.Betti.SupportCochainVanishing
import Mathlib.Order.Preorder.Finite

/-! # Support Top Cochains -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SupportTopCochains.Cech

noncomputable section

/-! Full-support cochains below top degree vanish; sorted top cochains have one coefficient. -/

variable {ι V : Type} [Fintype ι] [LinearOrder ι] [AddCommGroup V]

theorem fullSupportCochain_zero_of_lt (q : ℕ) (hq : q + 1 < Fintype.card ι)
    (s : SupportedCochains.Cech.supportedCechCochains V (Finset.univ : Finset ι) q) : s = 0 := by
  apply Subtype.ext
  funext t
  apply s.property t
  intro hN
  have ht : Function.Surjective t := by
    intro i
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp (hN (Finset.mem_univ i))
    exact ⟨k, hk⟩
  have hcard := Fintype.card_le_of_surjective t ht
  exact (Nat.not_le_of_gt hq) (by simpa only [Fintype.card_fin] using hcard)

omit [Fintype ι] [LinearOrder ι] in
theorem fullSupportTop_sorted_tuple (n : ℕ) (t : Fin (n + 1) → Fin (n + 1))
    (ht : Function.Injective t) : t ∘ Tuple.sort t = id :=
  ((Tuple.monotone_sort t).strictMono_of_injective (ht.comp (Tuple.sort t).injective)).eq_id

omit [Fintype ι] [LinearOrder ι] in
theorem fullSupportTopSorting_apply (n : ℕ)
    (s : SupportedCochains.Cech.supportedCechCochains V (Finset.univ : Finset (Fin (n + 1))) n)
    (t : Fin (n + 1) → Fin (n + 1)) :
    (SupportedCochainSorting.Cech.supportedCechSorting Finset.univ n s).val t =
      if Function.Injective t then (Equiv.Perm.sign (Tuple.sort t) : ℤ) • s.val id else 0 := by
  change TupleCochainBoundary.Cech.tupleCochainPairing n s.val (SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleAlternatingProjection n (Finsupp.single t 1)) = _
  rw [SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleAlternatingProjection_single, one_smul]
  by_cases ht : Function.Injective t
  · rw [ite_eq_left ht, SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleAlternatingProjectionBasis_of_injective t ht,
      TupleCochainBoundary.Cech.tupleCochainPairing_single, fullSupportTop_sorted_tuple n t ht]
  · rw [ite_eq_right ht, SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleAlternatingProjectionBasis_of_not_injective t ht, map_zero]

omit [Fintype ι] [LinearOrder ι] in
theorem fullSupportTopSorting_ext (n : ℕ)
    (s t : SupportedCochains.Cech.supportedCechCochains V (Finset.univ : Finset (Fin (n + 1))) n)
    (h : s.val id = t.val id) :
    SupportedCochainSorting.Cech.supportedCechSorting Finset.univ n s = SupportedCochainSorting.Cech.supportedCechSorting Finset.univ n t := by
  apply Subtype.ext
  funext a
  rw [fullSupportTopSorting_apply, fullSupportTopSorting_apply, h]

omit [Fintype ι] [LinearOrder ι] in
theorem fullSupportTopSorting_id (n : ℕ)
    (s : SupportedCochains.Cech.supportedCechCochains V (Finset.univ : Finset (Fin (n + 1))) n) :
    (SupportedCochainSorting.Cech.supportedCechSorting Finset.univ n s).val id = s.val id := by
  change TupleCochainBoundary.Cech.tupleCochainPairing n s.val (SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleAlternatingProjection n (Finsupp.single id 1)) = _
  rw [SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleAlternatingProjection_single, one_smul,
    SheafCohomology.Projective.CechTupleAlternatingHomotopy.cechTupleAlternatingProjectionBasis_of_strictMono id strictMono_id,
    TupleCochainBoundary.Cech.tupleCochainPairing_single, one_smul]

end

end OAI.AlgebraicGeometry.Comparison.Betti.SupportTopCochains.Cech
