import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.Localization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.SequenceBasic

/-! # Sequence Flat Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.SequenceFlatBaseChange

noncomputable section

open _root_.Module
universe u v w x
variable {R : Type u} {S : Type v} {M : Type w} {N : Type x}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

theorem weaklyRegular_flat_baseChange [Flat R S] {f : M →ₗ[R] N} (hf : IsBaseChange S f)
    {rs : List R} (reg : SequenceBasic.RingTheory.Sequence.IsWeaklyRegular M rs) : SequenceBasic.RingTheory.Sequence.IsWeaklyRegular N (rs.map (algebraMap R S)) := by
  induction rs generalizing M N with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons, SequenceBasic.RingTheory.Sequence.isWeaklyRegular_cons_iff] at reg ⊢
    let e := (QuotSMulTop.algebraMapTensorEquivTensorQuotSMulTop r M S).symm ≪≫ₗ
      QuotSMulTop.congr ((algebraMap R S) r) hf.equiv
    have he : IsBaseChange S
        (e.toLinearMap.restrictScalars R ∘ₗ TensorProduct.mk R S (QuotSMulTop r M) 1) :=
      IsBaseChange.of_equiv e (fun _ => by simp)
    exact ⟨reg.1.of_flat_of_isBaseChange hf, ih he reg.2⟩

theorem weaklyRegular_flat_algebra [Flat R S] {rs : List R} (reg : SequenceBasic.RingTheory.Sequence.IsWeaklyRegular R rs) :
    SequenceBasic.RingTheory.Sequence.IsWeaklyRegular S (rs.map (algebraMap R S)) :=
  weaklyRegular_flat_baseChange (IsBaseChange.linearMap R S) reg

theorem weaklyRegular_regular_localization
    (S : Type v) [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]
    [IsLocalization.AtPrime S p] {rs : List R}
    (reg : SequenceBasic.RingTheory.Sequence.IsWeaklyRegular R rs) (mem : ∀ r ∈ rs, r ∈ p) :
    SequenceBasic.RingTheory.Sequence.IsRegular S (rs.map (algebraMap R S)) := by
  have : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S p
  have : Nontrivial S := IsLocalization.AtPrime.nontrivial S p
  have : Flat R S := IsLocalization.flat S p.primeCompl
  apply (SequenceBasic.IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal (fun r hr => ?_)).mpr
  · exact weaklyRegular_flat_algebra reg
  · obtain ⟨r, hrmem, rfl⟩ := List.mem_map.mp hr
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff S p r).mpr (mem r hrmem)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.SequenceFlatBaseChange
