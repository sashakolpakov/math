import Mathlib.RingTheory.Unramified.LocalRing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.SequenceFlatBaseChange

/-! # Etale Local Regular Sequences -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EtaleLocalRegularSequences

noncomputable section

/-! A flat, essentially finite-type, formally unramified local map carries a regular sequence generating the source maximal ideal to a regular sequence generating the target maximal ideal. -/
open IsLocalRing
universe u v

theorem local_unramified_flat_regular_generators
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B]
    [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B]
    [Algebra.FormallyUnramified A B] [Module.Flat A B]
    (rs : List A) (hregular : Regular.SequenceBasic.RingTheory.Sequence.IsRegular A rs)
    (hgenerate : Regular.SequenceBasic.Ideal.ofList rs = maximalIdeal A) :
    Regular.SequenceBasic.RingTheory.Sequence.IsRegular B (rs.map (algebraMap A B)) ∧
      Regular.SequenceBasic.Ideal.ofList (rs.map (algebraMap A B)) = maximalIdeal B := by
  have hmap : Regular.SequenceBasic.Ideal.ofList (rs.map (algebraMap A B)) = maximalIdeal B := by
    rw [← Regular.SequenceBasic.Ideal.map_ofList, hgenerate, Algebra.FormallyUnramified.map_maximalIdeal]
  have hweak : Regular.SequenceBasic.RingTheory.Sequence.IsWeaklyRegular B (rs.map (algebraMap A B)) := Regular.SequenceFlatBaseChange.weaklyRegular_flat_algebra hregular.1
  have hmem : ∀ r ∈ rs.map (algebraMap A B), r ∈ maximalIdeal B := by
    intro r hr
    rw [← hmap]
    exact Ideal.subset_span hr
  exact ⟨(Regular.SequenceBasic.IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem).mpr hweak, hmap⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EtaleLocalRegularSequences
